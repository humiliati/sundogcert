"""GPU-ready white-box HARVEST for the H-I cliff generality run (H7 residual).

Runs the v2 authority-vs-volume task on LOCAL open-weight models and persists, per
model: decision-time hidden vectors at depth-scaled layers + same-model first-token
entropy + O + lambda. Analysis (probe AUC, cross-stack alignment) is done OFFLINE by
whitebox_analyze.py, so the expensive GPU box is a pure harvest sprint.

Device-agnostic: CUDA + bf16 when available (the rented box), else CPU + fp32 (local
dry-run) -- identical code path. The SAME corpus seed sequence is used for every model,
so trials are PAIRED across models (enables CCA/Procrustes cross-stack transfer).

  # local plumbing smoke (CPU, tiny):
  python scripts/whitebox_harvest.py --models Qwen/Qwen2.5-0.5B-Instruct --grid smoke --n-trials 5
  # rented 8xH200 sprint (harvest the ladder, then tear down; analyze offline):
  python scripts/whitebox_harvest.py --ladder --grid full --n-trials 30 --out-dir ../results/whitebox_ladder
"""
from __future__ import annotations
import argparse, gc, json, os, time
import numpy as np
import torch
from transformers import AutoTokenizer, AutoModelForCausalLM
import cliff_transfer_task_v2 as t2

LADDER = [
    "Qwen/Qwen2.5-0.5B-Instruct", "Qwen/Qwen2.5-1.5B-Instruct", "Qwen/Qwen2.5-3B-Instruct",
    "Qwen/Qwen2.5-7B-Instruct", "Qwen/Qwen2.5-14B-Instruct", "Qwen/Qwen2.5-32B-Instruct",
    "meta-llama/Llama-3.1-8B-Instruct", "meta-llama/Llama-3.3-70B-Instruct",
]
GRIDS = {
    "smoke": (0.0, 0.5, 0.75, 1.0),
    "full": (0.0, 0.375, 0.5, 0.5625, 0.625, 0.6875, 0.75, 0.875, 1.0),
}


def maybe_set_hf_token():
    """Silently export HF_TOKEN from the reversed-filename keyring to dodge rate limits."""
    if os.environ.get("HF_TOKEN"):
        return
    p = os.path.join(os.path.expanduser("~"), "Dev", "syek.ecafgnigguh.txt")
    if os.path.exists(p):
        tok = [l.strip() for l in open(p, encoding="utf-8") if l.strip() and not l.startswith("#")]
        if tok:
            os.environ["HF_TOKEN"] = max(tok, key=len)


def pick_device():
    if torch.cuda.is_available():
        # bf16 is native only on Ampere+ (cc>=8; H200=9.0). Pascal (GTX 1080=6.1)
        # only emulates it -> use fp16 there. CPU stays fp32.
        cc = torch.cuda.get_device_capability(0)
        return "cuda", (torch.bfloat16 if cc[0] >= 8 else torch.float16)
    return "cpu", torch.float32


def load(name, dev, dt):
    tok = AutoTokenizer.from_pretrained(name)
    kw = {"dtype": dt}
    if dev == "cuda":
        try:
            import accelerate  # noqa: F401  (enables device_map sharding on the multi-GPU box)
            model = AutoModelForCausalLM.from_pretrained(name, device_map="auto", **kw)
        except ImportError:
            # single-GPU, no accelerate (local dry-run): plain load + move to cuda.
            model = AutoModelForCausalLM.from_pretrained(name, **kw).to("cuda")
    else:
        model = AutoModelForCausalLM.from_pretrained(name, **kw)
    model.eval()
    return tok, model


def layers_for(model):
    n = model.config.num_hidden_layers
    return sorted({max(1, round(f * n)) for f in (0.2, 0.4, 0.6, 0.8, 0.95)})


@torch.no_grad()
def decision(model, tok, prompt, layers, max_new_tokens=8):
    text = tok.apply_chat_template([{"role": "user", "content": prompt}],
                                   tokenize=False, add_generation_prompt=True)
    ids = tok(text, return_tensors="pt").to(model.device)
    out = model.generate(**ids, max_new_tokens=max_new_tokens, do_sample=False,
                         output_hidden_states=True, output_scores=True,
                         return_dict_in_generate=True, pad_token_id=tok.eos_token_id)
    gen = out.sequences[0, ids["input_ids"].shape[1]:]
    ans = tok.decode(gen, skip_special_tokens=True)
    step0 = out.hidden_states[0]  # tuple len n_layers+1; each [1, prompt_len, hidden]
    hid = {L: step0[L][0, -1, :].float().cpu().numpy() for L in layers}
    logits = out.scores[0][0].float()
    logp = torch.log_softmax(logits, -1)
    ent = float(-(logp.exp() * logp).sum().cpu())  # full-vocab first-token entropy (nats)
    return ans, hid, ent


def harvest_model(name, grid, n_trials, dev, dt):
    tok, model = load(name, dev, dt)
    layers = layers_for(model)
    recs = []
    seed = 0  # identical across models -> paired trials
    malformed = 0
    for lam in grid:
        for _ in range(n_trials):
            prompt, truth, trap = t2.build_corpus(lam, seed); seed += 1
            ans, hid, ent = decision(model, tok, prompt, layers)
            scan = ans.split("</think>")[-1] if "</think>" in ans else ans
            o, _ = t2.score_o(scan, truth, trap)
            if o is None:
                malformed += 1
            recs.append((lam, o, ent, hid))
    hidden_dim = int(model.config.hidden_size)
    del model
    gc.collect()
    if dev == "cuda":
        torch.cuda.empty_cache()
    return layers, hidden_dim, recs, malformed


def save_model(out_dir, name, layers, hidden_dim, recs):
    safe = name.replace("/", "__")
    lam = np.array([r[0] for r in recs], dtype=np.float32)
    O = np.array([-1 if r[1] is None else int(r[1]) for r in recs], dtype=np.int64)
    ent = np.array([r[2] for r in recs], dtype=np.float32)
    arrs = {f"hid_L{L}": np.stack([r[3][L] for r in recs]).astype(np.float32) for L in layers}
    np.savez(os.path.join(out_dir, safe + ".npz"),
             lam=lam, O=O, entropy=ent, layers=np.array(layers, dtype=np.int64),
             hidden_dim=hidden_dim, **arrs)
    return safe + ".npz"


def main():
    ap = argparse.ArgumentParser(description="White-box harvest for H-I cliff generality.")
    ap.add_argument("--models", nargs="+", default=None)
    ap.add_argument("--ladder", action="store_true", help="use the full scale/family ladder")
    ap.add_argument("--grid", choices=list(GRIDS), default="smoke")
    ap.add_argument("--n-trials", type=int, default=5)
    ap.add_argument("--out-dir", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                      "..", "results", "whitebox_ladder"))
    args = ap.parse_args()
    maybe_set_hf_token()
    models = args.models or (LADDER if args.ladder else ["Qwen/Qwen2.5-0.5B-Instruct"])
    grid = GRIDS[args.grid]
    dev, dt = pick_device()
    os.makedirs(args.out_dir, exist_ok=True)
    print(f"[harvest] device={dev} dtype={dt} | {len(models)} models x {len(grid)} lambdas x {args.n_trials} trials")
    manifest = {"device": dev, "grid": grid, "n_trials": args.n_trials, "models": []}
    for name in models:
        t0 = time.time()
        try:
            layers, hidden_dim, recs, malformed = harvest_model(name, grid, args.n_trials, dev, dt)
        except Exception as e:
            print(f"[harvest] {name}: ERROR {type(e).__name__}: {e}")
            manifest["models"].append({"model": name, "error": f"{type(e).__name__}: {e}"})
            continue
        fn = save_model(args.out_dir, name, layers, hidden_dim, recs)
        oby = {}
        for lam, o, _e, _h in recs:
            oby.setdefault(round(lam, 4), []).append(0 if o is None else o)
        ocurve = {l: round(np.mean([v for v in vs if v is not None or True]) if vs else 0, 3) for l, vs in oby.items()}
        wall = time.time() - t0
        print(f"[harvest] {name:42s} layers={layers} dim={hidden_dim} malformed={malformed} "
              f"({wall:.0f}s) -> {fn}")
        manifest["models"].append({"model": name, "file": fn, "layers": layers,
                                   "hidden_dim": hidden_dim, "malformed": malformed,
                                   "wall_s": round(wall, 1)})
    with open(os.path.join(args.out_dir, "harvest_manifest.json"), "w") as f:
        json.dump(manifest, f, indent=2)
    print(f"[harvest] wrote {args.out_dir}/harvest_manifest.json")


if __name__ == "__main__":
    main()
