"""White-box cliff probe: does the HIDDEN STATE predict the volume-override cliff
that the black-box signals (entropy, self-consistency) were blind to?

Same v2 authority-vs-volume task (cliff_transfer_task_v2), but on a LOCAL open-weight
model so we can read its internals. At each trial we take the decision-time hidden
state (last prompt token, a fixed layer) and ask whether a cheap linear probe on it
predicts O (did the model adopt the contradiction). The black-box campaign found the
override leaves NO signal in the output (AUC ~ chance); the white-box question is
whether it leaves one INSIDE — i.e. whether internal access rescues H-I's monitor, or
whether the override is genuinely undetectable (a stronger bound, matching the Lean
`no_word_function_determines_decisive`).

CPU-only (torch+cpu); ~3 s/trial on Qwen2.5-0.5B. Keep sweeps short (≤ ~8 min) or
stage for the operator's PowerShell.

Run:
  python scripts/cliff_transfer_whitebox.py --probe --model Qwen/Qwen2.5-0.5B-Instruct
"""

from __future__ import annotations

import argparse
import json
import sys
import time

import numpy as np
import torch
from sklearn.decomposition import PCA
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import cross_val_score
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
from transformers import AutoModelForCausalLM, AutoTokenizer

import cliff_transfer_analysis as cta
import cliff_transfer_task_v2 as t2

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

WHITEBOX_VERSION = "H1_CLIFF_TRANSFER_WHITEBOX_V1"
DEFAULT_LAYERS = (4, 8, 12, 16, 20)


def load_model(name):
    tok = AutoTokenizer.from_pretrained(name)
    model = AutoModelForCausalLM.from_pretrained(name, dtype=torch.float32)
    model.eval()
    return tok, model


@torch.no_grad()
def decision(model, tok, prompt, layers, max_new_tokens=8):
    """Greedy-generate; return (answer_text, {layer: decision-time hidden vec},
    first_token_entropy). The hidden state is the last PROMPT token at each layer
    (the representation just before the model commits); the entropy is the
    SAME-MODEL black-box signal, computed free from the first-token logits, so the
    white-box vs black-box contrast is on identical trials."""
    text = tok.apply_chat_template([{"role": "user", "content": prompt}],
                                   tokenize=False, add_generation_prompt=True)
    enc = tok(text, return_tensors="pt")
    out = model.generate(**enc, max_new_tokens=max_new_tokens, do_sample=False,
                         output_hidden_states=True, output_scores=True,
                         return_dict_in_generate=True)
    answer = tok.decode(out.sequences[0][enc["input_ids"].shape[1]:], skip_special_tokens=True)
    step0 = out.hidden_states[0]  # tuple over layers, each [batch, prompt_len, hidden]
    hid = {L: step0[L][0, -1, :].float().numpy() for L in layers}
    logp = torch.log_softmax(out.scores[0][0].float(), dim=-1)
    entropy = float(-(logp.exp() * logp).sum())
    return answer, hid, entropy


def collect(model, tok, lambdas, n_trials, layers, seed0=0):
    rows = []
    seed = seed0
    for lam in lambdas:
        for _ in range(n_trials):
            prompt, truth, trap = t2.build_corpus(lam, seed)
            seed += 1
            ans, hid, ent = decision(model, tok, prompt, layers)
            o, label = t2.score_o(ans, truth, trap)
            rows.append({"lam": lam, "O": o, "label": label, "hid": hid, "entropy": ent})
    return rows


def probe_auc(X, y, n_pca=20, folds=5):
    """Cross-validated linear-probe ROC-AUC: can a cheap linear readout of the
    hidden state predict O? Degenerate (one class / too few) -> nan/0.5."""
    y = np.asarray(y)
    X = np.asarray(X)
    if len(set(y.tolist())) < 2 or X.shape[0] < 8:
        return float("nan")
    folds = int(min(folds, np.bincount(y).min()))
    if folds < 2:
        return float("nan")
    n_pca = int(min(n_pca, X.shape[0] - 1, X.shape[1]))
    pipe = make_pipeline(StandardScaler(), PCA(n_components=n_pca),
                         LogisticRegression(max_iter=2000))
    return float(cross_val_score(pipe, X, y, cv=folds, scoring="roc_auc").mean())


def analyze(rows, layers):
    # cliff fit on O(lambda)
    arows = [{"lambda_fraction": r["lam"], "lambda_hat": r["lam"], "O": int(r["O"] or 0)}
             for r in rows if r["O"] is not None]
    cliff = cta.fit_cliff(arows)
    lam_star = cliff.lambda_star
    # cliff window (the hard regime); fall back to all if degenerate
    win = [r for r in rows if r["O"] is not None
           and abs(r["lam"] - lam_star) <= cta.AUC_WINDOW_HALF_WIDTH]
    if {r["O"] for r in win} != {0, 1}:
        win = [r for r in rows if r["O"] is not None]
    y = [int(r["O"]) for r in win]
    layer_auc = {L: probe_auc([r["hid"][L] for r in win], y) for L in layers}
    # Same-model black-box baseline: first-token entropy predicting O in the window.
    entropy_auc = cta._auc_from_scores([(r["entropy"], int(r["O"])) for r in win])
    o_by = {}
    for r in rows:
        o_by.setdefault(r["lam"], []).append(1 if r["O"] == 1 else 0)
    return {
        "lambda_star": lam_star, "width": cliff.width, "fit_r2": cliff.r2,
        "window_n": len(win), "window_O_rate": (sum(y) / len(y) if y else None),
        "probe_auc_by_layer": layer_auc,
        "best_layer": max(layer_auc, key=lambda L: (layer_auc[L] if layer_auc[L] == layer_auc[L] else -1)),
        "best_probe_auc": max((v for v in layer_auc.values() if v == v), default=float("nan")),
        "entropy_auc_same_model": entropy_auc,
        "malformed": sum(1 for r in rows if r["O"] is None),
        "O_by_lambda": sorted((l, sum(v) / len(v)) for l, v in o_by.items()),
    }


def probe(model_name="Qwen/Qwen2.5-0.5B-Instruct", *,
          lambdas=(0.0, 0.3, 0.5, 0.55, 0.6, 0.65, 0.7, 0.8, 1.0),
          n_trials=10, layers=DEFAULT_LAYERS, out=None):
    t0 = time.time()
    tok, model = load_model(model_name)
    load_s = time.time() - t0
    rows = collect(model, tok, lambdas, n_trials, layers)
    res = analyze(rows, layers)
    res.update({"version": WHITEBOX_VERSION, "model": model_name, "layers": list(layers),
                "n_trials": n_trials, "load_s": load_s, "wall_s": time.time() - t0,
                "n_generations": len(rows)})
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            json.dump(res, fh, indent=2)
    return res


def format_probe(r):
    aucs = "  ".join(f"L{L}:{a:.3f}" for L, a in r["probe_auc_by_layer"].items())
    return "\n".join([
        f"WHITE-BOX CLIFF {r['version']}  model={r['model']}",
        f"  generations={r['n_generations']} malformed={r['malformed']} "
        f"load={r['load_s']:.0f}s wall={r['wall_s']:.0f}s",
        "  O(λ): " + "  ".join(f"{l:.2f}:{o:.2f}" for l, o in r["O_by_lambda"]),
        f"  cliff: λ*={r['lambda_star']:.3f} w={r['width']:.3f} r²={r['fit_r2']:.3f} "
        f"(window_n={r['window_n']} O_rate={r['window_O_rate']})",
        f"  hidden-probe AUC by layer: {aucs}",
        f"  BEST hidden-probe AUC = {r['best_probe_auc']:.3f} (layer {r['best_layer']})  "
        f"vs SAME-MODEL entropy AUC = {r['entropy_auc_same_model']:.3f}",
    ])


def main(argv=None):
    p = argparse.ArgumentParser(description="White-box cliff hidden-state probe.")
    p.add_argument("--probe", action="store_true")
    p.add_argument("--model", default="Qwen/Qwen2.5-0.5B-Instruct")
    p.add_argument("--n-trials", type=int, default=10)
    p.add_argument("--out", default=None)
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    r = probe(args.model, n_trials=args.n_trials, out=args.out)
    print(json.dumps(r, indent=2) if args.json else format_probe(r))
    return r


if __name__ == "__main__":
    main()
