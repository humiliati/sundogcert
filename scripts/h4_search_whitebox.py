"""White-box H-IV probe: on a REAL agent search, does count-by-score collapse onto
redundant high-score branches (pruning the low-score solution) where a structural
line-free admission stays diverse and retains it?

The H-IV chain is closed (falsifier, the structural line-free fix `structural_slot_receipt`,
the Lean core `StructuralSlot`). The one remaining import is the branch->cap-set map from
real agent search. This is the H-IV analog of the H-II retrieval and H-III attention
white-boxes.

Measurement map (see AGENTIC_TRACE_H4_SEARCH_PREREG.md): for each short-answer task, sample
K branches (completions) with their sequence logprob (the agent's score) and a correctness
flag; mean-pool each branch's embedding, PCA the task-local embeddings to 3 dims, tercile
to a point in F_3^3 (the imported coordinate map). Compare, at matched admitted size:
count-by-score (top-m by logprob) vs the structural line-free cap (one branch per distinct
coordinate, admitted line-free). Metrics: solution recall and admitted redundancy.

CPU-only, local 0.5B. Run:
  python scripts/h4_search_whitebox.py --dry-run
  python scripts/h4_search_whitebox.py --real --json out.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys

import numpy as np

from branch_budget_receipt import SearchBranch, budget_search_branches
from structural_slot_receipt import (
    StructuralBranch,
    is_cap,
    is_line,
    make_structural_receipt,
)

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

VERSION = "H4_SEARCH_WHITEBOX_V2"
K = 8
DIM = 3
SEED = 0
MAX_NEW_SHORT = 12
MAX_NEW_REASONING = 96

TASKS = [
    ("Q: What is 7 plus 8? Answer with just the number.\nA:", "15"),
    ("Q: What is 13 minus 6? Answer with just the number.\nA:", "7"),
    ("Q: What is 6 times 4? Answer with just the number.\nA:", "24"),
    ("Q: What is the capital of France? One word.\nA:", "Paris"),
    ("Q: What color do you get mixing blue and yellow? One word.\nA:", "green"),
    ("Q: How many legs does a spider have? Just the number.\nA:", "8"),
]

# Harder tasks where a 0.5B model's top sample is frequently wrong — to test whether the
# collapse regime (a low-score correct branch) actually arises and the structural fix helps.
HARD_TASKS = [
    ("Q: What is 17 times 23? Answer with just the number.\nA:", "391"),
    ("Q: What is 2 to the power 10? Just the number.\nA:", "1024"),
    ("Q: What is the 7th prime number? Just the number.\nA:", "17"),
    ("Q: What is the capital of Australia? One word.\nA:", "Canberra"),
    ("Q: What is 144 divided by 12? Just the number.\nA:", "12"),
    ("Q: What is 9 times 13? Answer with just the number.\nA:", "117"),
]

# Multi-step reasoning tasks (the scale re-run, AGENTIC_TRACE_H4_SEARCH_SCALE_PREREG.md):
# longer branches (reasoning chains) on harder problems, so a larger model SAMPLES the
# correct solution sometimes while mis-ranking it (the collapse regime), and the chains are
# diverse enough that the F_3^3 cap map is not degenerate. Integer answers, matched as a
# standalone number (\b<answer>\b).
_REASON_SUFFIX = " Show your work step by step and end with the final number.\nA:"
REASONING_TASKS = [
    ("Q: Tom has 3 boxes with 12 pencils each and gives away 8 pencils. How many does he have left?" + _REASON_SUFFIX, "28"),
    ("Q: A train travels 60 miles per hour for 3 hours, then 40 miles per hour for 2 hours. How many miles in total?" + _REASON_SUFFIX, "260"),
    ("Q: A baker makes 12 dozen cookies. How many cookies is that in total?" + _REASON_SUFFIX, "144"),
    ("Q: There are 9 crates with 13 oranges in each crate. How many oranges in total?" + _REASON_SUFFIX, "117"),
    ("Q: An auditorium has 17 rows with 23 chairs in each row. How many chairs in total?" + _REASON_SUFFIX, "391"),
    ("Q: A tank holds 200 liters of water and 125 liters are used. How many liters remain?" + _REASON_SUFFIX, "75"),
    ("Q: Sam earns 15 dollars per hour for 8 hours and also gets a 25 dollar bonus. How much does he earn in total?" + _REASON_SUFFIX, "145"),
    ("Q: A book has 320 pages. Maria reads 45 pages per day for 4 days. How many pages are left?" + _REASON_SUFFIX, "140"),
]


def _is_correct(text: str, answer: str, word_boundary: bool = False) -> bool:
    if word_boundary:
        return re.search(r"\b" + re.escape(answer) + r"\b", text) is not None
    return answer.lower() in text.lower()


# ------------------------------------------------------- coordinate map (F_3^n) ----

def quantize_to_f3(embeddings: np.ndarray, dim: int = DIM, mode: str = "embedding") -> list[tuple[int, ...]]:
    """PCA the task-local embeddings to `dim` components and tercile each to {0,1,2}.
    mode="whitened" first centers (subtract the task-mean, removing the dominant anisotropic
    direction that pins same-problem chains together) and per-dimension standardizes."""
    from sklearn.decomposition import PCA
    X = np.asarray(embeddings, dtype=float)
    if mode == "whitened":
        X = X - X.mean(axis=0, keepdims=True)
        X = X / (X.std(axis=0, keepdims=True) + 1e-8)
    k = min(dim, X.shape[0] - 1, X.shape[1])
    comps = PCA(n_components=max(k, 1)).fit_transform(X) if k >= 1 else X[:, :1]
    if comps.shape[1] < dim:                       # pad to `dim` with zeros (constant -> 0)
        comps = np.hstack([comps, np.zeros((comps.shape[0], dim - comps.shape[1]))])
    comps = np.round(comps, 9)                     # snap SVD noise so identical embeddings
    #                                                share a coord (no 1e-16 tercile flips)
    coords = []
    for row in comps:
        c = []
        for d in range(dim):
            col = comps[:, d]
            lo, hi = np.quantile(col, 1 / 3), np.quantile(col, 2 / 3)
            v = row[d]
            c.append(0 if v <= lo else (2 if v > hi else 1))
        coords.append(tuple(c))
    return coords


# ---------------------------------------------------------------- admissions ----

def _cos(a, b) -> float:
    na, nb = np.linalg.norm(a), np.linalg.norm(b)
    return float(a @ b / (na * nb)) if na and nb else 0.0


def redundancy(embs) -> float:
    e = list(embs)
    if len(e) < 2:
        return 0.0
    sims = [_cos(e[i], e[j]) for i in range(len(e)) for j in range(i + 1, len(e))]
    return float(np.mean(sims))


def struct_admit(branches, dim: int = DIM):
    """One representative (highest logprob) per distinct coordinate, admitted line-free."""
    best: dict[tuple, int] = {}
    for i, b in enumerate(branches):
        c = b["coord"]
        if c not in best or b["logprob"] > branches[best[c]]["logprob"]:
            best[c] = i
    reps = sorted(best.values())
    receipt = make_structural_receipt(
        [StructuralBranch(str(i), branches[i]["coord"]) for i in reps], dim)
    admitted = sorted(int(bid) for bid in receipt.admitted_ids())
    return admitted, receipt


def score_admit(branches, m: int):
    """Top-m branches by logprob (the count-by-score budget)."""
    order = sorted(range(len(branches)), key=lambda i: (-branches[i]["logprob"], i))
    return sorted(order[:m])


def task_metrics(branches, dim: int = DIM) -> dict:
    struct_idx, receipt = struct_admit(branches, dim)
    m = len(struct_idx)
    score_idx = score_admit(branches, m)

    def recall(idx):
        return int(any(branches[i]["correct"] for i in idx))

    top_idx = score_admit(branches, 1)[0]
    return {
        "m": m,
        "score_recall": recall(score_idx),
        "struct_recall": recall(struct_idx),
        "score_redundancy": redundancy([branches[i]["emb"] for i in score_idx]),
        "struct_redundancy": redundancy([branches[i]["emb"] for i in struct_idx]),
        "top_score_correct": int(branches[top_idx]["correct"]),
        "any_correct": int(any(b["correct"] for b in branches)),
        "struct_is_cap": is_cap(branches[i]["coord"] for i in struct_idx),
    }


def analyze(per_task: list[dict]) -> dict:
    usable = [t for t in per_task if t["any_correct"]]                 # a solution exists to retain
    collapse = [t for t in usable if not t["top_score_correct"]]      # top-score is wrong
    def mean(key, rows):
        return float(np.mean([t[key] for t in rows])) if rows else 0.0
    out = {
        "n_tasks": len(per_task), "n_usable": len(usable), "n_collapse": len(collapse),
        "mean_score_redundancy": mean("score_redundancy", usable),
        "mean_struct_redundancy": mean("struct_redundancy", usable),
        "mean_score_recall_collapse": mean("score_recall", collapse),
        "mean_struct_recall_collapse": mean("struct_recall", collapse),
        "all_struct_caps": all(t["struct_is_cap"] for t in per_task),
    }
    out["campaign_verdict"] = _classify(out, usable, collapse)
    return out


def _classify(o, usable, collapse) -> str:
    if not o["all_struct_caps"]:
        return "K-ARTIFACT"
    if len(usable) > 0 and len(collapse) < len(usable) / 3:
        return "K-NULL-NOEXPLORE"                          # top-score already correct mostly
    diverse = o["mean_score_redundancy"] - o["mean_struct_redundancy"] >= 0.05
    retains = o["mean_struct_recall_collapse"] >= o["mean_score_recall_collapse"]
    if diverse and retains:
        return "K-SUPPORT"
    if not diverse:
        return "K-NULL-STRUCT-NOHELP-redundancy"
    return "K-NULL-STRUCT-NOHELP-recall"


# ------------------------------ V3: faithful slot maps + small-budget recall@k (slot-map prereg) ----

MAPS = ("embedding", "whitened", "answer")


def _f33_cap() -> list[tuple[int, int, int]]:
    """A fixed greedy cap (line-free set) in F_3^3 — for the answer-bucket coordinate."""
    cap: list[tuple[int, int, int]] = []
    for p in [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]:
        if not any(is_line(cap[i], cap[j], p)
                   for i in range(len(cap)) for j in range(i + 1, len(cap))):
            cap.append(p)
    return cap


F33_CAP = _f33_cap()


def coords_for(branches, mode: str) -> list[tuple[int, ...]]:
    """Slot-map per the prereg. embedding/whitened: PCA->tercile of (whitened) embeddings;
    answer: bucket by the integer the branch concludes (distinct -> distinct cap points),
    diversity-by-conclusion computed with NO ground truth."""
    if mode in ("embedding", "whitened"):
        return quantize_to_f3([b["emb"] for b in branches], mode=mode)
    if mode == "answer":
        seen: dict[object, tuple] = {}
        coords = []
        for b in branches:
            key = b.get("concluded")
            if key not in seen:
                seen[key] = F33_CAP[len(seen) % len(F33_CAP)]
            coords.append(seen[key])
        return coords
    raise ValueError(mode)


def slotmap_recall(branches, coords, dim: int = DIM) -> dict:
    """Small-budget recall@k: count-by-score (top-k logprob) vs the structural
    diversity-constrained top-k (best-logprob branch per distinct line-free slot)."""
    for b, c in zip(branches, coords):
        b["coord"] = c
    struct_idx, _ = struct_admit(branches, dim)
    struct_sorted = sorted(struct_idx, key=lambda i: -branches[i]["logprob"])
    score_sorted = sorted(range(len(branches)), key=lambda i: (-branches[i]["logprob"], i))

    def has_correct(idx):
        return int(any(branches[i]["correct"] for i in idx))

    out = {"m": len(struct_idx),
           "struct_is_cap": is_cap(branches[i]["coord"] for i in struct_idx),
           "struct_redundancy": redundancy([branches[i]["emb"] for i in struct_idx])}
    for k in (1, 2, 3):
        out[f"score_recall@{k}"] = has_correct(score_sorted[:k])
        out[f"struct_recall@{k}"] = has_correct(struct_sorted[:k])
    return out


def task_metrics_v3(branches) -> dict:
    top = sorted(range(len(branches)), key=lambda i: (-branches[i]["logprob"], i))[0]
    return {"top_score_correct": int(branches[top]["correct"]),
            "any_correct": int(any(b["correct"] for b in branches)),
            "maps": {m: slotmap_recall(branches, coords_for(branches, m)) for m in MAPS}}


def analyze_v3(per_task: list[dict]) -> dict:
    usable = [t for t in per_task if t["any_correct"]]
    collapse = [t for t in usable if not t["top_score_correct"]]

    def cmean(fn, rows):
        return float(np.mean([fn(t) for t in rows])) if rows else 0.0

    maps = {}
    for m in MAPS:
        g = lambda t, k: t["maps"][m][f"struct_recall@{k}"] - t["maps"][m][f"score_recall@{k}"]
        maps[m] = {
            **{f"mean_struct_recall@{k}_collapse": cmean(lambda t: t["maps"][m][f"struct_recall@{k}"], collapse)
               for k in (1, 2, 3)},
            **{f"mean_score_recall@{k}_collapse": cmean(lambda t: t["maps"][m][f"score_recall@{k}"], collapse)
               for k in (1, 2, 3)},
            "gap@2": cmean(lambda t: g(t, 2), collapse),
            "gap@3": cmean(lambda t: g(t, 3), collapse),
            "mean_struct_redundancy": cmean(lambda t: t["maps"][m]["struct_redundancy"], usable),
            "all_caps": all(t["maps"][m]["struct_is_cap"] for t in per_task),
        }
    out = {"n_tasks": len(per_task), "n_usable": len(usable), "n_collapse": len(collapse),
           "maps": maps}
    out["campaign_verdict"] = _classify_v3(out)
    return out


def _classify_v3(o) -> str:
    if not all(o["maps"][m]["all_caps"] for m in MAPS):
        return "K-ARTIFACT"
    if o["n_usable"] > 0 and o["n_collapse"] < o["n_usable"] / 3:
        return "K-NULL-NOEXPLORE-STILL"
    base = max(o["maps"]["embedding"]["gap@2"], o["maps"]["embedding"]["gap@3"])
    w = max(o["maps"]["whitened"]["gap@2"], o["maps"]["whitened"]["gap@3"])
    a = max(o["maps"]["answer"]["gap@2"], o["maps"]["answer"]["gap@3"])
    if w >= 0.25 and w > base:
        return "K-SUPPORT-FAIRTEST"
    if a >= 0.25 and a > base:
        return "K-PARTIAL-ANSWER-ONLY"
    return "K-NULL-NO-SMALLBUDGET-GAP"


# --------------------------------------------------------------- synthetic pin ----

def synthetic_branches() -> list[dict]:
    rng = np.random.default_rng(SEED)
    branches = []
    base = rng.normal(size=6)
    for i in range(5):                                       # high-score WRONG near-duplicates
        branches.append({"id": f"dup{i}", "logprob": -1.0 - 0.01 * i,
                         "correct": False, "emb": base + 0.001 * rng.normal(size=6)})
    branches.append({"id": "WINNER", "logprob": -5.0,        # low-score CORRECT, distinct
                     "correct": True, "emb": rng.normal(size=6) + np.array([5, 0, 0, 0, 0, 0])})
    branches.append({"id": "x", "logprob": -4.0, "correct": False,
                     "emb": rng.normal(size=6) + np.array([0, 5, 0, 0, 0, 0])})
    branches.append({"id": "y", "logprob": -4.5, "correct": False,
                     "emb": rng.normal(size=6) + np.array([0, 0, 5, 0, 0, 0])})
    coords = quantize_to_f3([b["emb"] for b in branches])
    for b, c in zip(branches, coords):
        b["coord"] = c
    return branches


def synthetic_branches_v3() -> list[dict]:
    """Slot-map pin: two high-logprob WRONG branches that are IDENTICAL (one slot) plus a
    medium-logprob CORRECT branch in a distinct slot. count-by-score@2 spends both slots on
    the wrong cluster; the diversity-constrained struct@2 reaches the correct slot. Two
    distinct slots only (no third point) so no cap line can spuriously form."""
    base = np.zeros(6); base[0] = 1.0
    return [
        {"id": "dup0", "logprob": -1.0, "correct": False, "concluded": "99", "emb": base.copy()},
        {"id": "dup1", "logprob": -1.1, "correct": False, "concluded": "99", "emb": base.copy()},
        {"id": "WINNER", "logprob": -1.5, "correct": True, "concluded": "42",
         "emb": np.array([0., 5, 0, 0, 0, 0])},
    ]


def dry_run() -> dict:
    tm = task_metrics(synthetic_branches())
    v3 = task_metrics_v3(synthetic_branches_v3())
    return {"version": VERSION, "mode": "synthetic", "task": tm, "task_v3": v3}


# --------------------------------------------------------------- real search ----

def load_model(name: str, dtype: str = "float32"):
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    td = {"float32": torch.float32, "bfloat16": torch.bfloat16}[dtype]
    tok = AutoTokenizer.from_pretrained(name)
    model = AutoModelForCausalLM.from_pretrained(name, dtype=td)
    model.eval()
    return tok, model


def sample_branches(tok, model, prompt: str, answer: str,
                    max_new_tokens: int = MAX_NEW_SHORT, word_boundary: bool = False) -> list[dict]:
    import torch
    torch.manual_seed(SEED)
    enc = tok(prompt, return_tensors="pt")
    plen = enc["input_ids"].shape[1]
    with torch.no_grad():
        gen = model.generate(**enc, do_sample=True, num_return_sequences=K,
                             max_new_tokens=max_new_tokens, temperature=0.9, top_p=0.95,
                             pad_token_id=tok.eos_token_id)
    branches = []
    for k in range(gen.shape[0]):
        full = gen[k]
        text = tok.decode(full[plen:], skip_special_tokens=True)
        with torch.no_grad():
            out = model(full.unsqueeze(0), output_hidden_states=True)
        logits = out.logits[0]
        lp = 0.0
        for t in range(plen - 1, full.shape[0] - 1):
            lp += float(torch.log_softmax(logits[t], dim=-1)[full[t + 1]])
        emb = out.hidden_states[-1][0].mean(0).to(torch.float64).numpy()
        ints = re.findall(r"-?\d+", text)
        branches.append({"id": f"b{k}", "logprob": lp,
                         "correct": _is_correct(text, answer, word_boundary),
                         "concluded": (ints[-1] if ints else None),     # branch's own conclusion
                         "text": text.strip(), "emb": emb})
    coords = quantize_to_f3([b["emb"] for b in branches])
    for b, c in zip(branches, coords):
        b["coord"] = c
    return branches


def _run_task_set(tok, model, tasks, max_new_tokens=MAX_NEW_SHORT, word_boundary=False) -> dict:
    per_task = []
    for prompt, answer in tasks:
        tm = task_metrics(sample_branches(tok, model, prompt, answer,
                                          max_new_tokens, word_boundary))
        tm["answer"] = answer
        per_task.append(tm)
    return {"per_task": per_task, **analyze(per_task)}


def real_run(model_name: str, dtype: str = "float32") -> dict:
    tok, model = load_model(model_name, dtype)
    easy = _run_task_set(tok, model, TASKS)
    hard = _run_task_set(tok, model, HARD_TASKS)
    return {"version": VERSION, "mode": "real", "model": model_name, "dtype": dtype,
            "easy": easy, "hard": hard,
            "campaign_verdict": easy["campaign_verdict"],
            "hard_verdict": hard["campaign_verdict"]}


def real_run_reasoning(model_name: str, dtype: str = "float32") -> dict:
    """The scale re-run: multi-step reasoning tasks, longer branches, on a larger model."""
    tok, model = load_model(model_name, dtype)
    res = _run_task_set(tok, model, REASONING_TASKS,
                        max_new_tokens=MAX_NEW_REASONING, word_boundary=True)
    return {"version": VERSION, "mode": "real-reasoning", "model": model_name, "dtype": dtype,
            "max_new_tokens": MAX_NEW_REASONING, "k": K, **res}


def dump_reasoning_branches(model_name: str, out_path: str, dtype: str = "float32") -> dict:
    """Run the reasoning regime ONCE and save raw branches (logprob, correctness, concluded
    integer, embedding) so the slot-map analysis can iterate OFFLINE with no model."""
    tok, model = load_model(model_name, dtype)
    tasks_out = []
    for prompt, answer in REASONING_TASKS:
        branches = sample_branches(tok, model, prompt, answer,
                                   max_new_tokens=MAX_NEW_REASONING, word_boundary=True)
        tasks_out.append({"answer": answer, "branches": [
            {"logprob": b["logprob"], "correct": b["correct"], "concluded": b["concluded"],
             "text": b["text"], "emb": [float(x) for x in b["emb"]]} for b in branches]})
    dump = {"version": VERSION, "mode": "dump", "model": model_name, "dtype": dtype,
            "max_new_tokens": MAX_NEW_REASONING, "k": K, "tasks": tasks_out}
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(dump, fh)
    return {"dumped": out_path, "n_tasks": len(tasks_out)}


def analyze_dump(path: str) -> dict:
    """Offline slot-map re-analysis of a saved branch dump (no model needed)."""
    with open(path, encoding="utf-8") as fh:
        dump = json.load(fh)
    per_task = []
    for t in dump["tasks"]:
        branches = [{"id": f"b{i}", "logprob": b["logprob"], "correct": b["correct"],
                     "concluded": b["concluded"], "text": b.get("text", ""),
                     "emb": np.asarray(b["emb"], dtype=float)}
                    for i, b in enumerate(t["branches"])]
        tm = task_metrics_v3(branches)
        tm["answer"] = t["answer"]
        per_task.append(tm)
    return {"version": VERSION, "mode": "analyze-slotmap", "model": dump.get("model"),
            "dtype": dump.get("dtype"), "source": path, "per_task": per_task,
            **analyze_v3(per_task)}


def main(argv=None):
    ap = argparse.ArgumentParser(description="H-IV search white-box probe.")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--real", action="store_true")
    ap.add_argument("--regime", choices=("short", "reasoning"), default="short")
    ap.add_argument("--model", default="Qwen/Qwen2.5-0.5B-Instruct")
    ap.add_argument("--dtype", default="float32", choices=("float32", "bfloat16"))
    ap.add_argument("--dump-branches", default=None,
                    help="run the reasoning regime and SAVE raw branches for offline slot-map analysis")
    ap.add_argument("--analyze", default=None,
                    help="re-analyze a saved branch dump under the slot maps (no model)")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)

    out = {"dry_run": dry_run()}
    if args.dump_branches:
        out["dump"] = dump_reasoning_branches(args.model, args.dump_branches, args.dtype)
    elif args.analyze:
        out["slotmap"] = analyze_dump(args.analyze)
    elif args.real:
        out["real"] = (real_run_reasoning(args.model, args.dtype) if args.regime == "reasoning"
                       else real_run(args.model, args.dtype))
    text = json.dumps(out, indent=2)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            fh.write(text)
    print(text)
    return out


if __name__ == "__main__":
    main()
