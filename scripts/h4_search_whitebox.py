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
import sys

import numpy as np

from branch_budget_receipt import SearchBranch, budget_search_branches
from structural_slot_receipt import (
    StructuralBranch,
    is_cap,
    make_structural_receipt,
)

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

VERSION = "H4_SEARCH_WHITEBOX_V1"
K = 8
DIM = 3
SEED = 0

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


# ------------------------------------------------------- coordinate map (F_3^n) ----

def quantize_to_f3(embeddings: np.ndarray, dim: int = DIM) -> list[tuple[int, ...]]:
    """PCA the task-local embeddings to `dim` components and tercile each to {0,1,2}."""
    from sklearn.decomposition import PCA
    X = np.asarray(embeddings, dtype=float)
    k = min(dim, X.shape[0] - 1, X.shape[1])
    comps = PCA(n_components=max(k, 1)).fit_transform(X) if k >= 1 else X[:, :1]
    if comps.shape[1] < dim:                       # pad to `dim` with zeros (constant -> 0)
        comps = np.hstack([comps, np.zeros((comps.shape[0], dim - comps.shape[1]))])
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


def dry_run() -> dict:
    tm = task_metrics(synthetic_branches())
    return {"version": VERSION, "mode": "synthetic", "task": tm}


# --------------------------------------------------------------- real search ----

def load_model(name: str):
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    tok = AutoTokenizer.from_pretrained(name)
    model = AutoModelForCausalLM.from_pretrained(name, dtype=torch.float32)
    model.eval()
    return tok, model


def sample_branches(tok, model, prompt: str, answer: str) -> list[dict]:
    import torch
    torch.manual_seed(SEED)
    enc = tok(prompt, return_tensors="pt")
    plen = enc["input_ids"].shape[1]
    with torch.no_grad():
        gen = model.generate(**enc, do_sample=True, num_return_sequences=K,
                             max_new_tokens=12, temperature=0.9, top_p=0.95,
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
        branches.append({"id": f"b{k}", "logprob": lp,
                         "correct": answer.lower() in text.lower(),
                         "text": text.strip(), "emb": emb})
    coords = quantize_to_f3([b["emb"] for b in branches])
    for b, c in zip(branches, coords):
        b["coord"] = c
    return branches


def _run_task_set(tok, model, tasks) -> dict:
    per_task = []
    for prompt, answer in tasks:
        tm = task_metrics(sample_branches(tok, model, prompt, answer))
        tm["answer"] = answer
        per_task.append(tm)
    return {"per_task": per_task, **analyze(per_task)}


def real_run(model_name: str) -> dict:
    tok, model = load_model(model_name)
    easy = _run_task_set(tok, model, TASKS)
    hard = _run_task_set(tok, model, HARD_TASKS)
    return {"version": VERSION, "mode": "real", "model": model_name,
            "easy": easy, "hard": hard,
            "campaign_verdict": easy["campaign_verdict"],
            "hard_verdict": hard["campaign_verdict"]}


def main(argv=None):
    ap = argparse.ArgumentParser(description="H-IV search white-box probe.")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--real", action="store_true")
    ap.add_argument("--model", default="Qwen/Qwen2.5-0.5B-Instruct")
    ap.add_argument("--json", default=None)
    args = ap.parse_args(argv)

    out = {"dry_run": dry_run()}
    if args.real:
        out["real"] = real_run(args.model)
    text = json.dumps(out, indent=2)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            fh.write(text)
    print(text)
    return out


if __name__ == "__main__":
    main()
