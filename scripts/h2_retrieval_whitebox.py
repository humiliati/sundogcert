"""White-box H-II probe: does a REAL embedding memory realize the fold-pair
annihilation that `RetrievalCusp` proves for the attractor model?

The H-II deductive chain is closed (`ContextDecay` rule, `CuspGerm` germ,
`RetrievalCusp` attractor model). The one remaining import
(`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md` §10) is empirical: *a real retrieval landscape
is (locally) this attractor energy with a decaying barrier.* This is the H-II analog
of the H-I white-box campaign (`cliff_transfer_whitebox.py`).

We build the standard modern-Hopfield / attention retrieval energy

    E_beta(xi) = -lse(beta, X @ xi) / beta + 0.5 * ||xi||^2

over REAL document embeddings X (mean-pooled hidden states of a local model, the same
Qwen2.5-0.5B the H-I white-box used). Along the line between two stored memories we
sweep the inverse-temperature beta (= freshness) DOWN and count the interior extrema
(folds = memories + barrier) with the very `foldpair_detector` the H-II fix produced.
Prediction (pre-registered, AGENTIC_TRACE_H2_RETRIEVAL_PREREG.md): distinct memories
show fold count 3 (two wells + barrier) collapsing to 1 (merged) as freshness decays —
a `structural-zero` annihilation; a near-identical control never forms a barrier.

CPU-only, ~1 min total. Run:
  python scripts/h2_retrieval_whitebox.py --dry-run          # synthetic pin only
  python scripts/h2_retrieval_whitebox.py --real --json out.json
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction

import numpy as np

import foldpair_detector as fp
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

VERSION = "H2_RETRIEVAL_WHITEBOX_V1"
BETAS = (128.0, 64.0, 32.0, 16.0, 8.0, 4.0, 2.0)   # descending = freshness decaying
T_LO, T_HI, N_SAMPLES = -0.4, 1.4, 41
# Smooth-curve regime: real extrema have flat parabolic bottoms (per-step slope ~1e-4
# at this sampling), numerical noise ~1e-12; min_slope sits cleanly between, calibrated
# on the synthetic pin (a single well must read as 1 fold, not 0).
MIN_SLOPE = Fraction(1, 1_000_000)

DOCS = [
    "The mitochondrion is the powerhouse of the cell, producing ATP.",
    "The French Revolution began in 1789 with the storming of the Bastille.",
    "Photosynthesis converts sunlight, water, and carbon dioxide into glucose and oxygen.",
    "The stock market crashed in October 1929, triggering the Great Depression.",
    "A black hole is a region of spacetime where gravity prevents light from escaping.",
    "Beethoven composed nine symphonies despite gradually losing his hearing.",
]
CONTROL_PAIR = (
    "The mitochondrion is the powerhouse of the cell, producing ATP.",
    "The mitochondria are the cell's powerhouse, generating ATP.",
)


# ----------------------------------------------------------------- the energy ----

def hopfield_energy(xi: np.ndarray, X: np.ndarray, beta: float) -> float:
    """Modern-Hopfield / attention retrieval energy at query `xi` over patterns `X`."""
    s = X @ xi
    m = np.max(beta * s)
    lse = (m + np.log(np.sum(np.exp(beta * s - m)))) / beta
    return float(-lse + 0.5 * float(xi @ xi))


def line_path(xi_i: np.ndarray, xi_j: np.ndarray):
    ts = np.linspace(T_LO, T_HI, N_SAMPLES)
    return ts, np.array([xi_i + t * (xi_j - xi_i) for t in ts])


def _curve_from_energy(control: int, energies: np.ndarray) -> fp.Curve:
    """Scale an energy curve to unit range and hand it to the fold-pair detector as a
    Fraction-exact curve on an evenly spaced integer grid."""
    e = np.asarray(energies, dtype=float)
    rng = float(e.max() - e.min()) or 1.0
    es = (e - e.min()) / rng
    samples = [(Fraction(i), Fraction(float(v)).limit_denominator(10 ** 6))
               for i, v in enumerate(es)]
    return fp.make_curve(control, samples)


def sweep_pair(X: np.ndarray, i: int, j: int, betas=BETAS):
    """Returns (receipt, fold_counts) for the energy landscape between memories i, j as
    beta (freshness) decays. fold_counts[k] = interior extrema at betas[k]."""
    _, path = line_path(X[i], X[j])
    curves = [_curve_from_energy(k, np.array([hopfield_energy(xi, X, b) for xi in path]))
              for k, b in enumerate(betas)]
    receipt = fp.make_foldpair_receipt(
        curves, fp.FoldPairThresholds(min_slope=MIN_SLOPE, min_samples=5))
    return receipt, list(receipt.fold_counts)


def beta_star(fold_counts, betas=BETAS):
    """Annihilation freshness: the LOWEST beta at which the barrier (>= 3 folds) still
    stands. A separation discriminator — barrier persistence to lower freshness."""
    held = [b for b, c in zip(betas, fold_counts) if c >= 3]
    return min(held) if held else None


# --------------------------------------------------------------- synthetic pin ----

def synthetic_patterns(d: int = 8):
    """Two orthonormal (well-separated) memories + a near-identical pair."""
    e1 = np.zeros(d); e1[0] = 1.0
    e2 = np.zeros(d); e2[1] = 1.0
    near = e1 + 0.02 * e2
    near = near / np.linalg.norm(near)
    return np.array([e1, e2]), np.array([e1, near])


def dry_run() -> dict:
    distinct, control = synthetic_patterns()
    r_d, fc_d = sweep_pair(distinct, 0, 1)
    r_c, fc_c = sweep_pair(control, 0, 1)
    return {
        "version": VERSION, "mode": "synthetic",
        "distinct": {"fold_counts": fc_d, "verdict": r_d.verdict, "reason": r_d.reason},
        "control": {"fold_counts": fc_c, "verdict": r_c.verdict, "reason": r_c.reason},
    }


# --------------------------------------------------------------- real embeddings --

def load_embedder(name: str):
    import torch
    from transformers import AutoModel, AutoTokenizer
    tok = AutoTokenizer.from_pretrained(name)
    model = AutoModel.from_pretrained(name, dtype=torch.float32)
    model.eval()
    return tok, model


def embed_texts(texts, tok, model) -> np.ndarray:
    import torch
    vecs = []
    with torch.no_grad():
        for t in texts:
            enc = tok(t, return_tensors="pt")
            h = model(**enc).last_hidden_state[0]          # (seq, d)
            v = h.mean(dim=0)                               # mean pool
            v = v / v.norm()                               # L2 normalize
            vecs.append(v.to(torch.float64).numpy())
    return np.array(vecs)


def real_run(model_name: str) -> dict:
    tok, model = load_embedder(model_name)
    X = embed_texts(DOCS, tok, model)
    pairs = []
    structural, total = 0, 0
    for i in range(len(DOCS)):
        for j in range(i + 1, len(DOCS)):
            r, fc = sweep_pair(X, i, j)
            had_barrier = max(fc) >= 3 if fc else False
            pairs.append({"i": i, "j": j, "fold_counts": fc, "verdict": r.verdict,
                          "reason": r.reason, "had_barrier": had_barrier,
                          "beta_star": beta_star(fc)})
            total += 1
            structural += int(r.verdict == STRUCTURAL_ZERO)

    Xc = embed_texts(list(CONTROL_PAIR), tok, model)
    rc, fcc = sweep_pair(Xc, 0, 1)
    control = {"fold_counts": fcc, "verdict": rc.verdict, "reason": rc.reason,
               "cosine": float(Xc[0] @ Xc[1]), "beta_star": beta_star(fcc),
               "had_barrier": (max(fcc) >= 3 if fcc else False)}

    # True null: identical patterns (cosine = 1) must form NO barrier at any beta.
    # This is the real instrument check — a paraphrase (cosine < 1) is not a true null.
    Xid = np.array([X[0], X[0]])
    rid, fcid = sweep_pair(Xid, 0, 1)
    identical_null = {"fold_counts": fcid, "verdict": rid.verdict,
                      "had_barrier": (max(fcid) >= 3 if fcid else False)}

    n_barrier = sum(p["had_barrier"] for p in pairs)
    distinct_bstar = sorted(p["beta_star"] for p in pairs if p["beta_star"])
    return {
        "version": VERSION, "mode": "real", "model": model_name,
        "n_pairs": total, "n_with_barrier": n_barrier, "n_structural_zero": structural,
        "distinct_beta_star": distinct_bstar,
        "pairs": pairs, "control": control, "identical_null": identical_null,
        "campaign_verdict": _classify(pairs, control, structural, total, n_barrier),
        "diagnostic_verdict": _diagnose(structural, total, control, identical_null,
                                        distinct_bstar),
    }


def _diagnose(structural, total, control, identical_null, distinct_bstar) -> str:
    """Post-hoc diagnosis distinct from the literal prereg verdict: uses the IDENTICAL
    null (the true null) as the artifact check and beta* as the separation discriminator."""
    if identical_null["verdict"] == STRUCTURAL_ZERO:
        return "ARTIFACT-CONFIRMED"                # instrument makes barriers from nothing
    if structural < (2 * total + 2) // 3:
        return "NULL-NOANNIHILATION"
    # annihilation real + instrument sound; is it separation-graded?
    cb = control["beta_star"]
    if distinct_bstar and cb is not None and max(distinct_bstar) < cb:
        return "SUPPORT-SEPARATION-GRADED"         # distinct barriers persist below control's
    return "SUPPORT-WEAK-CONTROL"


def _classify(pairs, control, structural, total, n_barrier) -> str:
    if control["verdict"] == STRUCTURAL_ZERO:
        return "K-ARTIFACT"                       # control annihilated => instrument suspect
    if n_barrier == 0:
        return "K-NULL-NOBARRIER"                 # real embeddings never form a barrier
    if structural >= (2 * total + 2) // 3 and control["verdict"] == ACCEPT:
        return "K-SUPPORT"                        # >= 2/3 distinct pairs annihilate cleanly
    return "K-NULL-NOANNIHILATION"                # barrier exists but no clean drop-by-2


# ----------------------------------------------------------------------- main ----

def main(argv=None):
    ap = argparse.ArgumentParser(description="H-II retrieval-cusp white-box probe.")
    ap.add_argument("--dry-run", action="store_true", help="synthetic analysis pin only")
    ap.add_argument("--real", action="store_true", help="run on real embeddings")
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
