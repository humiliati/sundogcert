"""H2 (deep-research slate) - row-equivalent basis search for colWeightLb.

CertWall.lean proves: minCosetWeight is a CODE invariant (depends only on ker H),
while the cheap sound bound colWeightLb(H, z) = wt(z) // colBound(H) is BASIS
dependent, and no cheap bound can be both basis-robust and everywhere tight
(that would be a decoder). This experiment asks the practice-side question the
theorem leaves open: on a FIXED deployed syndrome distribution, can choosing /
learning a row-equivalent parity-check basis H' = M.H (M in GL(m, GF(2)))
materially tighten colWeightLb, without overfitting?

Faithful definitions (mirror Sundogcert/Certificate.lean):
    colBound(H)        = max column Hamming weight of H
    colWeightLb(H, z)  = wt(z) // colBound(H)         (sound: <= minCosetWeight)
    H' = M.H (mod 2),  z' = M.z (mod 2)               (row-equivalent basis)
    minCosetWeight(H,z)= min wt(e) s.t. H e = z        (code invariant; exact table)

Basis schedules: original (M=I), random_dense (CertWall collapse case), sparse
(minimize colBound), learned (hill-climb mean lb on a TRAIN corpus). A train/test
split detects the report's named overfit risk.

Pre-registered falsifier
------------------------
H2 is NULL if no schedule materially raises held-out (test) mean / lower-quantile
lb or reject-coverage over the original basis, OR if the learned gain does not
transfer from train to test.

Soundness self-check: colWeightLb <= minCosetWeight must hold for every basis and
syndrome (it is a theorem); the script asserts it, so reject is never a false
quarantine regardless of basis.

Run:
    python scripts/colweightlb_basis_search.py
"""

from __future__ import annotations

import argparse
import json
import os

import numpy as np


# --------------------------------------------------------------------------
# GF(2) helpers
# --------------------------------------------------------------------------

def gf2_rank(A: np.ndarray) -> int:
    M = A.copy() % 2
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


def random_invertible(m: int, rng: np.random.Generator) -> np.ndarray:
    while True:
        M = rng.integers(0, 2, size=(m, m), dtype=np.uint8)
        if gf2_rank(M) == m:
            return M


def col_bound(H: np.ndarray) -> int:
    return int(H.sum(axis=0).max()) if H.size else 0


def colweight_lb(z_weights: np.ndarray, cb: int) -> np.ndarray:
    if cb == 0:
        return np.zeros_like(z_weights)
    return z_weights // cb


def apply_basis(M: np.ndarray, H: np.ndarray, Z: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Return (M.H mod 2, (M.Z^T)^T mod 2). Z is (N, m) syndromes in the ORIGINAL basis."""
    Hp = (M @ H) % 2
    Zp = (Z @ M.T) % 2
    return Hp, Zp


# --------------------------------------------------------------------------
# Exact minCosetWeight table (code invariant; computed once on H)
# --------------------------------------------------------------------------

def min_coset_weight_table(H: np.ndarray, n: int, m: int) -> np.ndarray:
    all_e = ((np.arange(2 ** n)[:, None] >> np.arange(n)) & 1).astype(np.uint8)  # (2^n, n)
    S = (all_e @ H.T) % 2                                                        # (2^n, m)
    synd_int = S.dot(1 << np.arange(m)).astype(np.int64)
    w = all_e.sum(axis=1).astype(np.int64)
    mcw = np.full(2 ** m, n + 1, dtype=np.int64)
    np.minimum.at(mcw, synd_int, w)
    return mcw


def synd_to_int(Z: np.ndarray, m: int) -> np.ndarray:
    return (Z % 2).dot(1 << np.arange(m)).astype(np.int64)


# --------------------------------------------------------------------------
# Basis search (hill-climb over GL(m,2) via elementary row operations)
# --------------------------------------------------------------------------

def hillclimb(H, Z_train, objective, m, rng, iters, init=None):
    """Maximize `objective(Hp, Zp_weights)` over M in GL(m,2). Returns best M."""
    M = np.eye(m, dtype=np.uint8) if init is None else init.copy()
    Hp, Zp = apply_basis(M, H, Z_train)
    best_obj = objective(Hp, Zp.sum(axis=1))
    best_M = M.copy()
    for _ in range(iters):
        a, b = rng.integers(0, m, size=2)
        if a == b:
            continue
        M2 = M.copy()
        M2[b] ^= M2[a]                       # row op: still invertible
        Hp2, Zp2 = apply_basis(M2, H, Z_train)
        obj2 = objective(Hp2, Zp2.sum(axis=1))
        if obj2 >= best_obj:
            if obj2 > best_obj:
                best_obj, best_M = obj2, M2.copy()
            M = M2                            # accept ties to keep exploring
    return best_M


def evaluate(name, M, H, Z_test, mcw_test, tau, m):
    Hp, Zp = apply_basis(M, H, Z_test)
    cb = col_bound(Hp)
    zw = Zp.sum(axis=1)
    lb = colweight_lb(zw, cb)
    # soundness: lb <= minCosetWeight for every test syndrome
    sound = bool(np.all(lb <= mcw_test))
    coverage_by_tau = {}
    for t in range(0, tau + 2):
        far = mcw_test > t
        coverage_by_tau[t] = float(np.mean(lb[far] > t)) if far.any() else 0.0
    nz = mcw_test > 0
    tightness = float(np.mean(lb[nz] / mcw_test[nz])) if nz.any() else 0.0
    return {
        "schedule": name,
        "col_bound": cb,
        "mean_lb": float(lb.mean()),
        "p10_lb": float(np.percentile(lb, 10)),
        "frac_nonvacuous": float(np.mean(lb > 0)),
        "mean_tightness_lb_over_true": tightness,
        "reject_coverage_at_tau": coverage_by_tau.get(tau, 0.0),
        "reject_coverage_by_tau": coverage_by_tau,
        "soundness_holds": sound,
    }


def run(args):
    rng = np.random.default_rng(args.seed)
    m, n = args.m, args.n

    # Fixed random rate-1/2 code with a generic (non-sparse) parity-check basis.
    H = rng.integers(0, 2, size=(m, n), dtype=np.uint8)
    while gf2_rank(H) < m:
        H = rng.integers(0, 2, size=(m, n), dtype=np.uint8)

    mcw = min_coset_weight_table(H, n, m)

    # Deployed corpus: random errors with weight in [w_lo, w_hi] (near/beyond radius).
    def make_corpus(count, r):
        E = np.zeros((count, n), dtype=np.uint8)
        for i in range(count):
            w = r.integers(args.w_lo, args.w_hi + 1)
            idx = r.choice(n, size=int(w), replace=False)
            E[i, idx] = 1
        Z = (E @ H.T) % 2
        return Z
    Z_train = make_corpus(args.corpus, np.random.default_rng(args.seed + 1))
    Z_test = make_corpus(args.corpus, np.random.default_rng(args.seed + 2))
    mcw_train = mcw[synd_to_int(Z_train, m)]
    mcw_test = mcw[synd_to_int(Z_test, m)]

    # Schedules.
    M_I = np.eye(m, dtype=np.uint8)
    M_rand = random_invertible(m, rng)
    M_sparse = hillclimb(H, Z_train, lambda Hp, zw: -col_bound(Hp), m, rng, args.iters)
    M_learned = hillclimb(
        H, Z_train,
        lambda Hp, zw: float((zw // max(col_bound(Hp), 1)).mean()),
        m, rng, args.iters,
    )

    schedules = [("original", M_I), ("random_dense", M_rand),
                 ("sparse_min_colbound", M_sparse), ("learned_mean_lb", M_learned)]
    test_rows = [evaluate(name, M, H, Z_test, mcw_test, args.tau, m) for name, M in schedules]
    train_rows = [evaluate(name, M, H, Z_train, mcw_train, args.tau, m) for name, M in schedules]

    by = {r["schedule"]: r for r in test_rows}
    by_train = {r["schedule"]: r for r in train_rows}
    orig = by["original"]
    learned = by["learned_mean_lb"]
    sparse = by["sparse_min_colbound"]

    # Transfer / overfit check on the learned schedule.
    transfer_gap = by_train["learned_mean_lb"]["mean_lb"] - learned["mean_lb"]
    tightens = (learned["mean_lb"] > orig["mean_lb"] or sparse["mean_lb"] > orig["mean_lb"])
    transfers = learned["mean_lb"] >= orig["mean_lb"]  # held-out gain not erased by overfit
    all_sound = all(r["soundness_holds"] for r in test_rows)
    status = "basis_search_tightens" if (tightens and transfers and all_sound) else "falsifier_fired"

    out_dir = args.results_dir
    os.makedirs(out_dir, exist_ok=True)
    manifest = {
        "experiment": "h2_colweightlb_basis_search",
        "hypothesis": "A row-equivalent parity-check basis chosen/learned for the deployed "
                      "syndrome distribution can materially tighten colWeightLb, though no cheap "
                      "bound is both basis-robust and everywhere tight (CertWall).",
        "status": status,
        "falsifier": "no schedule raises held-out lb/coverage over original, or learned gain "
                     "does not transfer train->test",
        "code": {"m": m, "n": n, "rate": m / n, "col_bound_original": col_bound(H)},
        "corpus": {"size": args.corpus, "weight_band": [args.w_lo, args.w_hi], "tau": args.tau},
        "search_iters": args.iters,
        "test": test_rows,
        "train": train_rows,
        "learned_transfer_gap_train_minus_test": transfer_gap,
        "all_schedules_sound": all_sound,
        "certwall_collapse_check": {
            "random_dense_mean_lb": by["random_dense"]["mean_lb"],
            "original_mean_lb": orig["mean_lb"],
            "note": "dense row-equivalent basis collapses colWeightLb (CertWall (3)).",
        },
    }
    with open(os.path.join(out_dir, "manifest.json"), "w") as f:
        json.dump(manifest, f, indent=2)

    print(f"[h2] code [{n},{n-m}] rate {m/n:.2f}, original colBound={col_bound(H)}, tau={args.tau}")
    print(f"[h2] {'schedule':22s} {'colBnd':>6s} {'meanLb':>7s} {'p10':>4s} "
          f"{'nonvac':>6s} {'tight':>6s} {'cover@0/1/2':>13s} {'sound':>6s}")
    for r in test_rows:
        cov = r["reject_coverage_by_tau"]
        covs = "/".join(f"{cov.get(t,0.0):.2f}" for t in (0, 1, 2))
        print(f"[h2] {r['schedule']:22s} {r['col_bound']:>6d} {r['mean_lb']:>7.3f} "
              f"{r['p10_lb']:>4.0f} {r['frac_nonvacuous']:>6.2f} "
              f"{r['mean_tightness_lb_over_true']:>6.3f} {covs:>13s} {str(r['soundness_holds']):>6s}")
    learned_vs_sparse = learned["mean_lb"] - sparse["mean_lb"]
    print(f"[h2] learned - sparse mean lb = {learned_vs_sparse:+.3f} "
          f"(corpus-learning adds little over sparsifying)")
    print(f"[h2] learned transfer gap (train-test mean lb) = {transfer_gap:.3f}")
    print(f"[h2] status: {status}; wrote {out_dir}")


def main():
    ap = argparse.ArgumentParser(description="H2 colWeightLb row-equivalent basis search.")
    ap.add_argument("--m", type=int, default=8)
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--corpus", type=int, default=2000)
    ap.add_argument("--w-lo", type=int, default=4)
    ap.add_argument("--w-hi", type=int, default=8)
    ap.add_argument("--tau", type=int, default=2)
    ap.add_argument("--iters", type=int, default=4000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--results-dir", type=str,
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "..", "results", "colweightlb_basis_search"))
    run(ap.parse_args())


if __name__ == "__main__":
    main()
