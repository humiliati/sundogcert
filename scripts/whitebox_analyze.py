"""OFFLINE analysis of whitebox_harvest.py output (CPU, re-runnable без GPU).

Per model: hidden-state linear-probe AUC by layer (can a cheap linear readout decode
the volume-override O?) vs the SAME-MODEL first-token entropy AUC (the black-box
signal). Cross-stack: CCA on PAIRED trials (same corpus seeds) -> canonical
correlations (representational similarity) + a transfer probe (train the adoption
axis on model A, test whether it predicts O in model B after alignment). Tests
whether internal legibility and the adoption direction generalize across scale/family.

  python scripts/whitebox_analyze.py --dir ../results/whitebox_ladder
"""
from __future__ import annotations
import argparse, glob, json, os
import numpy as np
from sklearn.cross_decomposition import CCA
from sklearn.decomposition import PCA
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import cross_val_score
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
import cliff_transfer_analysis as cta   # reuse fit_cliff (torch-free)


def probe_auc(X, y, n_pca=20, folds=5):
    """CV linear-probe ROC-AUC (inlined from cliff_transfer_whitebox to keep this
    offline analysis torch-free / re-runnable without the GPU box)."""
    y = np.asarray(y); X = np.asarray(X)
    if len(set(y.tolist())) < 2 or X.shape[0] < 8:
        return float("nan")
    folds = int(min(folds, np.bincount(y).min()))
    if folds < 2:
        return float("nan")
    n_pca = int(min(n_pca, X.shape[0] - 1, X.shape[1]))
    pipe = make_pipeline(StandardScaler(), PCA(n_components=n_pca), LogisticRegression(max_iter=2000))
    return float(cross_val_score(pipe, X, y, cv=folds, scoring="roc_auc").mean())


def load(path):
    d = np.load(path)
    layers = [int(L) for L in d["layers"]]
    return {"name": os.path.basename(path)[:-4].replace("__", "/"),
            "lam": d["lam"], "O": d["O"], "entropy": d["entropy"],
            "layers": layers, "hidden_dim": int(d["hidden_dim"]),
            "hid": {L: d[f"hid_L{L}"] for L in layers}}


def per_model(m):
    O = m["O"]
    valid = O >= 0
    y = O[valid]
    n_pca = min(20, max(2, len(y) // 5))  # fold-safe for small smoke N; 20 on the real run
    layer_auc = {L: probe_auc(m["hid"][L][valid], y, n_pca=n_pca) for L in m["layers"]}
    good = {L: a for L, a in layer_auc.items() if a == a}
    best_layer = max(good, key=good.get) if good else None
    # entropy AUC (same-model black-box signal)
    ent_auc = float("nan")
    if len(set(y.tolist())) == 2:
        ent_auc = float(roc_auc_score(y, m["entropy"][valid]))
    # cliff fit on O(lambda)
    rows = [{"lambda_fraction": float(l), "lambda_hat": float(l), "O": int(o)}
            for l, o in zip(m["lam"], O) if o >= 0]
    cliff = cta.fit_cliff(rows) if rows else None
    return {
        "model": m["name"], "hidden_dim": m["hidden_dim"], "n_valid": int(valid.sum()),
        "O_rate": float(y.mean()) if len(y) else None,
        "probe_auc_by_layer": {str(L): (None if a != a else round(a, 3)) for L, a in layer_auc.items()},
        "best_layer": best_layer, "best_probe_auc": round(good[best_layer], 3) if good else None,
        "entropy_auc": None if ent_auc != ent_auc else round(ent_auc, 3),
        "cliff_lambda_star": round(cliff.lambda_star, 3) if cliff else None,
        "cliff_width": round(cliff.width, 3) if cliff else None,
    }


def cross_stack(a, b, k=4):
    """Paired-trial CCA + transfer. Uses rows valid (O>=0) in BOTH models."""
    both = (a["O"] >= 0) & (b["O"] >= 0)
    if both.sum() < 12:
        return {"pair": f"{a['name']} <-> {b['name']}", "note": "too few paired valid trials"}
    la, lb = a["layers"][len(a["layers"]) // 2], b["layers"][len(b["layers"]) // 2]  # mid-depth
    XA, XB = a["hid"][la][both], b["hid"][lb][both]
    yA, yB = a["O"][both], b["O"][both]
    n = both.sum(); idx = np.arange(n); np.random.default_rng(0).shuffle(idx)
    tr, te = idx[:n // 2], idx[n // 2:]
    # PCA-reduce each model's hidden space BEFORE CCA to avoid the p>>n degeneracy
    # (raw dims 896..8192 >> n_paired => CCA would report trivial corr=1.0).
    from sklearn.decomposition import PCA
    pca_dim = int(min(50, len(tr) - 1, XA.shape[1], XB.shape[1]))
    pA = PCA(n_components=pca_dim).fit(XA[tr]); pB = PCA(n_components=pca_dim).fit(XB[tr])
    RA_tr, RA_te = pA.transform(XA[tr]), pA.transform(XA[te])
    RB_tr, RB_te = pB.transform(XB[tr]), pB.transform(XB[te])
    kk = int(min(k, pca_dim, len(tr) - 1))
    cca = CCA(n_components=kk).fit(RA_tr, RB_tr)
    ZA_tr, ZB_tr = cca.transform(RA_tr, RB_tr)
    ZA_te, ZB_te = cca.transform(RA_te, RB_te)
    # HELD-OUT canonical correlations: CCA maximizes TRAIN corr by construction (~1.0
    # always), so only the test-set correlation is meaningful (generalizing alignment).
    corrs = [round(float(np.corrcoef(ZA_te[:, i], ZB_te[:, i])[0, 1]), 3) for i in range(kk)]
    out = {"pair": f"{a['name']} <-> {b['name']}", "layers": [la, lb],
           "canonical_correlations": corrs, "n_paired": int(n)}
    # transfer: adoption axis trained on A, tested on B (predict A's O)
    if len(set(yA[tr].tolist())) == 2 and len(set(yA[te].tolist())) == 2:
        clf = LogisticRegression(max_iter=2000).fit(ZA_tr, yA[tr])
        out["transfer_auc_A_axis_on_B"] = round(float(roc_auc_score(yA[te], clf.decision_function(ZB_te))), 3)
    else:
        out["transfer_auc_A_axis_on_B"] = None
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "..", "results", "whitebox_ladder"))
    args = ap.parse_args()
    files = sorted(glob.glob(os.path.join(args.dir, "*.npz")))
    models = [load(f) for f in files]
    per = [per_model(m) for m in models]
    pairs = [cross_stack(models[i], models[j]) for i in range(len(models)) for j in range(i + 1, len(models))]
    report = {"per_model": per, "cross_stack": pairs}
    with open(os.path.join(args.dir, "analysis.json"), "w") as f:
        json.dump(report, f, indent=2)

    print(f"{'model':40s} {'dim':>5s} {'Orate':>6s} {'bestL':>5s} {'probeAUC':>8s} {'entAUC':>7s} {'cliffλ*':>7s}")
    for p in per:
        print(f"{p['model']:40s} {p['hidden_dim']:>5d} "
              f"{('%.2f'%p['O_rate']) if p['O_rate'] is not None else 'NA':>6s} "
              f"{str(p['best_layer']):>5s} {str(p['best_probe_auc']):>8s} "
              f"{str(p['entropy_auc']):>7s} {str(p['cliff_lambda_star']):>7s}")
    print("\ncross-stack:")
    for c in pairs:
        print(" ", json.dumps(c))
    print(f"\nwrote {args.dir}/analysis.json")


if __name__ == "__main__":
    main()
