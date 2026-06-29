"""Frozen analysis-pin for the H-III attention white-box probe (V2: + phi_mean + ladder).

Pins the measurement map (phi_sum and phi_mean gradients, circ curl, quantization, both
receipts, AUC) on hand-built attention matrices BEFORE any real attention touches it
(prereg §4 of both the base and the scale prereg). The real run changes only the source of
A and the model size.

  python -m pytest scripts/test_h3_attention_whitebox.py -q
"""

import h3_attention_whitebox as wb
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO


def test_sum_gradient_separates_curl_is_blind():
    best = wb.dry_run()["sum"]["analysis"]["best_layer"]
    assert best["gradient_auc"] == 1.0           # authority margin perfectly separates
    assert abs(best["curl_auc"] - 0.5) < 1e-9    # loop circulation is blind (matched curl)


def test_mean_matches_sum_on_synthetic():
    # single-token spans => phi_mean == phi_sum, so the length-normalized metric reproduces
    # the frozen result on the synthetic pin (the scale-prereg phi_mean assertion).
    best = wb.dry_run()["mean"]["analysis"]["best_layer"]
    assert best["gradient_auc"] == 1.0
    assert abs(best["curl_auc"] - 0.5) < 1e-9


def test_hierarchy_receipt_separates_loop_does_not_both_metrics():
    out = wb.dry_run()
    for metric in ("sum", "mean"):
        conf = out[metric]["receipts"]
        assert conf["hierarchy"]["injected_flagged"] == conf["n_injected"]
        assert conf["hierarchy"]["benign_flagged"] == 0
        assert conf["loop"]["benign_flagged"] == conf["n_benign"]      # loop flags everything
        assert conf["loop"]["injected_flagged"] == conf["n_injected"]


def test_field_extraction_dict():
    f = wb.field_from_attention(wb._synthetic_matrix(0.7, 0.1), [0], [1], [2])
    assert f["sys_sum"] > f["slot_sum"] and f["sys_mean"] > f["slot_mean"]
    assert wb.hierarchy_verdict(f["sys_sum"], f["slot_sum"], f["circ"]) == ACCEPT
    g = wb.field_from_attention(wb._synthetic_matrix(0.1, 0.7), [0], [1], [2])
    assert g["sys_sum"] < g["slot_sum"]
    assert wb.hierarchy_verdict(g["sys_sum"], g["slot_sum"], g["circ"]) == STRUCTURAL_ZERO


def test_matched_curl_is_equal():
    a = wb.field_from_attention(wb._synthetic_matrix(0.7, 0.1), [0], [1], [2])
    b = wb.field_from_attention(wb._synthetic_matrix(0.1, 0.7), [0], [1], [2])
    assert abs(a["circ"] - b["circ"]) < 1e-9


def test_mean_normalization_multitoken_span():
    # answer row attends 0.4 to system (1 token) and 0.2+0.2 to a 2-token slot. The SUMS are
    # equal (0.4 each) but the per-token MEANS are not (0.4 vs 0.2): phi_mean divides by span.
    import numpy as np
    A = np.array([
        [1.0, 0.0, 0.0, 0.0, 0.0],
        [1.0, 0.0, 0.0, 0.0, 0.0],
        [0.5, 0.5, 0.0, 0.0, 0.0],
        [0.4, 0.3, 0.3, 0.0, 0.0],
        [0.1, 0.4, 0.2, 0.2, 0.1],          # answer row
    ])
    f = wb.field_from_attention(A, [0], [1], [2, 3])
    assert abs(f["sys_sum"] - 0.4) < 1e-9 and abs(f["slot_sum"] - 0.4) < 1e-9
    assert abs(f["sys_mean"] - 0.4) < 1e-9 and abs(f["slot_mean"] - 0.2) < 1e-9
    # sum sees no authority gap; mean does -> the metrics can disagree (the scale-prereg point)
    assert (f["sys_sum"] - f["slot_sum"]) == 0.0
    assert (f["sys_mean"] - f["slot_mean"]) > 0.0


def test_ladder_driver_shape(monkeypatch):
    # the ladder driver calls real_run per model and reports the scaling trend; stub real_run
    # so the pin exercises the aggregation without loading any model.
    fake = {"0.5B": {"n_layers": 2, "sum": {"best_layer": 1, "gradient_auc": 0.9,
                                            "curl_auc": 0.66, "verdict": "K-NULL-MARGINAL-PERSISTS"}},
            "3B": {"n_layers": 2, "sum": {"best_layer": 1, "gradient_auc": 0.95,
                                          "curl_auc": 0.55, "verdict": "K-SUPPORT-SHARPENS"}}}
    monkeypatch.setattr(wb, "real_run", lambda name, dtype="float32": fake[name])
    out = wb.run_ladder(["0.5B", "3B"])
    assert [s["curl_auc"] for s in out["scaling"]] == [0.66, 0.55]
    assert out["curl_non_increasing"] is True      # curl drops with scale => sharpening trend
