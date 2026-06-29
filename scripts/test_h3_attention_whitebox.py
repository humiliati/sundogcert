"""Frozen analysis-pin for the H-III attention white-box probe.

Pins the measurement map (phi gradient, circ curl, quantization, both receipts, AUC)
on hand-built attention matrices BEFORE any real attention touches it (prereg §4). The
real run then changes only the source of A.

  python -m pytest scripts/test_h3_attention_whitebox.py -q
"""

import h3_attention_whitebox as wb
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO


def test_gradient_separates_curl_is_blind():
    out = wb.dry_run()
    best = out["analysis"]["best_layer"]
    assert best["gradient_auc"] == 1.0          # authority margin perfectly separates
    assert abs(best["curl_auc"] - 0.5) < 1e-9   # loop circulation is blind (matched curl)


def test_hierarchy_receipt_separates_loop_does_not():
    conf = wb.dry_run()["receipts"]
    # the Hodge-split fix flags every injected, no benign:
    assert conf["hierarchy"]["injected_flagged"] == conf["n_injected"]
    assert conf["hierarchy"]["benign_flagged"] == 0
    # the old loop receipt flags everything -> no separation:
    assert conf["loop"]["benign_flagged"] == conf["n_benign"]
    assert conf["loop"]["injected_flagged"] == conf["n_injected"]


def test_field_extraction():
    # answer (row 3) attends mostly to system (col 1): margin > 0, intact.
    A = wb._synthetic_matrix(0.7, 0.1)
    ps, pl, circ = wb.field_from_attention(A, [0], [1], [2])
    assert ps > pl
    assert wb.hierarchy_verdict(ps, pl, circ) == ACCEPT
    # injected: answer attends mostly to slot -> margin < 0, flagged.
    B = wb._synthetic_matrix(0.1, 0.7)
    ps2, pl2, circ2 = wb.field_from_attention(B, [0], [1], [2])
    assert ps2 < pl2
    assert wb.hierarchy_verdict(ps2, pl2, circ2) == STRUCTURAL_ZERO


def test_matched_curl_is_equal():
    # the non-answer rows are identical, so the curl matches across benign/injected.
    A = wb._synthetic_matrix(0.7, 0.1)
    B = wb._synthetic_matrix(0.1, 0.7)
    _, _, ca = wb.field_from_attention(A, [0], [1], [2])
    _, _, cb = wb.field_from_attention(B, [0], [1], [2])
    assert abs(ca - cb) < 1e-9
