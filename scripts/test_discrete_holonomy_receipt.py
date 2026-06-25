"""Frozen tests for toy discrete-holonomy receipts.

Run:
  python -m pytest scripts/test_discrete_holonomy_receipt.py -q
"""

from dataclasses import replace

import discrete_holonomy_receipt as dhr


def test_closed_loop_zero_accepts_and_verifies():
    receipt = dhr.demo_closed_zero_receipt()

    assert receipt.verdict == dhr.ACCEPT
    assert receipt.reason == "closed-loop-zero"
    assert receipt.gauge_steps == (3, 6, -9)
    assert receipt.endpoint_diff == 0
    assert receipt.gauge_circulation == 0
    assert receipt.observed_circulation == 0
    assert receipt.residual_circulation == 0
    assert dhr.verify_holonomy_receipt(receipt)


def test_nonzero_residual_is_structural_zero():
    receipt = dhr.demo_nonzero_residual_receipt()

    assert receipt.verdict == dhr.STRUCTURAL_ZERO
    assert receipt.reason == "nonzero-loop-residual"
    assert receipt.gauge_circulation == 0
    assert receipt.observed_circulation == 2
    assert receipt.residual_circulation == 2
    assert dhr.verify_holonomy_receipt(receipt)


def test_malformed_inputs_quarantine_and_verify():
    assert dhr.make_holonomy_receipt(("root",), {"root": 1}, ()).reason == "path-too-short"
    assert dhr.make_holonomy_receipt(("root", "root"), {"root": 1}, ()).reason == "edge-count-mismatch"
    assert dhr.make_holonomy_receipt(("root", "missing", "root"), {"root": 1}, (0, 0)).reason == "missing-potential"
    open_path = dhr.make_holonomy_receipt(("root", "grep"), {"root": 1, "grep": 2}, (1,))
    assert open_path.verdict == dhr.QUARANTINE
    assert open_path.reason == "not-closed-loop"
    assert dhr.verify_holonomy_receipt(open_path)


def test_digest_and_payload_tampering_rejected():
    receipt = dhr.demo_closed_zero_receipt()

    stale_digest = replace(receipt, observed_circulation=1)
    assert not dhr.verify_holonomy_receipt(stale_digest)

    changed_edges = replace(receipt, edge_values=(3, 6, -8)).with_digest()
    assert not dhr.verify_holonomy_receipt(changed_edges)


def test_digest_is_stable():
    receipt1 = dhr.demo_closed_zero_receipt()
    receipt2 = dhr.demo_closed_zero_receipt()

    assert receipt1.digest == receipt2.digest
    assert len(receipt1.digest) == 64
