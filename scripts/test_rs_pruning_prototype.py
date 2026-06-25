"""Frozen tests for the toy RS-pruning prototype.

Run:
  python -m pytest scripts/test_rs_pruning_prototype.py -q
"""

from dataclasses import replace

import rs_pruning_prototype as rsp


def test_demo_accepts_and_prunes_expected_cells():
    scheme = rsp.demo_scheme()
    trace = rsp.demo_trace()
    receipt = rsp.prune_trace(scheme, trace)

    assert receipt.verdict == rsp.ACCEPT
    assert receipt.reason == "unique-rs-survivor"
    assert receipt.survivor_poly == (3, 2, 5)
    assert receipt.agreement_indices == (0, 1, 3, 4, 5, 7)
    assert receipt.pruned_indices == (2, 6)
    assert [trace[i].label for i in receipt.pruned_indices] == [
        "stale-preference-old-model",
        "contradictory-source-unsafe-accept",
    ]


def test_demo_receipt_verifies_and_digest_is_stable():
    result1 = rsp.run_demo()
    result2 = rsp.run_demo()

    assert result1["receipt_verifies"] is True
    assert result2["receipt_verifies"] is True
    assert result1["branch_receipt_verifies"] is True
    assert result2["branch_receipt_verifies"] is True
    assert result1["receipt"]["digest"] == result2["receipt"]["digest"]
    assert result1["branch_receipt"]["digest"] == result2["branch_receipt"]["digest"]
    assert len(result1["receipt"]["digest"]) == 64
    assert len(result1["branch_receipt"]["digest"]) == 64


def test_tampered_receipt_rejected():
    receipt = rsp.prune_trace(rsp.demo_scheme(), rsp.demo_trace())

    wrong_pruned = replace(receipt, pruned_indices=(2,))
    assert not rsp.verify_receipt(wrong_pruned)

    wrong_poly = replace(receipt, survivor_poly=(3, 2, 6)).with_digest()
    assert not rsp.verify_receipt(wrong_poly)


def test_branch_budget_receipt_structural_zero_overflow():
    scheme = rsp.demo_scheme()
    trace = rsp.demo_trace()
    rs_receipt = rsp.prune_trace(scheme, trace)
    branches = rsp.demo_search_branches(trace, rs_receipt.agreement_indices)
    branch_receipt = rsp.budget_search_branches(branches, budget=4)

    assert branch_receipt.verdict == rsp.STRUCTURAL_ZERO
    assert branch_receipt.reason == "branch-budget-exhausted"
    assert branch_receipt.candidate_branch_ids == ("b00", "b01", "b03", "b04", "b05", "b07")
    assert branch_receipt.admitted_slots == (("b00", 0), ("b01", 1), ("b03", 2), ("b04", 3))
    assert branch_receipt.overflow_branch_ids == ("b05", "b07")
    assert rsp.verify_branch_budget_receipt(branch_receipt, branches)


def test_branch_budget_accepts_when_under_budget():
    trace = rsp.demo_trace()
    branches = rsp.demo_search_branches(trace, kept_indices=(0, 1, 3))
    branch_receipt = rsp.budget_search_branches(branches, budget=4)

    assert branch_receipt.verdict == rsp.ACCEPT
    assert branch_receipt.reason == "branch-budget-satisfied"
    assert branch_receipt.admitted_slots == (("b00", 0), ("b01", 1), ("b03", 2))
    assert branch_receipt.overflow_branch_ids == ()
    assert rsp.verify_branch_budget_receipt(branch_receipt, branches)


def test_tampered_branch_budget_receipt_rejected():
    result = rsp.run_demo()
    trace = rsp.demo_trace()
    branches = rsp.demo_search_branches(trace, kept_indices=(0, 1, 3, 4, 5, 7))
    receipt = rsp.budget_search_branches(branches, budget=4)

    wrong_overflow = replace(receipt, overflow_branch_ids=("b07", "b05")).with_digest()
    assert not rsp.verify_branch_budget_receipt(wrong_overflow, branches)

    wrong_slot = replace(receipt, admitted_slots=(("b00", 0), ("b01", 1), ("b03", 1), ("b04", 3))).with_digest()
    assert not rsp.verify_branch_budget_receipt(wrong_slot, branches)

    wrong_budget = replace(receipt, budget=5).with_digest()
    assert not rsp.verify_branch_budget_receipt(wrong_budget, branches)
    assert result["branch_receipt_verifies"] is True


def test_too_many_corruptions_quarantine():
    trace = rsp.demo_trace(extra_corruptions={4: 12})
    receipt = rsp.prune_trace(rsp.demo_scheme(), trace)

    assert receipt.verdict == rsp.QUARANTINE
    assert receipt.reason == "no-survivor"
    assert receipt.survivor_poly is None
    assert not rsp.verify_receipt(receipt)


def test_radius_violation_quarantine():
    scheme = rsp.RSScheme(p=17, n=6, k=3, tau=2, nodes=tuple(range(6)))
    trace = rsp.demo_trace()[:6]
    receipt = rsp.prune_trace(scheme, trace)

    assert receipt.verdict == rsp.QUARANTINE
    assert receipt.reason == "unique-radius-violated"
    assert not rsp.verify_receipt(receipt)


def test_human_report_mentions_pruned_cells():
    report = rsp.format_report(rsp.run_demo())

    assert "RS-PRUNING PROTOTYPE" in report
    assert "verdict=accept" in report
    assert "branch_budget=4 verdict=structural-zero" in report
    assert "overflow_branch_ids=['b05', 'b07']" in report
    assert "stale-preference-old-model" in report
    assert "contradictory-source-unsafe-accept" in report
