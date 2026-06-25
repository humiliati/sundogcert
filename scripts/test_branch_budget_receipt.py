"""Frozen tests for generic branch-budget receipts.

Run:
  python -m pytest scripts/test_branch_budget_receipt.py -q
"""

from dataclasses import replace

import branch_budget_receipt as bbr


def branches() -> list[bbr.SearchBranch]:
    return [
        bbr.SearchBranch("b-low", 2, "grep:low", 10),
        bbr.SearchBranch("b-top", 0, "grep:top", 30),
        bbr.SearchBranch("b-mid", 1, "grep:mid", 20),
        bbr.SearchBranch("b-tie", 3, "grep:tie", 20),
    ]


def test_order_is_public_and_deterministic():
    ordered = bbr.order_branches(branches())

    assert tuple(branch.branch_id for branch in ordered) == ("b-top", "b-mid", "b-tie", "b-low")


def test_overflow_receipt_verifies_without_private_state():
    receipt = bbr.budget_search_branches(branches(), budget=2)

    assert receipt.verdict == bbr.STRUCTURAL_ZERO
    assert receipt.reason == "branch-budget-exhausted"
    assert receipt.admitted_slots == (("b-top", 0), ("b-mid", 1))
    assert receipt.overflow_branch_ids == ("b-tie", "b-low")
    assert bbr.verify_branch_budget_receipt(receipt)
    assert bbr.verify_branch_budget_receipt(receipt, branches())


def test_accept_receipt_verifies_when_all_fit():
    receipt = bbr.budget_search_branches(branches(), budget=4)

    assert receipt.verdict == bbr.ACCEPT
    assert receipt.reason == "branch-budget-satisfied"
    assert receipt.overflow_branch_ids == ()
    assert bbr.verify_branch_budget_receipt(receipt, branches())


def test_duplicate_branch_id_quarantine_is_verifiable():
    bad = branches() + [bbr.SearchBranch("b-mid", 9, "grep:duplicate", 5)]
    receipt = bbr.budget_search_branches(bad, budget=4)

    assert receipt.verdict == bbr.QUARANTINE
    assert receipt.reason == "duplicate-branch-id"
    assert receipt.admitted_slots == ()
    assert receipt.overflow_branch_ids == receipt.candidate_branch_ids
    assert bbr.verify_branch_budget_receipt(receipt)
    assert bbr.verify_branch_budget_receipt(receipt, bad)


def test_tampered_budget_receipts_rejected():
    receipt = bbr.budget_search_branches(branches(), budget=2)

    wrong_overflow = replace(receipt, overflow_branch_ids=("b-low", "b-tie")).with_digest()
    assert not bbr.verify_branch_budget_receipt(wrong_overflow, branches())

    duplicate_slot = replace(receipt, admitted_slots=(("b-top", 0), ("b-mid", 0))).with_digest()
    assert not bbr.verify_branch_budget_receipt(duplicate_slot, branches())

    stale_digest = replace(receipt, reason="branch-budget-satisfied")
    assert not bbr.verify_branch_budget_receipt(stale_digest, branches())


def test_negative_budget_rejected_before_receipt():
    try:
        bbr.budget_search_branches(branches(), budget=-1)
    except ValueError as exc:
        assert "budget must be nonnegative" in str(exc)
    else:
        raise AssertionError("negative budget should raise ValueError")
