"""Verifier-checkable branch-budget receipts for toy agent search.

This is the runtime counterpart of the Lean `BudgetedTrace` hook in
`Sundogcert.AgenticTrace`: an admitted branch set is injected into a finite set
of slots, so the admitted branch count cannot exceed the published budget.

The receipt has three public outcomes:

* `accept`: every candidate branch fits inside the budget;
* `structural-zero`: candidates are well-formed, but overflow branches are
  refused because no certified slot remains;
* `quarantine`: the candidate trace itself is malformed, currently duplicate
  branch IDs.

This is a generic finite-budget receipt, not a cap-set receipt.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace

ACCEPT = "accept"
QUARANTINE = "quarantine"
STRUCTURAL_ZERO = "structural-zero"


@dataclass(frozen=True)
class SearchBranch:
    branch_id: str
    source_index: int
    query: str
    score: int

    def to_dict(self) -> dict:
        return {
            "branch_id": self.branch_id,
            "source_index": self.source_index,
            "query": self.query,
            "score": self.score,
        }


@dataclass(frozen=True)
class BranchBudgetReceipt:
    budget: int
    candidate_branch_ids: tuple[str, ...]
    admitted_slots: tuple[tuple[str, int], ...]
    overflow_branch_ids: tuple[str, ...]
    verdict: str
    reason: str
    digest: str = ""

    def payload(self) -> dict:
        return {
            "budget": self.budget,
            "candidate_branch_ids": list(self.candidate_branch_ids),
            "admitted_slots": [[branch_id, slot] for branch_id, slot in self.admitted_slots],
            "overflow_branch_ids": list(self.overflow_branch_ids),
            "verdict": self.verdict,
            "reason": self.reason,
        }

    def computed_digest(self) -> str:
        encoded = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def with_digest(self) -> "BranchBudgetReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def order_branches(branches: list[SearchBranch]) -> tuple[SearchBranch, ...]:
    """Public deterministic search order: highest score first, then branch id."""
    return tuple(sorted(branches, key=lambda branch: (-branch.score, branch.branch_id)))


def budget_search_branches(branches: list[SearchBranch], budget: int) -> BranchBudgetReceipt:
    if budget < 0:
        raise ValueError("budget must be nonnegative")
    ordered = order_branches(branches)
    candidate_ids = tuple(branch.branch_id for branch in ordered)
    if len(set(candidate_ids)) != len(candidate_ids):
        return BranchBudgetReceipt(
            budget=budget,
            candidate_branch_ids=candidate_ids,
            admitted_slots=(),
            overflow_branch_ids=candidate_ids,
            verdict=QUARANTINE,
            reason="duplicate-branch-id",
        ).with_digest()

    admitted = ordered[:budget]
    overflow = ordered[budget:]
    verdict = ACCEPT if not overflow else STRUCTURAL_ZERO
    reason = "branch-budget-satisfied" if not overflow else "branch-budget-exhausted"
    return BranchBudgetReceipt(
        budget=budget,
        candidate_branch_ids=candidate_ids,
        admitted_slots=tuple((branch.branch_id, slot) for slot, branch in enumerate(admitted)),
        overflow_branch_ids=tuple(branch.branch_id for branch in overflow),
        verdict=verdict,
        reason=reason,
    ).with_digest()


def _verify_quarantine(receipt: BranchBudgetReceipt) -> bool:
    if receipt.verdict != QUARANTINE or receipt.reason != "duplicate-branch-id":
        return False
    candidates = receipt.candidate_branch_ids
    return (
        len(set(candidates)) != len(candidates)
        and receipt.admitted_slots == ()
        and receipt.overflow_branch_ids == candidates
    )


def _verify_admission_or_overflow(receipt: BranchBudgetReceipt) -> bool:
    if receipt.verdict not in (ACCEPT, STRUCTURAL_ZERO):
        return False

    candidates = receipt.candidate_branch_ids
    admitted_ids = tuple(branch_id for branch_id, _ in receipt.admitted_slots)
    overflow_ids = receipt.overflow_branch_ids
    if len(set(candidates)) != len(candidates):
        return False
    if len(set(admitted_ids)) != len(admitted_ids):
        return False
    if len(set(overflow_ids)) != len(overflow_ids):
        return False
    if set(admitted_ids).intersection(overflow_ids):
        return False
    if tuple(admitted_ids + overflow_ids) != candidates:
        return False
    if len(admitted_ids) > receipt.budget:
        return False

    slots = tuple(slot for _, slot in receipt.admitted_slots)
    if len(set(slots)) != len(slots):
        return False
    if any(slot < 0 or slot >= receipt.budget for slot in slots):
        return False
    if slots != tuple(range(len(slots))):
        return False

    expected_verdict = ACCEPT if len(candidates) <= receipt.budget else STRUCTURAL_ZERO
    expected_reason = "branch-budget-satisfied" if expected_verdict == ACCEPT else "branch-budget-exhausted"
    return receipt.verdict == expected_verdict and receipt.reason == expected_reason


def verify_branch_budget_receipt(
    receipt: BranchBudgetReceipt, branches: list[SearchBranch] | None = None
) -> bool:
    if not receipt.digest_matches():
        return False
    if receipt.budget < 0:
        return False

    if receipt.verdict == QUARANTINE:
        basic_ok = _verify_quarantine(receipt)
    else:
        basic_ok = _verify_admission_or_overflow(receipt)
    if not basic_ok:
        return False

    if branches is not None:
        expected = budget_search_branches(branches, receipt.budget)
        return receipt.payload() == expected.payload()
    return True
