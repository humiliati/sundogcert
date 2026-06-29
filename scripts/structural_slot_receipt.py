"""Re-specified trace bound (the H-IV fix): a structural line-free (cap-set) slot receipt.

The H-IV falsifier (`AGENTIC_TRACE_H4_FALSIFIER_RESULT.md`) showed the count-by-score
budget receipt (`branch_budget_receipt.py`) bounds the per-node admitted COUNT ranked by
score, which is neither the solution-bearing structure (it prunes a low-score winner) nor
the total tree complexity (per-node acceptance composes to `budget**depth`).

This receipt fixes it by admitting on a STRUCTURAL predicate instead of score. Each branch
carries a coordinate in F_3^n; a branch is admitted iff its coordinate keeps the admitted
set LINE-FREE (a cap set: no three distinct admitted points `a, b, c` with
`a + b + c ≡ 0 (mod 3)` — the collinearity condition in AG(n, 3)). Admission never depends
on score, and the admitted set's size is bounded by the cap-set capacity of the space —
the Ellenberg–Gijswijt structural bound — independent of how many candidates (the tree's
`budget**depth`) are offered.

  * accept: every candidate occupies a certified line-free slot (the whole candidate set
    is a cap — structurally bounded);
  * structural-zero: a branch is refused because admitting it would form a line (no
    certified structural slot remains) — the genuine published boundary;
  * quarantine: malformed (coordinate out of F_3^n, duplicate coordinate, duplicate id).

Closes both legs: a low-score solution-bearing branch with a fresh line-free coordinate is
admitted (A); the admitted set is bounded by the cap capacity, not the candidate count (B).

Integer coordinates, exact, re-verifiable — matching the other receipts' shape.
"""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass, replace

from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


@dataclass(frozen=True)
class StructuralBranch:
    branch_id: str
    coord: tuple[int, ...]      # a point in F_3^n
    score: int = 0              # carried for parity with the old receipt; NEVER gates admission
    solves: bool = False        # marks a solution-bearing branch (for tests / audit)


@dataclass(frozen=True)
class StructuralSlotReceipt:
    dim: int
    candidate_branch_ids: tuple[str, ...]
    admitted: tuple[tuple[str, tuple[int, ...]], ...]
    refused_branch_ids: tuple[str, ...]
    verdict: str
    reason: str
    digest: str = ""

    def payload(self) -> dict:
        return {
            "dim": self.dim,
            "candidate_branch_ids": list(self.candidate_branch_ids),
            "admitted": [[bid, list(c)] for bid, c in self.admitted],
            "refused_branch_ids": list(self.refused_branch_ids),
            "verdict": self.verdict,
            "reason": self.reason,
        }

    def computed_digest(self) -> str:
        enc = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(enc).hexdigest()

    def with_digest(self) -> "StructuralSlotReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def admitted_ids(self) -> tuple[str, ...]:
        return tuple(bid for bid, _ in self.admitted)

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def is_line(a: tuple[int, ...], b: tuple[int, ...], c: tuple[int, ...]) -> bool:
    """Three distinct points of F_3^n are collinear iff their coordinatewise sum is 0 mod 3."""
    if a == b or a == c or b == c:
        return False
    return all((x + y + z) % 3 == 0 for x, y, z in zip(a, b, c))


def is_cap(coords) -> bool:
    """A set of points is line-free (a cap) iff no three distinct points are collinear."""
    pts = list(coords)
    n = len(pts)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                if is_line(pts[i], pts[j], pts[k]):
                    return False
    return True


def _forms_line(coord, admitted_coords) -> bool:
    """Would adding `coord` to the admitted set create a line? (`coord` is new/distinct.)"""
    m = len(admitted_coords)
    for i in range(m):
        for j in range(i + 1, m):
            if is_line(admitted_coords[i], admitted_coords[j], coord):
                return True
    return False


def order_branches(branches) -> tuple:
    """Deterministic admission order by branch id — score-independent, by design."""
    return tuple(sorted(branches, key=lambda b: b.branch_id))


def make_structural_receipt(branches, dim: int) -> StructuralSlotReceipt:
    ordered = order_branches(branches)
    candidate_ids = tuple(b.branch_id for b in ordered)

    def quarantine(reason: str) -> StructuralSlotReceipt:
        return StructuralSlotReceipt(dim=dim, candidate_branch_ids=candidate_ids,
                                     admitted=(), refused_branch_ids=candidate_ids,
                                     verdict=QUARANTINE, reason=reason).with_digest()

    if dim < 1:
        return quarantine("bad-dimension")
    if len(set(candidate_ids)) != len(candidate_ids):
        return quarantine("duplicate-branch-id")
    for b in ordered:
        if len(b.coord) != dim or any(x not in (0, 1, 2) for x in b.coord):
            return quarantine("coordinate-not-in-F3n")
    coords = [b.coord for b in ordered]
    if len(set(coords)) != len(coords):
        return quarantine("duplicate-coordinate")

    admitted, admitted_coords, refused = [], [], []
    for b in ordered:
        if _forms_line(b.coord, admitted_coords):
            refused.append(b.branch_id)                 # no certified structural slot remains
        else:
            admitted.append((b.branch_id, b.coord))     # admitted on structure, not score
            admitted_coords.append(b.coord)

    verdict = ACCEPT if not refused else STRUCTURAL_ZERO
    reason = "line-free-cap" if not refused else "line-violation-refused"
    return StructuralSlotReceipt(dim=dim, candidate_branch_ids=candidate_ids,
                                 admitted=tuple(admitted),
                                 refused_branch_ids=tuple(refused),
                                 verdict=verdict, reason=reason).with_digest()


def verify_structural_receipt(receipt: StructuralSlotReceipt, branches=None) -> bool:
    if not receipt.digest_matches():
        return False
    if receipt.verdict not in (ACCEPT, STRUCTURAL_ZERO, QUARANTINE):
        return False
    if receipt.verdict != QUARANTINE:
        if not is_cap(c for _, c in receipt.admitted):
            return False                                # the admitted set must be a genuine cap
        admitted_ids = set(receipt.admitted_ids())
        refused = set(receipt.refused_branch_ids)
        # verdict must match the refusal set, and admitted ⊔ refused must partition candidates.
        if (receipt.verdict == ACCEPT) != (len(refused) == 0):
            return False
        if admitted_ids & refused:
            return False
        if admitted_ids | refused != set(receipt.candidate_branch_ids):
            return False
    if branches is not None:
        return receipt.payload() == make_structural_receipt(branches, receipt.dim).payload()
    return True


# --- known cap-set capacity (max line-free set in AG(n,3)); the structural budget ---------
CAP_CAPACITY = {1: 2, 2: 4, 3: 9, 4: 20, 5: 45, 6: 112}


def demo_cap_receipt() -> StructuralSlotReceipt:
    """A known 4-point cap in F_3^2: every branch occupies a line-free slot -> accept."""
    pts = [(0, 0), (1, 0), (0, 1), (1, 1)]
    return make_structural_receipt(
        [StructuralBranch(f"b{i}", c, score=i) for i, c in enumerate(pts)], dim=2)


def demo_overflow_receipt() -> StructuralSlotReceipt:
    """All 9 points of F_3^2: only a cap (<= 4) is admitted, the rest refused structurally."""
    pts = [(i, j) for i in range(3) for j in range(3)]
    return make_structural_receipt(
        [StructuralBranch(f"b{i}", c) for i, c in enumerate(pts)], dim=2)


if __name__ == "__main__":
    for name, r in (("cap", demo_cap_receipt()), ("overflow", demo_overflow_receipt())):
        print(f"{name:9s} verdict={r.verdict:15s} reason={r.reason:22s} "
              f"admitted={len(r.admitted)} refused={len(r.refused_branch_ids)} "
              f"is_cap={is_cap(c for _, c in r.admitted)} verifies={verify_structural_receipt(r)}")
