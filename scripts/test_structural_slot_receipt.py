"""Frozen tests for the re-specified trace bound — the H-IV fix.

Each falsifier leg is re-run against BOTH the old count-by-score budget receipt
(`branch_budget_receipt`) and the new structural line-free slot receipt
(`structural_slot_receipt`), showing the fix gives the right answer where the old
receipt failed.

  python -m pytest scripts/test_structural_slot_receipt.py -q
"""

from dataclasses import replace

import structural_slot_receipt as ss
from branch_budget_receipt import (
    ACCEPT,
    QUARANTINE,
    STRUCTURAL_ZERO,
    SearchBranch,
    budget_search_branches,
)


# --------------------------------------------- the fix closes the falsifier ----

def test_legA_low_score_winner_now_admitted():
    # distractors + winner together form a cap (line-free); winner has the lowest score.
    coords = {"d0": (0, 0), "d1": (1, 0), "d2": (0, 1), "WINNER": (1, 1)}
    scores = {"d0": 10, "d1": 9, "d2": 8, "WINNER": 1}

    old = budget_search_branches(
        [SearchBranch(b, i, "q", scores[b]) for i, b in enumerate(coords)], budget=2)
    assert "WINNER" in old.overflow_branch_ids          # count-by-score refuses the winner

    new = ss.make_structural_receipt(
        [ss.StructuralBranch(b, c, score=scores[b], solves=(b == "WINNER"))
         for b, c in coords.items()], dim=2)
    assert new.verdict == ACCEPT                         # whole set is a cap
    assert "WINNER" in new.admitted_ids()               # admitted on STRUCTURE, not score
    assert ss.verify_structural_receipt(new)


def test_legB_bounded_by_capacity_not_count():
    pts = [(i, j) for i in range(3) for j in range(3)]   # all 9 points of F_3^2
    branches = [ss.StructuralBranch(f"b{i}", c) for i, c in enumerate(pts)]

    # old count cap with a big budget bounds nothing: it accepts all 9.
    old = budget_search_branches(
        [SearchBranch(f"b{i}", i, "q", 100 - i) for i in range(9)], budget=100)
    assert old.verdict == ACCEPT and len(old.overflow_branch_ids) == 0

    new = ss.make_structural_receipt(branches, dim=2)
    assert new.verdict == STRUCTURAL_ZERO
    assert ss.is_cap(c for _, c in new.admitted)         # admitted set is a genuine cap
    assert len(new.admitted) <= ss.CAP_CAPACITY[2]       # bounded by the structural capacity (4)
    assert len(new.admitted) < len(pts)                  # ... regardless of candidate count
    assert ss.verify_structural_receipt(new)


def test_legB_refusals_are_structural():
    # every refused branch genuinely would form a line with the admitted cap.
    r = ss.demo_overflow_receipt()
    admitted = [c for _, c in r.admitted]
    by_id = {f"b{i}": (i // 3, i % 3) for i in range(9)}
    for bid in r.refused_branch_ids:
        assert ss._forms_line(by_id[bid], admitted)


# ----------------------------------------------------- malformed / controls ----

def test_known_cap_accepts():
    assert ss.demo_cap_receipt().verdict == ACCEPT


def test_malformed_inputs_quarantine():
    good = [ss.StructuralBranch("a", (0, 0)), ss.StructuralBranch("b", (1, 0))]
    # duplicate coordinate
    dup = [ss.StructuralBranch("a", (0, 0)), ss.StructuralBranch("b", (0, 0))]
    assert ss.make_structural_receipt(dup, dim=2).reason == "duplicate-coordinate"
    # coordinate not in F_3^n
    bad = [ss.StructuralBranch("a", (3, 0)), ss.StructuralBranch("b", (1, 0))]
    assert ss.make_structural_receipt(bad, dim=2).reason == "coordinate-not-in-F3n"
    # wrong dimension
    assert ss.make_structural_receipt(good, dim=3).reason == "coordinate-not-in-F3n"


def test_tampered_receipt_rejected():
    r = ss.demo_overflow_receipt()
    assert ss.verify_structural_receipt(r)
    forged = replace(r, verdict=ACCEPT).with_digest()
    assert not ss.verify_structural_receipt(forged)
