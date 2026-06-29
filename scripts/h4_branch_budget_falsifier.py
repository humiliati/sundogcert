"""H-IV falsifier: the budget receipt bounds branch COUNT-by-score, not the structural
boundary (solution location, or total tree complexity).

H-IV's hook: *a recursive search tree should stop at a published STRUCTURAL boundary, not
an opaque token budget.* The runtime is `branch_budget_receipt.budget_search_branches`,
which orders candidate branches by score and admits the top `budget` into slots,
refusing the overflow (`structural-zero`). It is offered as the structural cap.

But a count-by-score cap is exactly the opaque budget the hook warned against, in
structural clothing — and the slate's own falsifier names the two failures:

  * Leg A (false negative): the bound cuts off the only successful branch. The winning
    branch has a low score, so it lands in overflow and is refused; the only budget that
    keeps it is the one that admits EVERYTHING (no bound at all). The count cap cannot
    simultaneously prune and retain the solution, because it is blind to which branch is
    solution-bearing.
  * Leg B (false positive): branch explosion despite every emitted trace satisfying the
    budget. Each node admits exactly `budget` branches, so every per-node receipt is
    `accept` (`branch-budget-satisfied`), yet a depth-`d` tree has `budget**d` nodes —
    the per-node breadth cap does not bound the total search.
  * Control: when candidates genuinely exceed the budget at a node, the receipt correctly
    refuses (`structural-zero`). The detector is not dead; it bounds per-node breadth —
    just not the solution-bearing structure (A) or the total complexity (B).

Root cause: the receipt bounds the per-node admitted COUNT ranked by score, which is
neither the structural solution predicate (A) nor the total tree complexity (B). A count
cap is the wrong invariant. This is a mis-specification, not a tunable budget.

Run:
  python scripts/h4_branch_budget_falsifier.py
"""

from __future__ import annotations

import json
import sys

from branch_budget_receipt import (
    ACCEPT,
    STRUCTURAL_ZERO,
    SearchBranch,
    budget_search_branches,
    verify_branch_budget_receipt,
)

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


# ----------------------------------------------- leg A: the bound cuts the winner ----

def leg_A_bound_cuts_winner(budget: int = 2) -> dict:
    """A low-score WINNER (the only solution-bearing branch) is pruned by the count cap;
    the minimal budget that keeps it admits everything (no bound)."""
    distractors = [SearchBranch(f"distractor{i}", i, "dead end", 10 - i) for i in range(3)]
    winner = SearchBranch("WINNER", 99, "the only path to the solution", 1)  # lowest score
    branches = distractors + [winner]

    r = budget_search_branches(branches, budget)
    winner_pruned = "WINNER" in r.overflow_branch_ids

    # smallest budget at which the winner is admitted (not overflow):
    keep_budget = next(b for b in range(len(branches) + 1)
                       if "WINNER" not in budget_search_branches(branches, b).overflow_branch_ids)
    no_bound_when_kept = keep_budget >= len(branches)

    fires = (winner_pruned and no_bound_when_kept and verify_branch_budget_receipt(r, branches))
    return {
        "leg": "A_bound_cuts_winner", "budget": budget, "verdict": r.verdict,
        "winner_pruned": winner_pruned, "keep_winner_needs_budget": keep_budget,
        "n_branches": len(branches), "no_bound_when_kept": no_bound_when_kept, "fires": fires,
        "note": "the winning branch is refused; keeping it = admitting everything (no bound)",
    }


# ------------------------------------ leg B: explosion despite every node accepting ----

def leg_B_explosion_despite_accept(budget: int = 3, depth: int = 8) -> dict:
    """Each node emits exactly `budget` branches -> every per-node receipt is `accept`,
    yet a depth-`d` tree has `budget**d` nodes (the count cap bounds breadth, not the tree)."""
    total_nodes, frontier, all_accept = 0, 1, True
    for level in range(depth):
        node_branches = [SearchBranch(f"b{level}_{i}", i, "expand", 100 - i)
                         for i in range(budget)]
        r = budget_search_branches(node_branches, budget)
        if not (r.verdict == ACCEPT and verify_branch_budget_receipt(r, node_branches)):
            all_accept = False
        frontier *= budget
        total_nodes += frontier
    fires = all_accept and total_nodes >= budget ** depth
    return {
        "leg": "B_explosion_despite_accept", "budget": budget, "depth": depth,
        "total_nodes": total_nodes, "budget_pow_depth": budget ** depth,
        "every_node_accepts": all_accept, "fires": fires,
        "note": "every per-node receipt accepts while the tree explodes to budget**depth",
    }


# ------------------------------------------------------------ control: not broken ----

def control_overflow_refused(budget: int = 2) -> dict:
    """When candidates genuinely exceed the per-node budget, the receipt refuses."""
    branches = [SearchBranch(f"b{i}", i, "q", 10 - i) for i in range(5)]
    r = budget_search_branches(branches, budget)
    holds = (r.verdict == STRUCTURAL_ZERO and len(r.overflow_branch_ids) == 5 - budget
             and verify_branch_budget_receipt(r, branches))
    return {"leg": "control_overflow_refused", "budget": budget, "verdict": r.verdict,
            "n_overflow": len(r.overflow_branch_ids), "holds": holds,
            "note": "genuine per-node breadth overflow is refused; detector is not dead"}


def run() -> dict:
    legs = [leg_A_bound_cuts_winner(), leg_B_explosion_despite_accept()]
    control = control_overflow_refused()
    fires = all(leg["fires"] for leg in legs)
    return {
        "hypothesis": "H-IV trace-bounded search trees",
        "legs": legs, "control": control,
        "falsifier_fires": fires, "control_holds": control["holds"],
        "verdict": ("FALSIFIER FIRES" if fires and control["holds"] else "inconclusive"),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
