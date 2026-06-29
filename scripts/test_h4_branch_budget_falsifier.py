"""Frozen H-IV falsifier — the budget receipt bounds count-by-score, not structure.

Pins the counterexamples against the live `branch_budget_receipt`:
  python -m pytest scripts/test_h4_branch_budget_falsifier.py -q
"""

import h4_branch_budget_falsifier as h4
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO


def test_bound_cuts_the_only_winner():
    leg = h4.leg_A_bound_cuts_winner()
    assert leg["fires"]
    assert leg["winner_pruned"]
    # keeping the winner requires admitting every branch -> no bound at all.
    assert leg["keep_winner_needs_budget"] == leg["n_branches"]
    assert leg["no_bound_when_kept"]


def test_explosion_despite_every_node_accepting():
    leg = h4.leg_B_explosion_despite_accept()
    assert leg["fires"]
    assert leg["every_node_accepts"]
    assert leg["total_nodes"] >= leg["budget_pow_depth"]


def test_control_overflow_is_refused():
    c = h4.control_overflow_refused()
    assert c["holds"]
    assert c["verdict"] == STRUCTURAL_ZERO
    assert c["n_overflow"] == 3


def test_falsifier_fires_and_control_holds():
    out = h4.run()
    assert out["falsifier_fires"] is True
    assert out["control_holds"] is True
    assert out["verdict"] == "FALSIFIER FIRES"
