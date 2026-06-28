"""Frozen H-III falsifier — the holonomy filter detects curl, not the hierarchy.

Pins the counterexamples against the live `discrete_holonomy_receipt`:
  python -m pytest scripts/test_h3_holonomy_filter_falsifier.py -q
"""

import h3_holonomy_filter_falsifier as h3
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO


def test_gradient_hijack_is_invisible():
    leg = h3.leg_A_gradient_hijack_invisible()
    assert leg["fires"]
    assert leg["benign"][0] == ACCEPT and leg["hijack"][0] == ACCEPT
    assert leg["benign"][1] == 0 and leg["hijack"][1] == 0      # both circulation zero
    assert leg["benign_rank"][0] == "system"                   # hierarchy hijacked:
    assert leg["hijack_rank"][0] == "injected"                 # injected now on top


def test_gauge_transform_leaves_observable_invariant():
    leg = h3.leg_A_gauge_transform_invariance()
    assert leg["fires"]
    assert leg["observed_circulation_invariant"]
    assert leg["rank_before"][0] == "system" and leg["rank_after"][0] == "injected"


def test_benign_curl_is_false_positive():
    leg = h3.leg_B_benign_curl_flagged()
    assert leg["fires"]
    assert leg["verdict"] == STRUCTURAL_ZERO
    assert leg["observed_circulation"] != 0


def test_control_flux_attack_is_caught():
    c = h3.control_flux_attack_caught()
    assert c["holds"]
    assert c["verdict"] == STRUCTURAL_ZERO


def test_falsifier_fires_and_control_holds():
    out = h3.run()
    assert out["falsifier_fires"] is True
    assert out["control_holds"] is True
    assert out["verdict"] == "FALSIFIER FIRES"
