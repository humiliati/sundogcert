"""Frozen tests for the H-II (cusp detector) falsifier.

These pin that the falsifier still fires against the live cusp_detector: the
sampled c2-sign-change signature detects inflections, not fold-pair annihilations,
so it false-positives on monotone curves, is invariant across the annihilation, and
misses off-center cusp germs.

Run:
  python -m pytest scripts/test_h2_cusp_detector_falsifier.py -q
"""

import h2_cusp_detector_falsifier as fz
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO


def test_A_monotone_S_curve_is_falsely_flagged():
    a = fz.leg_A_false_positive()
    assert a["interior_extrema"] == 0          # fold-FREE
    assert a["verdict"] == STRUCTURAL_ZERO      # ...yet flagged as a cusp
    assert a["verifies"] is True
    assert a["fires"] is True


def test_B_detector_is_blind_to_the_annihilation():
    b = fz.leg_B_annihilation_blind()
    assert b["verdict_invariant"] is True       # same verdict for every e
    assert b["c2_invariant"] is True            # identical c2 = (-6,0,6)
    # the fold pair is present at e=3 (2 interior extrema) and gone at e<=0,
    # yet the detector's verdict never changes -> blind to the annihilation.
    assert b["extrema_by_e"][3] == 2
    assert b["extrema_by_e"][0] == 0
    assert b["extrema_by_e"][-3] == 0
    assert b["fires"] is True


def test_C_offcenter_cusp_germ_is_missed():
    c = fz.leg_C_false_negative()
    assert c["verdict"] == ACCEPT               # genuine x^3 cusp, missed
    assert c["fires"] is True


def test_control_detector_still_discriminates():
    ctrl = fz.control_detector_not_stuck()
    assert ctrl["parabola_verdict"] == ACCEPT
    assert ctrl["demo_cusp_verdict"] == STRUCTURAL_ZERO
    assert ctrl["holds"] is True


def test_overall_verdict():
    r = fz.run()
    assert r["falsifier_fires"] is True
    assert r["control_holds"] is True
