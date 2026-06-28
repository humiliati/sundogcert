"""Frozen tests for the re-specified fold-pair detector — the H-II fix.

The H-II falsifier's three legs (h2_cusp_detector_falsifier) are re-run as the
2-parameter families they should have been, and the new detector gives the RIGHT
answer where the c2-only `cusp_detector` failed.

Run:
  python -m pytest scripts/test_foldpair_detector.py -q
"""

from dataclasses import replace
from fractions import Fraction

import foldpair_detector as fp
from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO


def _cubic_family(es, xs):
    return [fp.make_curve(i, [(x, Fraction(x) ** 3 - e * x) for x in xs]) for i, e in enumerate(es)]


# ----------------------------------------------- the fix closes the falsifier ----

def test_legA_monotone_family_now_accepts():
    # The falsifier's monotone S-curve (c2 false-positive) is FOLD-FREE -> accept.
    s_curve = [(-2, -5), (-1, -3), (0, 0), (1, 3), (2, 5)]
    assert fp.count_interior_extrema([Fraction(s) for _, s in s_curve], Fraction(1)) == 0
    r = fp.make_foldpair_receipt([fp.make_curve(0, s_curve),
                                  fp.make_curve(1, [(-2, -7), (-1, -4), (0, 0), (1, 4), (2, 7)])])
    assert r.verdict == ACCEPT
    assert r.fold_counts == (0, 0)
    assert fp.verify_foldpair_receipt(r)


def test_legB_annihilation_now_detected():
    # The x^3 - e*x family the c2 detector was INVARIANT across: the fold count
    # drops 2 -> 0, so the annihilation is now witnessed.
    r = fp.make_foldpair_receipt(_cubic_family((3, 2, 1, 0), (-2, -1, 0, 1, 2)))
    assert r.verdict == STRUCTURAL_ZERO
    assert r.reason == "fold-pair-annihilation"
    assert r.fold_counts[0] == 2 and r.fold_counts[-1] == 0
    assert len(r.annihilations) >= 1
    assert fp.verify_foldpair_receipt(r)


def test_legC_offcenter_annihilation_now_detected():
    # The genuine cusp germ sampled OFF-center (c2 false-negative) is caught:
    # counting folds is robust to where the cusp sits.
    xs = [Fraction(2 * i - 3, 2) for i in range(5)]  # -1.5, -0.5, 0.5, 1.5, 2.5
    r = fp.make_foldpair_receipt(_cubic_family((3, 2, 1, 0), xs))
    assert r.verdict == STRUCTURAL_ZERO
    assert r.fold_counts[-1] == 0
    assert fp.verify_foldpair_receipt(r)


# ------------------------------------------------------- robustness / controls ----

def test_demos_verify():
    assert fp.demo_annihilation_receipt().verdict == STRUCTURAL_ZERO
    assert fp.demo_monotone_receipt().verdict == ACCEPT
    assert fp.verify_foldpair_receipt(fp.demo_annihilation_receipt())
    assert fp.verify_foldpair_receipt(fp.demo_monotone_receipt())


def test_stable_fold_count_accepts():
    # Two curves that both keep their fold pair: no annihilation.
    r = fp.make_foldpair_receipt(_cubic_family((3, 3), (-2, -1, 0, 1, 2)))
    assert r.fold_counts == (2, 2)
    assert r.verdict == ACCEPT


def test_malformed_inputs_quarantine():
    # one curve
    assert fp.make_foldpair_receipt([fp.make_curve(0, [(-2, -5), (-1, -3), (0, 0), (1, 3), (2, 5)])]).reason == "need-at-least-two-curves"
    # too few samples
    assert fp.make_foldpair_receipt(
        [fp.make_curve(0, [(-1, 1), (0, 0), (1, 1)]), fp.make_curve(1, [(-1, 1), (0, 0), (1, 1)])]
    ).reason == "too-few-samples"
    # uneven x spacing
    uneven = [(-2, -5), (-1, -3), (0, 0), (1, 3), (4, 5)]
    assert fp.make_foldpair_receipt([fp.make_curve(0, uneven), fp.make_curve(1, uneven)]).reason == "samples-not-evenly-spaced"
    # non-increasing control
    fam = _cubic_family((3, 0), (-2, -1, 0, 1, 2))
    bad = [fam[0], replace(fam[1], control=Fraction(0))]
    assert fp.make_foldpair_receipt([fp.make_curve(0, [(-2, -8), (-1, -1), (0, 0), (1, 1), (2, 8)]),
                                     fp.make_curve(0, [(-2, -8), (-1, -1), (0, 0), (1, 1), (2, 8)])]).reason == "control-not-increasing"


def test_unpaired_fold_change_quarantines():
    # A single-fold curve (1 extremum) next to a two-fold curve: an UNPAIRED change
    # (delta = -1) = the control sweep is too coarse to assert a clean annihilation.
    parabola = fp.make_curve(0, [(-2, 4), (-1, 1), (0, 0), (1, 1), (2, 4)])      # 1 fold
    twofold = fp.make_curve(1, [(-2, -2), (-1, 2), (0, 0), (1, -2), (2, 2)])     # 2 folds
    # delta = 1 - 2 = -1 (odd, unpaired) -> quarantine (the quarantine path clears
    # fold_counts; the reason explains the unpaired change).
    assert fp.count_interior_extrema([Fraction(s) for _, s in [(-2, 4), (-1, 1), (0, 0), (1, 1), (2, 4)]], Fraction(1)) == 1
    r = fp.make_foldpair_receipt([parabola, twofold])
    assert r.verdict == QUARANTINE
    assert r.reason == "unpaired-or-undersampled-fold-change"


def test_tampered_receipt_rejected():
    r = fp.demo_annihilation_receipt()
    assert fp.verify_foldpair_receipt(r)
    forged = replace(r, verdict=ACCEPT).with_digest()
    assert not fp.verify_foldpair_receipt(forged)
