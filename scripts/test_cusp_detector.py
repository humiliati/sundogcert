"""Frozen tests for the sampled cusp detector.

Run:
  python -m pytest scripts/test_cusp_detector.py -q
"""

from dataclasses import replace

import cusp_detector as cd


def test_cubic_like_sample_triggers_structural_zero():
    receipt = cd.demo_cusp_receipt()

    assert receipt.verdict == cd.STRUCTURAL_ZERO
    assert receipt.reason == "sampled-cusp-signature"
    assert receipt.c2 == (-6, 0, 6)
    assert receipt.c3 == (6, 6)
    assert cd.verify_cusp_receipt(receipt)


def test_smooth_convex_sample_accepts():
    receipt = cd.demo_smooth_receipt()

    assert receipt.verdict == cd.ACCEPT
    assert receipt.reason == "no-sampled-cusp"
    assert receipt.c2 == (2, 2, 2)
    assert receipt.c3 == (0, 0)
    assert cd.verify_cusp_receipt(receipt)


def test_detector_quarantines_malformed_samples():
    count_bad = cd.make_cusp_receipt(((-1, 1), (0, 0), (1, 1)))
    spacing_bad = cd.make_cusp_receipt(((-2, -8), (-1, -1), (0, 0), (2, 1), (3, 8)))
    threshold_bad = cd.make_cusp_receipt(
        ((-2, -8), (-1, -1), (0, 0), (1, 1), (2, 8)),
        cd.CuspThresholds(min_abs_c2=-1),
    )

    assert count_bad.verdict == cd.QUARANTINE
    assert count_bad.reason == "sample-count-mismatch"
    assert spacing_bad.verdict == cd.QUARANTINE
    assert spacing_bad.reason == "samples-not-evenly-spaced"
    assert threshold_bad.verdict == cd.QUARANTINE
    assert threshold_bad.reason == "negative-threshold"
    assert cd.verify_cusp_receipt(count_bad)
    assert cd.verify_cusp_receipt(spacing_bad)
    assert cd.verify_cusp_receipt(threshold_bad)


def test_sign_change_outside_third_bound_quarantines():
    receipt = cd.make_cusp_receipt(((-2, -100), (-1, -1), (0, 0), (1, 1), (2, 100)))

    assert receipt.verdict == cd.QUARANTINE
    assert receipt.reason == "third-bound-exceeded"
    assert receipt.c2 == (-98, 0, 98)
    assert receipt.c3 == (98, 98)
    assert cd.verify_cusp_receipt(receipt)


def test_weak_or_off_center_sign_change_accepts():
    weak = cd.make_cusp_receipt(
        ((-2, "-1/10"), (-1, "-1/20"), (0, 0), (1, "1/20"), (2, "1/10"))
    )
    off_center = cd.make_cusp_receipt(((-2, -8), (-1, 0), (0, 1), (1, 1), (2, 8)))

    assert weak.verdict == cd.ACCEPT
    assert weak.reason == "no-sampled-cusp"
    assert off_center.verdict == cd.ACCEPT
    assert off_center.reason == "no-sampled-cusp"
    assert cd.verify_cusp_receipt(weak)
    assert cd.verify_cusp_receipt(off_center)


def test_tampered_cusp_receipt_rejected():
    receipt = cd.demo_cusp_receipt()

    stale_digest = replace(receipt, verdict=cd.ACCEPT)
    assert not cd.verify_cusp_receipt(stale_digest)

    wrong_c2 = replace(receipt, c2=(-6, 1, 6)).with_digest()
    assert not cd.verify_cusp_receipt(wrong_c2)


def test_digest_is_stable():
    receipt1 = cd.demo_cusp_receipt()
    receipt2 = cd.demo_cusp_receipt()

    assert receipt1.digest == receipt2.digest
    assert len(receipt1.digest) == 64
