"""Frozen tests for the H-I decisive-source binding fix.

These pin that the fix closes both legs of the falsifier (without weakening the
un-designated path, which the falsifier still owns) and that the designation is
tamper-evident through the receipt digest.

Run:
  python -m pytest scripts/test_decisive_gate_fix.py -q
"""

from dataclasses import replace

import decisive_gate_fix as fix
import rs_pruning_prototype as rsp


def test_A_designation_forces_quarantine():
    a = fix.fix_A_designation_forces_quarantine()
    assert a["ungated_verdict"] == rsp.ACCEPT  # un-designated path unchanged
    assert a["ungated_dropped_decisive"] is True
    assert a["gated_verdict"] == rsp.QUARANTINE
    assert a["gated_reason"] == fix.DECISIVE_PRUNED
    assert a["fix_holds"] is True


def test_B_designation_splits_the_receipt():
    b = fix.fix_B_designation_splits_the_receipt()
    assert b["safe_verdict"] == rsp.ACCEPT
    assert b["safe_verifies"] is True
    assert b["decisive_verdict"] == rsp.QUARANTINE
    assert b["decisive_reason"] == fix.DECISIVE_PRUNED
    assert b["digests_differ"] is True
    assert b["fix_holds"] is True


def test_C_kept_decisive_still_accepts():
    c = fix.fix_C_kept_decisive_still_accepts()
    assert c["verdict"] == rsp.ACCEPT
    assert c["verifies"] is True
    assert c["all_kept_survive"] is True
    assert c["fix_holds"] is True


def test_D_malformed_designation_fails_closed():
    d = fix.fix_D_malformed_designation_fails_closed()
    assert d["out_of_range_verdict"] == rsp.QUARANTINE
    assert d["out_of_range_reason"] == fix.MALFORMED_DECISIVE
    assert d["negative_verdict"] == rsp.QUARANTINE
    # The load-bearing case: a partially valid set (0 is real, 99 is a typo) must
    # NOT silently keep {0} and accept — it fails closed.
    assert d["partially_valid_verdict"] == rsp.QUARANTINE
    assert d["partially_valid_reason"] == fix.MALFORMED_DECISIVE
    assert d["fix_holds"] is True


def test_malformed_designation_does_not_verify():
    bad = rsp.prune_trace(rsp.demo_scheme(), rsp.demo_trace(), decisive_indices=(99,))
    assert bad.verdict == rsp.QUARANTINE
    assert rsp.verify_receipt(bad) is False


def test_forged_out_of_range_decisive_is_rejected():
    # Forge an ACCEPT that claims an out-of-range decisive cell. Even with a
    # recomputed digest, verify_receipt rejects it: the designation is invalid.
    accept = rsp.prune_trace(rsp.demo_scheme(), rsp.demo_trace(), decisive_indices=(0,))
    assert rsp.verify_receipt(accept) is True
    forged = replace(accept, decisive_indices=(99,)).with_digest()
    assert rsp.verify_receipt(forged) is False


def test_non_int_designation_fails_closed():
    # A non-int index (e.g. a stray string or bool) is malformed, not coerced.
    for bad_des in (("0",), (True,), (1.0,)):
        r = rsp.prune_trace(rsp.demo_scheme(), rsp.demo_trace(), decisive_indices=bad_des)
        assert r.verdict == rsp.QUARANTINE, bad_des
        assert r.reason == fix.MALFORMED_DECISIVE, bad_des


def test_designation_is_bound_into_the_digest():
    # Same numbers, two designations -> two distinct receipts.
    scheme, base = rsp.demo_scheme(), rsp.demo_trace()
    r_none = rsp.prune_trace(scheme, base)
    r_kept = rsp.prune_trace(scheme, base, decisive_indices=(0,))
    assert r_none.digest != r_kept.digest  # () vs (0,) is a different certificate


def test_tampered_decisive_designation_is_rejected():
    # Take a clean accept, then forge a claim that a PRUNED cell (index 6) was
    # decisive. verify_receipt must reject: the gate would have quarantined it.
    accept = rsp.prune_trace(rsp.demo_scheme(), rsp.demo_trace(), decisive_indices=(0,))
    assert accept.verdict == rsp.ACCEPT
    assert rsp.verify_receipt(accept) is True

    forged = replace(accept, decisive_indices=(6,)).with_digest()
    assert rsp.verify_receipt(forged) is False  # 6 is pruned -> decisive gate broken


def test_overall_fix_closes_falsifier():
    result = fix.run()
    assert result["fix_closes_falsifier"] is True
