"""Frozen test for the HS7 consistency lock (audit_cost_check.py).

Pins the op-counts byte-exactly at n in {8, 64, 512} against the Lean cost model
(AuditCost.lean: auditCost_eq / auditCost_le), the audit verdicts, and the bump fiber-pair laws.
Deterministic: SEED = 20260610, exact rational arithmetic, no floats.
Run:  python -m pytest scripts/test_audit_cost_check.py -q
"""

from fractions import Fraction

import audit_cost_check as acc


def test_lean_cost_model_pinned_values():
    # auditCost n = n + (n - 1) + 2  (auditCost_eq), frozen at the three prereg sizes
    assert acc.lean_audit_cost(8) == 17
    assert acc.lean_audit_cost(64) == 129
    assert acc.lean_audit_cost(512) == 1025


def test_bound_3n_plus_2_pinned_values():
    # auditCost_le at the three prereg sizes: 17 <= 26, 129 <= 194, 1025 <= 1538
    for n, bound in ((8, 26), (64, 194), (512, 1538)):
        assert acc.lean_audit_cost(n) <= bound
        assert 3 * n + 2 == bound


def test_instrumented_count_matches_model_exactly():
    # measured-as-performed ops == the Lean model, on both accept and reject paths
    for n in acc.SIZES:
        u = [Fraction(k + 1, 3) for k in range(n)]
        mean = acc.pooled_mean(u)
        ops = acc.OpCounter()
        assert acc.instrumented_audit(u, mean, ops) is True
        assert ops.total == acc.lean_audit_cost(n)
        assert (ops.reads, ops.adds, ops.divs, ops.cmps) == (n, n - 1, 1, 1)
        ops2 = acc.OpCounter()
        assert acc.instrumented_audit(u, mean + Fraction(1), ops2) is False
        assert ops2.total == acc.lean_audit_cost(n)


def test_toy_n8_matches_lean_example():
    # the AuditCost.lean n=8 toy: u8 = [3,1,4,1,5,9,2,6], pooled mean 31/8
    u8 = [Fraction(x) for x in (3, 1, 4, 1, 5, 9, 2, 6)]
    assert acc.pooled_mean(u8) == Fraction(31, 8)
    ops = acc.OpCounter()
    assert acc.instrumented_audit(u8, Fraction(31, 8), ops) is True
    ops = acc.OpCounter()
    assert acc.instrumented_audit(u8, Fraction(4), ops) is False


def test_bump_fiber_pair_laws():
    # pooledMean_bump / bump_apply on a fixed pair, exact arithmetic
    u = [Fraction(x) for x in (3, 1, 4, 1, 5, 9, 2, 6)]
    delta = Fraction(7, 3)
    u2 = acc.bump(u, 2, 5, delta)
    assert acc.pooled_mean(u2) == acc.pooled_mean(u)
    assert u2[2] == u[2] + delta
    assert u2[5] == u[5] - delta
    assert u2 != u  # the populations genuinely differ


def test_full_run_frozen():
    # the seeded end-to-end run is byte-stable: same rows every time
    rows1 = acc.main()
    rows2 = acc.main()
    assert rows1 == rows2
    assert [r["n"] for r in rows1] == [8, 64, 512]
    assert [r["measured_ops"] for r in rows1] == [17, 129, 1025]
    assert [r["lean_auditCost"] for r in rows1] == [17, 129, 1025]
    assert all(r["honest_accepts"] for r in rows1)
