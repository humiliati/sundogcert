"""HS7 consistency lock: instrumented op-counter for the AuditCost.lean cost model.

NOT A KILL (prereg HS7_AUDIT_ASYMMETRY_PREREG.md section 2c): a same-author cost model cannot
self-falsify -- the model is a trust-surface item a reviewer audits (CheckCost.lean precedent).
This script locks INTERNAL CONSISTENCY only:

  1. an instrumented audit (ops counted as they happen, not from a formula) must reproduce the
     Lean cost model exactly: measured == auditCost n == n + (n - 1) + 2   (auditCost_eq), and
     measured <= 3n + 2                                                    (auditCost_le);
  2. audit verdicts must match the reference predicate r == pooledMean u   (audit_sound /
     audit_complete);
  3. the bump fiber-pair laws hold numerically on seeded populations       (pooledMean_bump /
     bump_apply): equal pooled mean, prescribed per-unit delta -- so every channel verifier,
     which sees only (report, pooledMean u), returns identical verdicts on the pair by
     construction (illustrative; the for-all-verifiers content is the Lean theorem's).

Exact rational arithmetic throughout (fractions.Fraction); no floats, fully deterministic.
Run:  python scripts/audit_cost_check.py
"""

from __future__ import annotations

import random
import sys
from fractions import Fraction

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

SEED = 20260610
SIZES = (8, 64, 512)


class OpCounter:
    """Counts field/comparison operations as they are performed."""

    def __init__(self) -> None:
        self.reads = 0
        self.adds = 0
        self.divs = 0
        self.cmps = 0

    @property
    def total(self) -> int:
        return self.reads + self.adds + self.divs + self.cmps


def pooled_mean(u: list[Fraction]) -> Fraction:
    """Reference pooled mean (uninstrumented): (sum u) / n."""
    return sum(u, Fraction(0)) / len(u)


def instrumented_audit(u: list[Fraction], report: Fraction, ops: OpCounter) -> bool:
    """The audit's dominant path, counting every operation as it happens:
    fold the n per-unit values (n term-reads, n-1 additions), one division, one equality test."""
    n = len(u)
    assert n >= 1
    acc = u[0]
    ops.reads += 1
    for k in range(1, n):
        term = u[k]
        ops.reads += 1
        acc = acc + term
        ops.adds += 1
    mean = acc / n
    ops.divs += 1
    verdict = report == mean
    ops.cmps += 1
    return verdict


def lean_audit_cost(n: int) -> int:
    """auditCost n = sumReadCost n + (n - 1) + 2  (AuditCost.lean, auditCost_eq)."""
    return n + (n - 1) + 2


def bump(u: list[Fraction], i: int, j: int, delta: Fraction) -> list[Fraction]:
    """The explicit fiber pair: +delta at i, -delta at j (i != j)."""
    assert i != j
    out = list(u)
    out[i] = out[i] + delta
    out[j] = out[j] - delta
    return out


def random_population(rng: random.Random, n: int) -> list[Fraction]:
    return [Fraction(rng.randint(-1000, 1000), rng.randint(1, 50)) for _ in range(n)]


def run_size(rng: random.Random, n: int) -> dict:
    u = random_population(rng, n)
    mean = pooled_mean(u)

    # 1. cost lock: measured == Lean model == n + (n-1) + 2, and <= 3n + 2
    ops = OpCounter()
    accepted = instrumented_audit(u, mean, ops)
    model = lean_audit_cost(n)
    assert ops.total == model, f"n={n}: measured {ops.total} != Lean auditCost {model}"
    assert ops.total <= 3 * n + 2, f"n={n}: measured {ops.total} > 3n+2 = {3 * n + 2}"

    # 2. verdict lock: honest accepts; a false report is caught (audit_complete / dishonest_caught)
    assert accepted, f"n={n}: honest report rejected"
    ops2 = OpCounter()
    false_report = mean + Fraction(1, 7)
    assert not instrumented_audit(u, false_report, ops2), f"n={n}: false report accepted"
    assert ops2.total == model, f"n={n}: reject path cost {ops2.total} != {model}"

    # 3. fiber-pair lock (pooledMean_bump / bump_apply), plus the channel-view consequence
    i, j = rng.sample(range(n), 2)
    delta = Fraction(rng.randint(1, 99), rng.randint(1, 9))
    u2 = bump(u, i, j, delta)
    assert pooled_mean(u2) == mean, f"n={n}: bump changed the pooled mean"
    assert u2[i] == u[i] + delta, f"n={n}: bump missed the prescribed delta at i"
    # any verifier of (report, pooledMean u) gets byte-identical inputs on the pair:
    report = mean  # an arbitrary fixed report; the Lean theorem quantifies over all of them
    assert (report, pooled_mean(u2)) == (report, pooled_mean(u)), f"n={n}: channel views differ"

    return {
        "n": n,
        "measured_ops": ops.total,
        "lean_auditCost": model,
        "bound_3n_plus_2": 3 * n + 2,
        "honest_accepts": accepted,
    }


def main() -> list[dict]:
    rng = random.Random(SEED)
    rows = [run_size(rng, n) for n in SIZES]
    for row in rows:
        print(
            f"n={row['n']:>4}  measured={row['measured_ops']:>5}  "
            f"auditCost={row['lean_auditCost']:>5}  bound(3n+2)={row['bound_3n_plus_2']:>5}  "
            f"match={row['measured_ops'] == row['lean_auditCost']}"
        )
    print("CONSISTENCY LOCK: PASS")
    return rows


if __name__ == "__main__":
    main()
