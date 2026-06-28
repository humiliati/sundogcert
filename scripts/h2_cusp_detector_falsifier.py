"""Falsifier for AGENTIC_TRACE_HYPOTHESES.md, Hypothesis II (Whitney A3 Cusp for
Context Decay).

H-II's pre-registered falsifier asks for either:

  * clean fresh-context retrievals that repeatedly TRIGGER the cusp detector, or
  * stale-context failures with NO cusp signature.

Both fire against the live `cusp_detector`. The finding is NOT that catastrophe
theory is wrong; it is that the detector's SPEC — a sign-change of the second
difference (`c2`) with the center exactly zero — detects an INFLECTION, which is
neither necessary nor sufficient for the A3 cusp it claims (a *fold-pair
annihilation*, where two extrema of the score merge: f' = f'' = 0). The detector
never looks at the FIRST difference (slope / critical points), so it cannot tell a
benign monotone saturation curve from a fold pair, and it is invariant across the
annihilation event itself.

  Leg A — FALSE POSITIVE: a monotone, fold-free S-curve (a healthy saturating
          retrieval score) triggers `structural-zero`.
  Leg B — ANNIHILATION-BLIND: the canonical unfolding x^3 - e*x gives an identical
          detector verdict (and identical c2) for every e, even as the fold pair
          (two interior extrema at e>0) annihilates into a monotone curve (e<=0).
          The detector fires the same on both sides of the event it exists to find.
  Leg C — FALSE NEGATIVE: the genuine cusp germ x^3, sampled OFF-center, reads
          `accept` (the exact center-c2=0 requirement is brittle to sampling).

Control: a parabola correctly `accept`s and the demo cusp `structural-zero`s, so
the detector is not trivially stuck.

Run:
  python scripts/h2_cusp_detector_falsifier.py
  python scripts/h2_cusp_detector_falsifier.py --json
  python -m pytest scripts/test_h2_cusp_detector_falsifier.py -q
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction

import cusp_detector as cd
from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


def _c2(receipt):
    return [cd.frac_str(v) for v in receipt.c2]


def _interior_extrema(scores) -> int:
    """Count interior extrema = sign changes of consecutive first differences.
    2 = a fold pair (max then min); 0 = monotone (folds annihilated)."""
    diffs = [scores[i + 1] - scores[i] for i in range(len(scores) - 1)]
    changes = 0
    for i in range(len(diffs) - 1):
        a, b = diffs[i], diffs[i + 1]
        if (a < 0 < b) or (b < 0 < a):
            changes += 1
    return changes


def leg_A_false_positive() -> dict:
    """A monotone, fold-free saturation curve is flagged as a cusp."""
    scores = [-5, -3, 0, 3, 5]  # monotone, slopes 2,3,3,2 (gentle S); zero interior extrema
    r = cd.make_cusp_receipt([(x, s) for x, s in zip((-2, -1, 0, 1, 2), scores)])
    return {
        "name": "A_false_positive_monotone_S_curve",
        "scores": scores,
        "interior_extrema": _interior_extrema([Fraction(s) for s in scores]),
        "verdict": r.verdict,
        "verifies": cd.verify_cusp_receipt(r),
        # Fires iff a fold-FREE (0 interior extrema), verifying curve is called a cusp.
        "fires": (r.verdict == STRUCTURAL_ZERO
                  and cd.verify_cusp_receipt(r)
                  and _interior_extrema([Fraction(s) for s in scores]) == 0),
    }


def leg_B_annihilation_blind() -> dict:
    """x^3 - e*x: the detector verdict is invariant as the fold pair annihilates."""
    xs = (-2, -1, 0, 1, 2)
    rows = []
    for e in (3, 1, 0, -1, -3):
        scores = [Fraction(x) ** 3 - e * x for x in xs]
        r = cd.make_cusp_receipt([(x, s) for x, s in zip(xs, scores)])
        rows.append({"e": e, "verdict": r.verdict, "c2": _c2(r),
                     "interior_extrema": _interior_extrema(scores)})
    verdicts = {row["verdict"] for row in rows}
    c2s = {tuple(row["c2"]) for row in rows}
    extrema = {row["e"]: row["interior_extrema"] for row in rows}
    return {
        "name": "B_annihilation_blind",
        "rows": rows,
        "extrema_by_e": extrema,
        "verdict_invariant": len(verdicts) == 1,
        "c2_invariant": len(c2s) == 1,
        # Fires iff the verdict is constant (single value) across e WHILE the fold
        # pair actually annihilates: e>0 has 2 interior extrema, e<=0 has 0.
        "fires": (len(verdicts) == 1
                  and verdicts == {STRUCTURAL_ZERO}
                  and extrema[3] == 2 and extrema[0] == 0 and extrema[-3] == 0),
    }


def leg_C_false_negative() -> dict:
    """The genuine cusp germ x^3, sampled off-center, is missed (accept)."""
    xs = [Fraction(2 * i - 3, 2) for i in range(5)]  # -1.5, -0.5, 0.5, 1.5, 2.5 (even, off-center)
    r = cd.make_cusp_receipt([(x, x ** 3) for x in xs])
    return {
        "name": "C_false_negative_offcenter_cusp",
        "xs": [cd.frac_str(x) for x in xs],
        "verdict": r.verdict,
        "verifies": cd.verify_cusp_receipt(r),
        # Fires iff a genuine cusp germ reads accept (missed).
        "fires": r.verdict == ACCEPT and cd.verify_cusp_receipt(r),
    }


def control_detector_not_stuck() -> dict:
    """Sanity: parabola accepts, demo cusp structural-zeros (detector still discriminates)."""
    para = cd.make_cusp_receipt([(-2, 4), (-1, 1), (0, 0), (1, 1), (2, 4)])
    cusp = cd.demo_cusp_receipt()
    return {
        "name": "control_detector_not_stuck",
        "parabola_verdict": para.verdict,
        "demo_cusp_verdict": cusp.verdict,
        "holds": para.verdict == ACCEPT and cusp.verdict == STRUCTURAL_ZERO,
    }


def run() -> dict:
    a, b, c = leg_A_false_positive(), leg_B_annihilation_blind(), leg_C_false_negative()
    ctrl = control_detector_not_stuck()
    return {
        "leg_A": a, "leg_B": b, "leg_C": c, "control": ctrl,
        "falsifier_fires": a["fires"] and b["fires"] and c["fires"],
        "control_holds": ctrl["holds"],
    }


def format_report(r: dict) -> str:
    a, b, c, ctrl = r["leg_A"], r["leg_B"], r["leg_C"], r["control"]
    lines = [
        "H-II FALSIFIER — Whitney A3 cusp detector",
        "",
        f"[A] false positive — monotone fold-free S-curve {a['scores']} "
        f"(interior_extrema={a['interior_extrema']})",
        f"    verdict={a['verdict']} verifies={a['verifies']}  FIRES={a['fires']}",
        "",
        "[B] annihilation-blind — x^3 - e*x (verdict invariant while the fold pair dies):",
    ]
    for row in b["rows"]:
        lines.append(f"    e={row['e']:+d}  verdict={row['verdict']:15s} c2={row['c2']} "
                     f"interior_extrema={row['interior_extrema']}")
    lines += [
        f"    verdict_invariant={b['verdict_invariant']} c2_invariant={b['c2_invariant']}  FIRES={b['fires']}",
        "",
        f"[C] false negative — cusp germ x^3 sampled off-center: "
        f"verdict={c['verdict']} verifies={c['verifies']}  FIRES={c['fires']}",
        "",
        f"[control] parabola={ctrl['parabola_verdict']} demo_cusp={ctrl['demo_cusp_verdict']}  "
        f"HOLDS={ctrl['holds']}",
        "",
        f"VERDICT: falsifier_fires={r['falsifier_fires']}  control_holds={r['control_holds']}",
    ]
    return "\n".join(lines)


def main(argv=None) -> dict:
    parser = argparse.ArgumentParser(description="Run the H-II cusp-detector falsifier.")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    result = run()
    print(json.dumps(result, indent=2, sort_keys=True) if args.json else format_report(result))
    return result


if __name__ == "__main__":
    main()
