"""Re-specified fold-pair / A3-cusp detector for H-II context decay.

The H-II falsifier (`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md`) showed the sampled
`cusp_detector` reads an INFLECTION (a `c2` sign-change), not the fold-pair
annihilation an A3 cusp is: it false-positives on monotone curves, is INVARIANT
across the canonical `x^3 - e*x` unfolding, and misses off-center germs. The defect
is structural — it inspects only the second difference of ONE 1-D jet.

This detector measures the right object:

  * the FIRST difference (slope) of each curve -> count INTERIOR EXTREMA = the number
    of FOLDS present (a monotone curve has 0, so it can never be a cusp); and
  * a TWO-PARAMETER FAMILY across the control/staleness parameter -> a fold-pair
    ANNIHILATION is a clean drop of the fold count by 2 between adjacent control
    values (the event a single jet cannot witness).

Caller contract: pass curves ordered by INCREASING control (e.g. decay / staleness /
regularization). A fold-pair annihilation is the fold count dropping by 2.

Outcomes:
  * structural-zero: a fold-pair annihilation occurs in the family (the retrieval
    geometry crossed the cusp) -> decay/quarantine the context;
  * accept: no annihilation (monotone throughout, or a stable / increasing fold count);
  * quarantine: malformed input -- fewer than two curves, a curve with < 5 evenly
    spaced samples, non-increasing control values, or an UNPAIRED fold-count change
    (odd, or |delta| > 2 between adjacent controls = the sweep is undersampled, so a
    clean single fold-pair event cannot be asserted).

Receipts are exact (`Fraction`) and re-verifiable, matching `cusp_detector`'s shape.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Iterable, Sequence

from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO
from cusp_detector import as_fraction, frac_str

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


@dataclass(frozen=True)
class FoldPairThresholds:
    min_slope: Fraction = Fraction(1)   # a turn counts as a fold only if a flank clears this
    min_samples: int = 5                # samples per curve (>=5 resolves a fold pair)

    def __post_init__(self) -> None:
        object.__setattr__(self, "min_slope", as_fraction(self.min_slope))

    def to_payload(self) -> dict:
        return {"min_slope": frac_str(self.min_slope), "min_samples": self.min_samples}


@dataclass(frozen=True)
class Curve:
    control: Fraction
    samples: tuple[tuple[Fraction, Fraction], ...]

    def to_payload(self) -> dict:
        return {"control": frac_str(self.control),
                "samples": [[frac_str(x), frac_str(s)] for x, s in self.samples]}


@dataclass(frozen=True)
class FoldPairReceipt:
    curves: tuple[Curve, ...]
    thresholds: FoldPairThresholds
    fold_counts: tuple[int, ...]
    annihilations: tuple[tuple[Fraction, Fraction], ...]
    verdict: str
    reason: str
    digest: str = ""

    def payload(self) -> dict:
        return {
            "curves": [c.to_payload() for c in self.curves],
            "thresholds": self.thresholds.to_payload(),
            "fold_counts": list(self.fold_counts),
            "annihilations": [[frac_str(a), frac_str(b)] for a, b in self.annihilations],
            "verdict": self.verdict,
            "reason": self.reason,
        }

    def computed_digest(self) -> str:
        encoded = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def with_digest(self) -> "FoldPairReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def make_curve(control, samples: Iterable[tuple]) -> Curve:
    return Curve(as_fraction(control),
                 tuple((as_fraction(x), as_fraction(s)) for x, s in samples))


def count_interior_extrema(scores: Sequence[Fraction], min_slope: Fraction) -> int:
    """Number of interior extrema = sign changes of consecutive first differences
    with a flank clearing `min_slope` (ignores flat/noise turns). This is the FOLD
    COUNT the c2-only detector never looked at."""
    diffs = [scores[i + 1] - scores[i] for i in range(len(scores) - 1)]
    count = 0
    for i in range(len(diffs) - 1):
        a, b = diffs[i], diffs[i + 1]
        opposite = (a < 0 < b) or (b < 0 < a)
        if opposite and max(abs(a), abs(b)) >= min_slope:
            count += 1
    return count


def _even_spacing(samples: tuple[tuple[Fraction, Fraction], ...]) -> bool:
    xs = [x for x, _ in samples]
    step = xs[1] - xs[0]
    if step == 0:
        return False
    return all(xs[i + 1] - xs[i] == step for i in range(len(xs) - 1))


def _quarantine(curves, thresholds, reason) -> FoldPairReceipt:
    return FoldPairReceipt(curves=tuple(curves), thresholds=thresholds, fold_counts=(),
                           annihilations=(), verdict=QUARANTINE, reason=reason).with_digest()


def make_foldpair_receipt(curves: Iterable[Curve | tuple],
                          thresholds: FoldPairThresholds | None = None) -> FoldPairReceipt:
    thresholds = thresholds or FoldPairThresholds()
    cs = []
    for c in curves:
        cs.append(c if isinstance(c, Curve) else make_curve(c[0], c[1]))
    cs = tuple(cs)

    if len(cs) < 2:
        return _quarantine(cs, thresholds, "need-at-least-two-curves")
    if thresholds.min_slope < 0 or thresholds.min_samples < 3:
        return _quarantine(cs, thresholds, "bad-thresholds")
    for c in cs:
        if len(c.samples) < thresholds.min_samples:
            return _quarantine(cs, thresholds, "too-few-samples")
        if not _even_spacing(c.samples):
            return _quarantine(cs, thresholds, "samples-not-evenly-spaced")
    if any(cs[i + 1].control <= cs[i].control for i in range(len(cs) - 1)):
        return _quarantine(cs, thresholds, "control-not-increasing")

    fold_counts = tuple(
        count_interior_extrema([s for _, s in c.samples], thresholds.min_slope) for c in cs
    )

    annihilations = []
    for i in range(len(fold_counts) - 1):
        delta = fold_counts[i] - fold_counts[i + 1]   # drop as control (staleness) increases
        if delta == 2:
            annihilations.append((cs[i].control, cs[i + 1].control))
        elif delta != 0 and (delta % 2 != 0 or abs(delta) > 2):
            # an unpaired extremum, or >1 fold pair between adjacent controls:
            # the control sweep is too coarse to assert a clean single annihilation.
            return _quarantine(cs, thresholds, "unpaired-or-undersampled-fold-change")

    if annihilations:
        verdict, reason = STRUCTURAL_ZERO, "fold-pair-annihilation"
    else:
        verdict, reason = ACCEPT, "no-fold-pair-annihilation"

    return FoldPairReceipt(curves=cs, thresholds=thresholds, fold_counts=fold_counts,
                           annihilations=tuple(annihilations), verdict=verdict,
                           reason=reason).with_digest()


def verify_foldpair_receipt(receipt: FoldPairReceipt) -> bool:
    if not receipt.digest_matches():
        return False
    if receipt.verdict not in (ACCEPT, STRUCTURAL_ZERO, QUARANTINE):
        return False
    expected = make_foldpair_receipt(receipt.curves, receipt.thresholds)
    return receipt.payload() == expected.payload()


# --------------------------------------------------------------- demo families ----

def _cubic_family(es, xs):
    return [make_curve(i, [(x, Fraction(x) ** 3 - e * x) for x in xs]) for i, e in enumerate(es)]


def demo_annihilation_receipt() -> FoldPairReceipt:
    """x^3 - e*x with e decreasing 3->0 (staleness increasing): fold pair dies."""
    return make_foldpair_receipt(_cubic_family((3, 2, 1, 0), (-2, -1, 0, 1, 2)))


def demo_monotone_receipt() -> FoldPairReceipt:
    """A family of monotone, fold-free curves: no annihilation."""
    return make_foldpair_receipt(
        [make_curve(i, [(x, k * x) for x in (-2, -1, 0, 1, 2)]) for i, k in enumerate((1, 2, 3))]
    )


def format_report(r: FoldPairReceipt) -> str:
    ann = ", ".join(f"({frac_str(a)}->{frac_str(b)})" for a, b in r.annihilations) or "none"
    return "\n".join([
        "FOLD-PAIR DETECTOR",
        f"  curves={len(r.curves)} fold_counts={list(r.fold_counts)}",
        f"  annihilations={ann}",
        f"  verdict={r.verdict} reason={r.reason} verifies={verify_foldpair_receipt(r)}",
    ])


def main(argv=None):
    parser = argparse.ArgumentParser(description="Re-specified fold-pair / A3-cusp detector.")
    parser.add_argument("--demo", choices=("annihilation", "monotone"), default="annihilation")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    r = demo_annihilation_receipt() if args.demo == "annihilation" else demo_monotone_receipt()
    print(json.dumps(r.to_dict(), indent=2) if args.json else format_report(r))
    return r


if __name__ == "__main__":
    main()
