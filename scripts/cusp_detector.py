"""Sampled cusp-detector receipts for context-decay experiments.

This is Step 5 of AGENTIC_TRACE_HYPOTHESES.md: specify the detector and its
falsification surface before any Lean theorem or model-internals claim.

The detector is intentionally small and exact. It consumes five evenly spaced
score samples from a one-dimensional retrieval/regularization sweep and computes
finite differences:

* three second differences (`c2_left`, `c2_center`, `c2_right`);
* two local third differences (`c3_left`, `c3_right`).

A cusp-like signature is declared only when:

* the left and right second differences have opposite signs;
* both are large enough to clear `min_abs_c2`;
* the center second difference is within `max_abs_center_c2`;
* both local third differences are bounded by `max_abs_c3`.

Outcomes:

* `accept`: no cusp signature is present;
* `structural-zero`: the sampled cusp signature is present, so the context
  window should be decayed/quarantined by a caller;
* `quarantine`: the receipt is malformed or outside the detector's declared
  numerical envelope.

This is not a proof that any vector database or model memory forms a Whitney A3
cusp. It is the small, public detector shape that such a claim would have to
survive.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Iterable

from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO


def as_fraction(value: int | str | Fraction) -> Fraction:
    if isinstance(value, Fraction):
        return value
    return Fraction(value)


def frac_str(value: Fraction | None) -> str | None:
    if value is None:
        return None
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


@dataclass(frozen=True)
class JetSample:
    x: Fraction
    score: Fraction

    def to_payload(self) -> list[str]:
        return [frac_str(self.x) or "0", frac_str(self.score) or "0"]


@dataclass(frozen=True)
class CuspThresholds:
    min_abs_c2: Fraction = Fraction(1)
    max_abs_center_c2: Fraction = Fraction(0)
    max_abs_c3: Fraction = Fraction(6)

    def __post_init__(self) -> None:
        object.__setattr__(self, "min_abs_c2", as_fraction(self.min_abs_c2))
        object.__setattr__(self, "max_abs_center_c2", as_fraction(self.max_abs_center_c2))
        object.__setattr__(self, "max_abs_c3", as_fraction(self.max_abs_c3))

    def to_payload(self) -> dict:
        return {
            "min_abs_c2": frac_str(self.min_abs_c2),
            "max_abs_center_c2": frac_str(self.max_abs_center_c2),
            "max_abs_c3": frac_str(self.max_abs_c3),
        }


@dataclass(frozen=True)
class CuspReceipt:
    samples: tuple[JetSample, ...]
    thresholds: CuspThresholds
    c2: tuple[Fraction, ...]
    c3: tuple[Fraction, ...]
    verdict: str
    reason: str
    digest: str = ""

    def payload(self) -> dict:
        return {
            "samples": [sample.to_payload() for sample in self.samples],
            "thresholds": self.thresholds.to_payload(),
            "c2": [frac_str(value) for value in self.c2],
            "c3": [frac_str(value) for value in self.c3],
            "verdict": self.verdict,
            "reason": self.reason,
        }

    def computed_digest(self) -> str:
        encoded = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def with_digest(self) -> "CuspReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def make_samples(values: Iterable[tuple[int | str | Fraction, int | str | Fraction]]) -> tuple[JetSample, ...]:
    return tuple(JetSample(as_fraction(x), as_fraction(score)) for x, score in values)


def _quarantine(samples: tuple[JetSample, ...], thresholds: CuspThresholds, reason: str) -> CuspReceipt:
    return CuspReceipt(
        samples=samples,
        thresholds=thresholds,
        c2=(),
        c3=(),
        verdict=QUARANTINE,
        reason=reason,
    ).with_digest()


def _even_spacing(samples: tuple[JetSample, ...]) -> bool:
    step = samples[1].x - samples[0].x
    if step == 0:
        return False
    return all(samples[i + 1].x - samples[i].x == step for i in range(len(samples) - 1))


def second_differences(scores: tuple[Fraction, ...]) -> tuple[Fraction, Fraction, Fraction]:
    return tuple(scores[i + 2] - 2 * scores[i + 1] + scores[i] for i in range(3))  # type: ignore[return-value]


def third_differences(c2: tuple[Fraction, Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return c2[1] - c2[0], c2[2] - c2[1]


def opposite_sign(left: Fraction, right: Fraction) -> bool:
    return (left < 0 < right) or (right < 0 < left)


def make_cusp_receipt(
    samples: Iterable[JetSample] | Iterable[tuple[int | str | Fraction, int | str | Fraction]],
    thresholds: CuspThresholds | None = None,
) -> CuspReceipt:
    thresholds = thresholds or CuspThresholds()
    sample_tuple = tuple(samples)
    if sample_tuple and not isinstance(sample_tuple[0], JetSample):
        sample_tuple = make_samples(sample_tuple)  # type: ignore[arg-type]

    if len(sample_tuple) != 5:
        return _quarantine(sample_tuple, thresholds, "sample-count-mismatch")  # type: ignore[arg-type]
    sample_tuple = sample_tuple  # type: ignore[assignment]
    if not _even_spacing(sample_tuple):
        return _quarantine(sample_tuple, thresholds, "samples-not-evenly-spaced")
    if thresholds.min_abs_c2 < 0 or thresholds.max_abs_center_c2 < 0 or thresholds.max_abs_c3 < 0:
        return _quarantine(sample_tuple, thresholds, "negative-threshold")

    scores = tuple(sample.score for sample in sample_tuple)
    c2 = second_differences(scores)
    c3 = third_differences(c2)

    left, center, right = c2
    sign_change = opposite_sign(left, right)
    clears_magnitude = abs(left) >= thresholds.min_abs_c2 and abs(right) >= thresholds.min_abs_c2
    center_near_zero = abs(center) <= thresholds.max_abs_center_c2
    third_bounded = max(abs(value) for value in c3) <= thresholds.max_abs_c3

    if sign_change and clears_magnitude and center_near_zero and not third_bounded:
        verdict = QUARANTINE
        reason = "third-bound-exceeded"
    elif sign_change and clears_magnitude and center_near_zero:
        verdict = STRUCTURAL_ZERO
        reason = "sampled-cusp-signature"
    else:
        verdict = ACCEPT
        reason = "no-sampled-cusp"

    return CuspReceipt(
        samples=sample_tuple,
        thresholds=thresholds,
        c2=c2,
        c3=c3,
        verdict=verdict,
        reason=reason,
    ).with_digest()


def verify_cusp_receipt(receipt: CuspReceipt) -> bool:
    if not receipt.digest_matches():
        return False
    if receipt.verdict not in (ACCEPT, STRUCTURAL_ZERO, QUARANTINE):
        return False
    expected = make_cusp_receipt(receipt.samples, receipt.thresholds)
    return receipt.payload() == expected.payload()


def demo_cusp_receipt() -> CuspReceipt:
    return make_cusp_receipt(((-2, -8), (-1, -1), (0, 0), (1, 1), (2, 8)))


def demo_smooth_receipt() -> CuspReceipt:
    return make_cusp_receipt(((-2, 4), (-1, 1), (0, 0), (1, 1), (2, 4)))
