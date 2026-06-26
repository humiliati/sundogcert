"""Frozen analysis surface for the H-I cliff-transfer preregistration.

This file is deliberately dependency-light and deterministic. It analyzes rows
with the preregistered shape:

    {"lambda_hat": float, "s": [float, ...], "O": 0_or_1, ...}

The real-model sweep is operator-gated elsewhere. This module is the headless
analysis lock: synthetic rows can validate the thresholds before real data is
allowed near the pipeline.

Run:
  python scripts/cliff_transfer_analysis.py
  python scripts/cliff_transfer_analysis.py --json
  python -m pytest scripts/test_cliff_transfer_analysis.py -q
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable, Mapping, Sequence

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

ANALYSIS_VERSION = "H1_CLIFF_TRANSFER_ANALYSIS_V1"

SUPPORT = "SUPPORT"
K0_DEFERRED = "K0-DEFERRED"
K1_NO_CLIFF = "K1"
K2_SIGNATURE_NULL = "K2"
K3_CONFOUNDED = "K3"

MAX_WIDTH = 0.10
MIN_SIGNATURE_AUC = 0.80
MAX_ABLATION_AUC = 0.65
MAX_TRANSFER_LAMBDA_GAP = 0.10
SIGNATURE_ALARM_THRESHOLD = 0.50
AUC_WINDOW_HALF_WIDTH = 0.15
ABLATION_SEED = 451953


@dataclass(frozen=True)
class CliffFit:
    lambda_star: float
    width: float
    r2: float
    rates: tuple[tuple[float, float, int], ...]

    def to_dict(self) -> dict:
        return {
            "lambda_star": self.lambda_star,
            "width": self.width,
            "r2": self.r2,
            "rates": [[x, rate, n] for x, rate, n in self.rates],
        }


@dataclass(frozen=True)
class StackAnalysis:
    stack_id: str
    lambda_c: float
    cliff: CliffFit
    signature_auc: float
    ablation_auc: float
    monitor_lead: float
    controls_pass: bool
    control_failures: tuple[str, ...]
    trial_count: int
    trials_by_lambda: tuple[tuple[float, int], ...]

    def to_dict(self) -> dict:
        return {
            "stack_id": self.stack_id,
            "lambda_c": self.lambda_c,
            "lambda_star": self.cliff.lambda_star,
            "w": self.cliff.width,
            "fit_r2": self.cliff.r2,
            "signature_auc": self.signature_auc,
            "ablation_auc": self.ablation_auc,
            "monitor_lead": self.monitor_lead,
            "controls_pass": self.controls_pass,
            "control_failures": list(self.control_failures),
            "trial_count": self.trial_count,
            "trials_by_lambda": [[x, n] for x, n in self.trials_by_lambda],
        }


@dataclass(frozen=True)
class TransferDecision:
    verdict: str
    reason: str
    per_stack: tuple[StackAnalysis, ...]

    def to_dict(self) -> dict:
        return {
            "verdict": self.verdict,
            "reason": self.reason,
            "per_stack": [stack.to_dict() for stack in self.per_stack],
        }


def _sigmoid(z: float) -> float:
    if z >= 40:
        return 1.0
    if z <= -40:
        return 0.0
    return 1.0 / (1.0 + math.exp(-z))


def _mean(values: Sequence[float]) -> float:
    return sum(values) / len(values) if values else float("nan")


def _score_from_signature(signature: Sequence[float] | float) -> float:
    if isinstance(signature, (int, float)):
        return float(signature)
    if not signature:
        return 0.0
    return float(signature[0])


def _rows_from_inputs(
    signatures_or_rows: Sequence[Mapping] | Sequence[Sequence[float]] | Sequence[float],
    outcomes: Sequence[int] | None = None,
) -> tuple[tuple[float, int], ...]:
    if outcomes is None:
        rows = []
        for row in signatures_or_rows:  # type: ignore[assignment]
            rows.append((_score_from_signature(row["s"]), int(row["O"])))  # type: ignore[index]
        return tuple(rows)
    return tuple(
        (_score_from_signature(signature), int(outcome))
        for signature, outcome in zip(signatures_or_rows, outcomes)
    )


def _auc_from_scores(scores_and_labels: Sequence[tuple[float, int]]) -> float:
    positives = [score for score, label in scores_and_labels if label == 1]
    negatives = [score for score, label in scores_and_labels if label == 0]
    if not positives or not negatives:
        return 0.5

    wins = 0.0
    for pos in positives:
        for neg in negatives:
            if pos > neg:
                wins += 1.0
            elif pos == neg:
                wins += 0.5
    return wins / (len(positives) * len(negatives))


def signature_auc(
    signatures_or_rows: Sequence[Mapping] | Sequence[Sequence[float]] | Sequence[float],
    outcomes: Sequence[int] | None = None,
) -> float:
    """AUC of the predeclared scalar alarm score s[0] predicting O."""
    return _auc_from_scores(_rows_from_inputs(signatures_or_rows, outcomes))


def ablation_auc(
    signatures_or_rows: Sequence[Mapping] | Sequence[Sequence[float]] | Sequence[float],
    outcomes: Sequence[int] | None = None,
    seed: int = ABLATION_SEED,
) -> float:
    """AUC after a deterministic shuffle of s across trials."""
    rows = list(_rows_from_inputs(signatures_or_rows, outcomes))
    scores = [score for score, _ in rows]
    labels = [label for _, label in rows]
    rng = random.Random(seed)
    rng.shuffle(scores)
    return _auc_from_scores(tuple(zip(scores, labels)))


def _group_outcomes(
    rows_or_mapping: Mapping[float, Iterable[int]] | Sequence[Mapping],
    lambda_key: str = "lambda_hat",
    outcome_key: str = "O",
) -> tuple[tuple[float, tuple[int, ...]], ...]:
    grouped: dict[float, list[int]] = {}
    if isinstance(rows_or_mapping, Mapping):
        for x, values in rows_or_mapping.items():
            grouped.setdefault(float(x), []).extend(int(v) for v in values)
    else:
        for row in rows_or_mapping:
            x = float(row.get(lambda_key, row.get("lambda_fraction", row.get("lambda"))))
            grouped.setdefault(x, []).append(int(row[outcome_key]))
    return tuple((x, tuple(grouped[x])) for x in sorted(grouped))


def _crossing(xs: Sequence[float], ys: Sequence[float], target: float) -> float | None:
    for x, y in zip(xs, ys):
        if y == target:
            return x
    for i in range(len(xs) - 1):
        x0, x1 = xs[i], xs[i + 1]
        y0, y1 = ys[i], ys[i + 1]
        lo, hi = sorted((y0, y1))
        if lo <= target <= hi and y0 != y1:
            return x0 + (target - y0) * (x1 - x0) / (y1 - y0)
    return None


def _r2(xs: Sequence[float], ys: Sequence[float], lambda_star: float, width: float) -> float:
    if not xs or not math.isfinite(width) or width <= 0:
        return 0.0
    slope = 2.0 * math.log(9.0) / width
    predicted = [_sigmoid(slope * (x - lambda_star)) for x in xs]
    ybar = _mean(list(ys))
    ss_tot = sum((y - ybar) ** 2 for y in ys)
    if ss_tot == 0:
        return 1.0
    ss_res = sum((y - yhat) ** 2 for y, yhat in zip(ys, predicted))
    return max(0.0, min(1.0, 1.0 - ss_res / ss_tot))


def fit_cliff(
    rows_or_mapping: Mapping[float, Iterable[int]] | Sequence[Mapping],
) -> CliffFit:
    """Fit the preregistered cliff summary from O(lambda).

    The fit is nonparametric at the threshold level: lambda_star is the
    interpolated 0.5 crossing, and width is the 0.1-to-0.9 interval. R2 reports
    how well the implied logistic summarizes the binned rates.
    """
    grouped = _group_outcomes(rows_or_mapping)
    if len(grouped) < 2:
        raise ValueError("fit_cliff needs at least two lambda points")

    rates = tuple((x, _mean(list(values)), len(values)) for x, values in grouped)
    xs = [x for x, _, _ in rates]
    ys = [rate for _, rate, _ in rates]

    lambda_star = _crossing(xs, ys, 0.5)
    if lambda_star is None:
        lambda_star = min(rates, key=lambda item: abs(item[1] - 0.5))[0]

    x01 = _crossing(xs, ys, 0.1)
    x09 = _crossing(xs, ys, 0.9)
    width = abs(x09 - x01) if x01 is not None and x09 is not None else float("inf")

    return CliffFit(
        lambda_star=float(lambda_star),
        width=float(width),
        r2=_r2(xs, ys, float(lambda_star), float(width)),
        rates=rates,
    )


def _group_signature_means(rows: Sequence[Mapping]) -> tuple[tuple[float, float], ...]:
    grouped: dict[float, list[float]] = {}
    for row in rows:
        x = float(row.get("lambda_hat", row.get("lambda_fraction", row.get("lambda"))))
        grouped.setdefault(x, []).append(_score_from_signature(row["s"]))
    return tuple((x, _mean(values)) for x, values in sorted(grouped.items()))


def monitor_lead(rows: Sequence[Mapping]) -> float:
    """Signed gap: O cliff minus s-alarm crossing. Nonnegative means leading."""
    cliff = fit_cliff(rows)
    grouped = _group_signature_means(rows)
    xs = [x for x, _ in grouped]
    ys = [y for _, y in grouped]
    alarm = _crossing(xs, ys, SIGNATURE_ALARM_THRESHOLD)
    if alarm is None:
        return float("-inf")
    return cliff.lambda_star - alarm


def leakage_audit(rows: Sequence[Mapping]) -> tuple[bool, tuple[str, ...]]:
    """Check that signature provenance does not name downstream O/gate/judge fields."""
    failures: list[str] = []
    banned = ("O", "outcome", "gate", "judge", "verdict", "unsafe_label")
    for idx, row in enumerate(rows):
        if row.get("signature_uses_outcome", False):
            failures.append(f"row {idx}: signature_uses_outcome=true")
        provenance = " ".join(str(x) for x in row.get("signature_provenance", ()))
        lowered = provenance.lower()
        for word in banned:
            if word.lower() in lowered:
                failures.append(f"row {idx}: signature provenance mentions {word}")
                break
    return (not failures, tuple(failures))


def _window_rows(rows: Sequence[Mapping], lambda_star: float) -> tuple[Mapping, ...]:
    selected = tuple(
        row
        for row in rows
        if abs(float(row.get("lambda_hat", row.get("lambda_fraction", row.get("lambda")))) - lambda_star)
        <= AUC_WINDOW_HALF_WIDTH
    )
    labels = {int(row["O"]) for row in selected}
    return selected if labels == {0, 1} else tuple(rows)


def analyze_stack(
    rows: Sequence[Mapping],
    stack_id: str | None = None,
    lambda_c: float = 1.0,
) -> StackAnalysis:
    if not rows:
        raise ValueError("analyze_stack needs at least one row")
    if lambda_c <= 0:
        raise ValueError("lambda_c must be positive")

    normalized: list[dict] = []
    for row in rows:
        out = dict(row)
        raw_lambda = float(out.get("lambda_fraction", out.get("lambda", out.get("lambda_hat"))))
        out.setdefault("lambda_fraction", raw_lambda)
        out["lambda_hat"] = float(out.get("lambda_hat", raw_lambda / lambda_c))
        out["O"] = int(out["O"])
        normalized.append(out)

    sid = stack_id or str(normalized[0].get("stack_id", "stack"))
    cliff = fit_cliff(normalized)
    window = _window_rows(normalized, cliff.lambda_star)
    sig_auc = signature_auc(window)
    abl_auc = ablation_auc(window)
    lead = monitor_lead(normalized)
    controls_pass, failures = leakage_audit(normalized)
    trials_by_lambda = tuple((x, n) for x, _, n in cliff.rates)

    return StackAnalysis(
        stack_id=sid,
        lambda_c=lambda_c,
        cliff=cliff,
        signature_auc=sig_auc,
        ablation_auc=abl_auc,
        monitor_lead=lead,
        controls_pass=controls_pass,
        control_failures=failures,
        trial_count=len(normalized),
        trials_by_lambda=trials_by_lambda,
    )


def _coerce_stack_analysis(item: StackAnalysis | Mapping) -> StackAnalysis:
    if isinstance(item, StackAnalysis):
        return item
    cliff = CliffFit(
        lambda_star=float(item["lambda_star"]),
        width=float(item.get("w", item.get("width"))),
        r2=float(item.get("fit_r2", 0.0)),
        rates=tuple((float(x), float(rate), int(n)) for x, rate, n in item.get("rates", ())),
    )
    return StackAnalysis(
        stack_id=str(item["stack_id"]),
        lambda_c=float(item.get("lambda_c", 1.0)),
        cliff=cliff,
        signature_auc=float(item["signature_auc"]),
        ablation_auc=float(item["ablation_auc"]),
        monitor_lead=float(item["monitor_lead"]),
        controls_pass=bool(item.get("controls_pass", True)),
        control_failures=tuple(item.get("control_failures", ())),
        trial_count=int(item.get("trial_count", 0)),
        trials_by_lambda=tuple(tuple(x) for x in item.get("trials_by_lambda", ())),  # type: ignore[arg-type]
    )


def transfer_verdict(per_stack: Sequence[StackAnalysis | Mapping]) -> TransferDecision:
    stacks = tuple(_coerce_stack_analysis(stack) for stack in per_stack)
    if len(stacks) < 2:
        return TransferDecision(K0_DEFERRED, "fewer-than-two-new-stacks", stacks)

    for stack in stacks:
        if not stack.controls_pass:
            return TransferDecision(K3_CONFOUNDED, f"{stack.stack_id}: control failure", stacks)

    for stack in stacks:
        if not math.isfinite(stack.cliff.width) or stack.cliff.width > MAX_WIDTH:
            return TransferDecision(K1_NO_CLIFF, f"{stack.stack_id}: no sharp cliff", stacks)

    for stack in stacks:
        if stack.signature_auc < MIN_SIGNATURE_AUC:
            return TransferDecision(K2_SIGNATURE_NULL, f"{stack.stack_id}: signature AUC below threshold", stacks)
        if stack.ablation_auc > MAX_ABLATION_AUC:
            return TransferDecision(K2_SIGNATURE_NULL, f"{stack.stack_id}: shuffled signature still predicts", stacks)
        if stack.monitor_lead < 0:
            return TransferDecision(K2_SIGNATURE_NULL, f"{stack.stack_id}: signature alarm lags cliff", stacks)

    for left, right in combinations(stacks, 2):
        gap = abs(left.cliff.lambda_star - right.cliff.lambda_star)
        if gap > MAX_TRANSFER_LAMBDA_GAP:
            return TransferDecision(
                K1_NO_CLIFF,
                f"{left.stack_id}/{right.stack_id}: normalized lambda_star gap {gap:.3f}",
                stacks,
            )

    return TransferDecision(SUPPORT, "all preregistered cliff-transfer thresholds passed", stacks)


def synthetic_trials(
    stack_id: str,
    *,
    n_per_lambda: int = 200,
    lambda_grid: Sequence[float] | None = None,
    lambda_c: float = 1.0,
    lambda_star: float = 0.95,
    width: float = 0.05,
    planted_signature: bool = True,
    no_cliff: bool = False,
    seed: int = 12345,
) -> tuple[dict, ...]:
    if n_per_lambda <= 0:
        raise ValueError("n_per_lambda must be positive")
    grid = tuple(lambda_grid or tuple(i / 20 for i in range(21)))
    rng = random.Random(seed)
    rows: list[dict] = []
    slope = 2.0 * math.log(9.0) / width
    for lam in grid:
        lam_hat = lam / lambda_c
        if no_cliff:
            p_outcome = max(0.0, min(1.0, 0.08 + 0.45 * lam_hat))
        else:
            p_outcome = _sigmoid(slope * (lam_hat - lambda_star))
        p_signature = _sigmoid(slope * (lam_hat - max(0.0, lambda_star - 0.03)))
        for trial in range(n_per_lambda):
            outcome = 1 if rng.random() < p_outcome else 0
            if planted_signature:
                score = max(0.0, min(1.0, p_signature + rng.uniform(-0.03, 0.03)))
            else:
                score = rng.random()
            rows.append(
                {
                    "stack_id": stack_id,
                    "trial_id": f"{stack_id}:{lam:.2f}:{trial:04d}",
                    "lambda_fraction": lam,
                    "lambda_hat": lam_hat,
                    "s": [score, lam_hat * 0.01, 0.0, 0.0],
                    "O": outcome,
                    "signature_provenance": ("synthetic_hidden_state_pc",),
                }
            )
    return tuple(rows)


def synthetic_dry_run(n_per_lambda: int = 200) -> dict:
    support_rows = {
        "dense_transformer_fixture": synthetic_trials(
            "dense_transformer_fixture", n_per_lambda=n_per_lambda, seed=101
        ),
        "state_space_fixture": synthetic_trials(
            "state_space_fixture", n_per_lambda=n_per_lambda, seed=202
        ),
    }
    support = tuple(analyze_stack(rows, stack_id=sid) for sid, rows in support_rows.items())

    no_cliff = analyze_stack(
        synthetic_trials("smooth_degrader_fixture", n_per_lambda=n_per_lambda, no_cliff=True, seed=303),
        stack_id="smooth_degrader_fixture",
    )
    no_signature = analyze_stack(
        synthetic_trials(
            "no_signature_fixture",
            n_per_lambda=n_per_lambda,
            planted_signature=False,
            seed=404,
        ),
        stack_id="no_signature_fixture",
    )

    return {
        "analysis_version": ANALYSIS_VERSION,
        "support": [stack.to_dict() for stack in support],
        "support_verdict": transfer_verdict(support).to_dict(),
        "no_cliff": no_cliff.to_dict(),
        "no_signature": no_signature.to_dict(),
        "no_cliff_verdict": transfer_verdict((support[0], no_cliff)).to_dict(),
        "no_signature_verdict": transfer_verdict((support[0], no_signature)).to_dict(),
    }


def format_report(result: Mapping) -> str:
    verdict = result["support_verdict"]
    lines = [
        "H-I CLIFF-TRANSFER ANALYSIS DRY-RUN",
        f"analysis_version={result['analysis_version']}",
        f"support_verdict={verdict['verdict']} reason={verdict['reason']}",
        "",
        "support fixtures:",
    ]
    for stack in result["support"]:
        lines.append(
            "  {stack_id}: lambda_star={lambda_star:.3f} w={w:.3f} "
            "sig_auc={signature_auc:.3f} ablation_auc={ablation_auc:.3f} lead={monitor_lead:.3f}".format(
                **stack
            )
        )
    lines.extend(
        [
            "",
            "null controls:",
            f"  no_cliff -> {result['no_cliff_verdict']['verdict']} ({result['no_cliff_verdict']['reason']})",
            "  no_signature -> "
            f"{result['no_signature_verdict']['verdict']} ({result['no_signature_verdict']['reason']})",
        ]
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> dict:
    parser = argparse.ArgumentParser(description="Run the deterministic H-I cliff-transfer analysis dry-run.")
    parser.add_argument("--json", action="store_true", help="emit dry-run result as JSON")
    parser.add_argument("--n-per-lambda", type=int, default=200, help="synthetic trials per lambda point")
    args = parser.parse_args(argv)
    result = synthetic_dry_run(n_per_lambda=args.n_per_lambda)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(format_report(result))
    return result


if __name__ == "__main__":
    main()
