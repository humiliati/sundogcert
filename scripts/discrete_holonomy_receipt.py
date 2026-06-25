"""Toy discrete-holonomy receipts for finite trace loops.

This is the executable companion to `Sundogcert.DiscreteHolonomy`. The Lean
theorem proves that pure gauge contributions telescope, and therefore close to
zero around a finite loop. This script turns that shape into a tiny public
receipt:

* `accept`: the loop is closed and the observed circulation is zero;
* `structural-zero`: the loop is closed, but observed circulation is nonzero;
* `quarantine`: the submitted path/potential/edge data is malformed.

The script uses integer potentials and edge values only. It does not claim that
any model attention trace has been faithfully mapped into this representation.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace

from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO


@dataclass(frozen=True)
class DiscreteHolonomyReceipt:
    path: tuple[str, ...]
    potentials: tuple[tuple[str, int], ...]
    edge_values: tuple[int, ...]
    gauge_steps: tuple[int, ...]
    endpoint_diff: int | None
    gauge_circulation: int | None
    observed_circulation: int | None
    residual_circulation: int | None
    verdict: str
    reason: str
    digest: str = ""

    def payload(self) -> dict:
        return {
            "path": list(self.path),
            "potentials": [[vertex, value] for vertex, value in self.potentials],
            "edge_values": list(self.edge_values),
            "gauge_steps": list(self.gauge_steps),
            "endpoint_diff": self.endpoint_diff,
            "gauge_circulation": self.gauge_circulation,
            "observed_circulation": self.observed_circulation,
            "residual_circulation": self.residual_circulation,
            "verdict": self.verdict,
            "reason": self.reason,
        }

    def computed_digest(self) -> str:
        encoded = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    def with_digest(self) -> "DiscreteHolonomyReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def normalize_potentials(potentials: dict[str, int]) -> tuple[tuple[str, int], ...]:
    return tuple(sorted(potentials.items()))


def make_holonomy_receipt(
    path: list[str] | tuple[str, ...], potentials: dict[str, int], edge_values: list[int] | tuple[int, ...]
) -> DiscreteHolonomyReceipt:
    path_tuple = tuple(path)
    potential_items = normalize_potentials(potentials)
    edge_tuple = tuple(edge_values)

    def quarantine(reason: str) -> DiscreteHolonomyReceipt:
        return DiscreteHolonomyReceipt(
            path=path_tuple,
            potentials=potential_items,
            edge_values=edge_tuple,
            gauge_steps=(),
            endpoint_diff=None,
            gauge_circulation=None,
            observed_circulation=None,
            residual_circulation=None,
            verdict=QUARANTINE,
            reason=reason,
        ).with_digest()

    if len(path_tuple) < 2:
        return quarantine("path-too-short")
    if len(edge_tuple) != len(path_tuple) - 1:
        return quarantine("edge-count-mismatch")
    if any(vertex not in potentials for vertex in path_tuple):
        return quarantine("missing-potential")
    if path_tuple[0] != path_tuple[-1]:
        return quarantine("not-closed-loop")

    gauge_steps = tuple(potentials[path_tuple[i + 1]] - potentials[path_tuple[i]]
                        for i in range(len(path_tuple) - 1))
    endpoint_diff = potentials[path_tuple[-1]] - potentials[path_tuple[0]]
    gauge_circulation = sum(gauge_steps)
    observed_circulation = sum(edge_tuple)
    residual_circulation = observed_circulation - endpoint_diff

    if gauge_circulation != endpoint_diff:
        verdict = QUARANTINE
        reason = "gauge-telescope-failed"
    elif observed_circulation == 0:
        verdict = ACCEPT
        reason = "closed-loop-zero"
    else:
        verdict = STRUCTURAL_ZERO
        reason = "nonzero-loop-residual"

    return DiscreteHolonomyReceipt(
        path=path_tuple,
        potentials=potential_items,
        edge_values=edge_tuple,
        gauge_steps=gauge_steps,
        endpoint_diff=endpoint_diff,
        gauge_circulation=gauge_circulation,
        observed_circulation=observed_circulation,
        residual_circulation=residual_circulation,
        verdict=verdict,
        reason=reason,
    ).with_digest()


def verify_holonomy_receipt(
    receipt: DiscreteHolonomyReceipt,
    path: list[str] | tuple[str, ...] | None = None,
    potentials: dict[str, int] | None = None,
    edge_values: list[int] | tuple[int, ...] | None = None,
) -> bool:
    if not receipt.digest_matches():
        return False
    if receipt.verdict not in (ACCEPT, STRUCTURAL_ZERO, QUARANTINE):
        return False

    if potentials is None:
        potentials = dict(receipt.potentials)
    if path is None:
        path = receipt.path
    if edge_values is None:
        edge_values = receipt.edge_values

    expected = make_holonomy_receipt(path, potentials, edge_values)
    return receipt.payload() == expected.payload()


def demo_closed_zero_receipt() -> DiscreteHolonomyReceipt:
    path = ("root", "grep", "rank", "root")
    potentials = {"root": 2, "grep": 5, "rank": 11}
    return make_holonomy_receipt(path, potentials, edge_values=(3, 6, -9))


def demo_nonzero_residual_receipt() -> DiscreteHolonomyReceipt:
    path = ("root", "grep", "rank", "root")
    potentials = {"root": 2, "grep": 5, "rank": 11}
    return make_holonomy_receipt(path, potentials, edge_values=(3, 6, -7))
