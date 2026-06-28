"""Re-specified holonomy filter (the H-III fix): a Hodge-split hierarchy receipt.

The H-III falsifier (`AGENTIC_TRACE_H3_FALSIFIER_RESULT.md`) showed the loop-circulation
filter (`discrete_holonomy_receipt.py`) measures only the NON-CONSERVATIVE (curl) Hodge
component of the trace field. The instruction hierarchy lives in the CONSERVATIVE
(gradient / potential) component, which `Sundogcert.DiscreteHolonomy.closed_gauge_sum_zero`
proves contributes zero to every loop — so a gradient-encoded hijack is invisible (false
negative, leg A) and benign curl is flagged (false positive, leg B).

This receipt fixes it by splitting the field into its two components and keying the
INJECTION verdict on the right one:

  * gradient / hierarchy (the conservative part): check the potential ordering against a
    declared reference `must_dominate` (trusted node must out-rank untrusted) — this is
    the actual injection signal, and it is supplied externally (you cannot read the
    hierarchy off a loop; you must be told it, the H-III analog of H-I's decisive_indices);
  * curl / residual (the non-conservative part): the observed loop circulation. Reported
    for transparency, but benign asymmetric reasoning is NOT an attack, so it does not
    by itself halt.

Outcomes:
  * structural-zero (HALT): a `must_dominate` constraint is violated (a hierarchy hijack);
  * accept: hierarchy intact (regardless of curl residual — benign non-conservative
    reasoning is allowed);
  * quarantine: malformed data (short/open path, edge mismatch, missing potential,
    reference node absent, or the gauge telescope identity fails).

Integer potentials / edge values, exact, re-verifiable — matching
`discrete_holonomy_receipt`'s shape.
"""

from __future__ import annotations

import hashlib
import json
import sys
from dataclasses import dataclass, replace

from branch_budget_receipt import ACCEPT, QUARANTINE, STRUCTURAL_ZERO

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


@dataclass(frozen=True)
class HierarchyHolonomyReceipt:
    path: tuple[str, ...]
    potentials: tuple[tuple[str, int], ...]
    edge_values: tuple[int, ...]
    must_dominate: tuple[tuple[str, str], ...]
    gauge_steps: tuple[int, ...]
    endpoint_diff: int | None
    gauge_circulation: int | None
    observed_circulation: int | None       # the curl / residual component (reported)
    residual_circulation: int | None
    hierarchy_violations: tuple[tuple[str, str], ...]   # the gradient component (keyed)
    verdict: str
    reason: str
    digest: str = ""

    def payload(self) -> dict:
        return {
            "path": list(self.path),
            "potentials": [[v, p] for v, p in self.potentials],
            "edge_values": list(self.edge_values),
            "must_dominate": [[hi, lo] for hi, lo in self.must_dominate],
            "gauge_steps": list(self.gauge_steps),
            "endpoint_diff": self.endpoint_diff,
            "gauge_circulation": self.gauge_circulation,
            "observed_circulation": self.observed_circulation,
            "residual_circulation": self.residual_circulation,
            "hierarchy_violations": [[hi, lo] for hi, lo in self.hierarchy_violations],
            "verdict": self.verdict,
            "reason": self.reason,
        }

    def computed_digest(self) -> str:
        enc = json.dumps(self.payload(), sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(enc).hexdigest()

    def with_digest(self) -> "HierarchyHolonomyReceipt":
        return replace(self, digest=self.computed_digest())

    def digest_matches(self) -> bool:
        return self.digest == self.computed_digest()

    def to_dict(self) -> dict:
        out = self.payload()
        out["digest"] = self.digest
        return out


def _normalize_potentials(potentials: dict[str, int]) -> tuple[tuple[str, int], ...]:
    return tuple(sorted(potentials.items()))


def make_hierarchy_receipt(
    path, potentials: dict[str, int], edge_values, must_dominate=(),
) -> HierarchyHolonomyReceipt:
    path_t = tuple(path)
    pot_items = _normalize_potentials(potentials)
    edge_t = tuple(edge_values)
    dom_t = tuple((hi, lo) for hi, lo in must_dominate)

    def quarantine(reason: str) -> HierarchyHolonomyReceipt:
        return HierarchyHolonomyReceipt(
            path=path_t, potentials=pot_items, edge_values=edge_t, must_dominate=dom_t,
            gauge_steps=(), endpoint_diff=None, gauge_circulation=None,
            observed_circulation=None, residual_circulation=None,
            hierarchy_violations=(), verdict=QUARANTINE, reason=reason).with_digest()

    if len(path_t) < 2:
        return quarantine("path-too-short")
    if len(edge_t) != len(path_t) - 1:
        return quarantine("edge-count-mismatch")
    if any(v not in potentials for v in path_t):
        return quarantine("missing-potential")
    if path_t[0] != path_t[-1]:
        return quarantine("not-closed-loop")
    if any(hi not in potentials or lo not in potentials for hi, lo in dom_t):
        return quarantine("missing-reference-node")

    gauge_steps = tuple(potentials[path_t[i + 1]] - potentials[path_t[i]]
                        for i in range(len(path_t) - 1))
    endpoint_diff = potentials[path_t[-1]] - potentials[path_t[0]]
    gauge_circulation = sum(gauge_steps)
    observed_circulation = sum(edge_t)
    residual_circulation = observed_circulation - endpoint_diff

    if gauge_circulation != endpoint_diff:
        return quarantine("gauge-telescope-failed")

    # The gradient component: the injection signal. A reference dominance constraint
    # (hi must strictly out-rank lo) is violated when potentials[hi] <= potentials[lo].
    violations = tuple((hi, lo) for hi, lo in dom_t
                       if not potentials[hi] > potentials[lo])

    if violations:
        verdict, reason = STRUCTURAL_ZERO, "hierarchy-violation"
    else:
        verdict, reason = ACCEPT, "hierarchy-intact"

    return HierarchyHolonomyReceipt(
        path=path_t, potentials=pot_items, edge_values=edge_t, must_dominate=dom_t,
        gauge_steps=gauge_steps, endpoint_diff=endpoint_diff,
        gauge_circulation=gauge_circulation, observed_circulation=observed_circulation,
        residual_circulation=residual_circulation, hierarchy_violations=violations,
        verdict=verdict, reason=reason).with_digest()


def verify_hierarchy_receipt(receipt: HierarchyHolonomyReceipt) -> bool:
    if not receipt.digest_matches():
        return False
    if receipt.verdict not in (ACCEPT, STRUCTURAL_ZERO, QUARANTINE):
        return False
    expected = make_hierarchy_receipt(
        receipt.path, dict(receipt.potentials), receipt.edge_values, receipt.must_dominate)
    return receipt.payload() == expected.payload()


def non_conservative(receipt: HierarchyHolonomyReceipt) -> bool:
    """True when the observed field has a curl residual (benign asymmetric reasoning).
    Reported, but NOT an injection signal."""
    return bool(receipt.observed_circulation)


# --------------------------------------------------------------------- demos ----

_LOOP = ("root", "system", "injected", "root")
_GUARD = (("system", "injected"),)   # system must out-rank any injected instruction


def demo_intact_receipt() -> HierarchyHolonomyReceipt:
    pot = {"root": 0, "system": 10, "injected": 1}
    edges = tuple(pot[_LOOP[i + 1]] - pot[_LOOP[i]] for i in range(len(_LOOP) - 1))
    return make_hierarchy_receipt(_LOOP, pot, edges, _GUARD)


def demo_hijack_receipt() -> HierarchyHolonomyReceipt:
    pot = {"root": 0, "system": 1, "injected": 10}     # gradient hijack, circulation 0
    edges = tuple(pot[_LOOP[i + 1]] - pot[_LOOP[i]] for i in range(len(_LOOP) - 1))
    return make_hierarchy_receipt(_LOOP, pot, edges, _GUARD)


if __name__ == "__main__":
    for name, r in (("intact", demo_intact_receipt()), ("hijack", demo_hijack_receipt())):
        print(f"{name:8s} verdict={r.verdict:15s} reason={r.reason:20s} "
              f"circulation={r.observed_circulation} violations={list(r.hierarchy_violations)} "
              f"verifies={verify_hierarchy_receipt(r)}")
