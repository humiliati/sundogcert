"""H-III falsifier: the holonomy filter detects loop CURL, not the instruction hierarchy.

H-III's hook: *a prompt injection looks locally ordinary while creating a nonzero loop
anomaly in the reasoning path*, so a gauge-style circulation receipt over a trace loop
catches it. The runtime is `discrete_holonomy_receipt.make_holonomy_receipt`, whose
anomaly signal is the OBSERVED LOOP CIRCULATION `sum(edge_values)`:
`accept` when it is zero, `structural-zero` (flag/halt) when nonzero.

But the filter's own proved theorem — `Sundogcert.DiscreteHolonomy.closed_gauge_sum_zero`
— is its blind spot. A loop circulation measures only the NON-CONSERVATIVE (curl / flux)
component of the trace field. The instruction hierarchy is carried by the POTENTIALS
(the conservative / gradient / gauge component), and a gradient contributes EXACTLY
ZERO to every closed loop. So:

  * Leg A (false negative — the killer): a hierarchy HIJACK encoded as a gradient
    (re-level the authority potentials, let the trace follow the new gradient) leaves
    the loop circulation at zero. The filter `accept`s it, identically to benign —
    even though the top authority flipped from `system` to the injected instruction.
    Gauge invariance (`A → A + grad χ` leaves the loop observable fixed) is the attack's
    cloak.
  * Leg B (false positive): a benign trace whose observed edges have genuine curl
    (asymmetric OOD reasoning, no hierarchy violation) gets `structural-zero` — flagged.
  * Control: a non-conservative (curl-type) attack IS caught. The detector is not
    trivially broken — it sees the curl component; it is specifically blind to the
    gradient component where the hierarchy lives.

Root cause: the receipt watches the wrong Hodge component. It certifies the
cohomologically nontrivial (loop) part is zero, while the instruction hierarchy is the
exact (gradient) part the zero-out theorem proves loops cannot see. This is a
mis-specification, not a tunable threshold.

Run:
  python scripts/h3_holonomy_filter_falsifier.py
"""

from __future__ import annotations

import json
import sys

from branch_budget_receipt import ACCEPT, STRUCTURAL_ZERO
from discrete_holonomy_receipt import make_holonomy_receipt, verify_holonomy_receipt

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")


def authority_ranking(potentials: dict[str, int]) -> tuple[str, ...]:
    """The instruction hierarchy the trace encodes: vertices by authority potential,
    highest first."""
    return tuple(v for v, _ in sorted(potentials.items(), key=lambda kv: (-kv[1], kv[0])))


def conservative_edges(path, potentials) -> tuple[int, ...]:
    """Observed edge field that FOLLOWS the authority gradient: edge_values = gauge
    steps. A conservative trace — its loop circulation is provably zero."""
    return tuple(potentials[path[i + 1]] - potentials[path[i]] for i in range(len(path) - 1))


# --------------------------------------------------------- leg A: false negative ----

def leg_A_gradient_hijack_invisible() -> dict:
    """A gradient-encoded hierarchy hijack and a benign trace produce the SAME zero
    receipt, yet the top authority flipped from `system` to the injected instruction."""
    path = ("root", "system", "injected", "root")
    benign = {"root": 0, "system": 10, "injected": 1}     # system outranks the injection
    hijack = {"root": 0, "system": 1, "injected": 10}     # injection now outranks system

    rb = make_holonomy_receipt(path, benign, conservative_edges(path, benign))
    rh = make_holonomy_receipt(path, hijack, conservative_edges(path, hijack))

    rank_b, rank_h = authority_ranking(benign), authority_ranking(hijack)
    fires = (
        rb.verdict == ACCEPT and rh.verdict == ACCEPT
        and rb.observed_circulation == 0 and rh.observed_circulation == 0
        and rank_b[0] == "system" and rank_h[0] == "injected"   # hierarchy hijacked
        and verify_holonomy_receipt(rb) and verify_holonomy_receipt(rh)
    )
    return {
        "leg": "A_gradient_hijack_invisible",
        "benign_rank": rank_b, "hijack_rank": rank_h,
        "benign": (rb.verdict, rb.observed_circulation),
        "hijack": (rh.verdict, rh.observed_circulation),
        "fires": fires,
        "note": "hierarchy top flipped system->injected; both receipts accept, circulation 0",
    }


def leg_A_gauge_transform_invariance() -> dict:
    """Sharper form: ADDING a gauge transform chi to a benign potential (the attack
    vector) leaves the observed circulation invariant while shifting the ranking."""
    path = ("root", "system", "injected", "root")
    benign = {"root": 0, "system": 10, "injected": 1}
    chi = {"root": 0, "system": -20, "injected": 0}        # the injected gauge transform
    attacked = {v: benign[v] + chi[v] for v in benign}      # system demoted below injected

    edges = conservative_edges(path, benign)               # same observed trace edges
    rb = make_holonomy_receipt(path, benign, edges)
    ra = make_holonomy_receipt(path, attacked, edges)
    fires = (
        rb.observed_circulation == ra.observed_circulation  # gauge-invariant observable
        and rb.verdict == ra.verdict == ACCEPT
        and authority_ranking(benign)[0] == "system"
        and authority_ranking(attacked)[0] == "injected"
    )
    return {
        "leg": "A_gauge_transform_invariance",
        "observed_circulation_invariant": rb.observed_circulation == ra.observed_circulation,
        "rank_before": authority_ranking(benign), "rank_after": authority_ranking(attacked),
        "fires": fires,
        "note": "A -> A + grad(chi) leaves the loop observable fixed; the ranking moved",
    }


# --------------------------------------------------------- leg B: false positive ----

def leg_B_benign_curl_flagged() -> dict:
    """A benign trace (clean authority potentials, no injection) whose observed edges
    have genuine curl is flagged as an anomaly."""
    path = ("root", "step1", "step2", "root")
    potentials = {"root": 0, "step1": 1, "step2": 2}       # clean, monotone authority
    edges = (1, 1, 1)                                       # net curl: circulation = 3 != 0
    r = make_holonomy_receipt(path, potentials, edges)
    fires = (
        r.verdict == STRUCTURAL_ZERO and r.observed_circulation != 0
        and authority_ranking(potentials)[0] == "step2"    # no injected node on top
        and verify_holonomy_receipt(r)
    )
    return {
        "leg": "B_benign_curl_flagged",
        "verdict": r.verdict, "observed_circulation": r.observed_circulation,
        "fires": fires,
        "note": "benign asymmetric reasoning (real curl) halted as if an attack",
    }


# ------------------------------------------------------------ control: not broken ----

def control_flux_attack_caught() -> dict:
    """A non-conservative (curl-type) attack IS caught: the detector sees the curl
    component, it is only blind to the gradient component."""
    path = ("root", "system", "injected", "root")
    potentials = {"root": 0, "system": 10, "injected": 1}
    edges = (5, 5, 5)                                       # injected real flux: circulation 15
    r = make_holonomy_receipt(path, potentials, edges)
    holds = r.verdict == STRUCTURAL_ZERO and r.observed_circulation != 0
    return {"leg": "control_flux_attack_caught", "verdict": r.verdict,
            "observed_circulation": r.observed_circulation, "holds": holds,
            "note": "curl-type anomaly is detected; detector is not trivially dead"}


def run() -> dict:
    legs = [leg_A_gradient_hijack_invisible(), leg_A_gauge_transform_invariance(),
            leg_B_benign_curl_flagged()]
    control = control_flux_attack_caught()
    falsifier_fires = all(leg["fires"] for leg in legs)
    return {
        "hypothesis": "H-III Aharonov-Bohm holonomy filter",
        "legs": legs, "control": control,
        "falsifier_fires": falsifier_fires, "control_holds": control["holds"],
        "verdict": ("FALSIFIER FIRES" if falsifier_fires and control["holds"]
                    else "inconclusive"),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, default=list))
