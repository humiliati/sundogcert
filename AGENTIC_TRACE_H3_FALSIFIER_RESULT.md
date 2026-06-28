# H-III FALSIFIER — the holonomy filter detects loop curl, not the instruction hierarchy

**Frozen:** 2026-06-28, repo HEAD `master`.
**Status:** **FALSIFIER FIRES** — H-III's own pre-registered falsifier (both forms:
an injection that preserves the zero receipt while changing the instruction hierarchy,
AND a benign trace with persistent nonzero phase) is satisfied by runnable,
receipt-checkable counterexamples against the live
`scripts/discrete_holonomy_receipt.py`. A fired falsifier is a banked SUCCESS: it is
caught before any ML-filter claim, and it localizes the exact re-spec the filter needs.
**Lane:** sundogcert agentic-trace slate, Hypothesis III (Aharonov-Bohm Holonomy
Filter).

---

## §1 The instrument and its claim

The runtime filter (`discrete_holonomy_receipt.make_holonomy_receipt`) maps a reasoning
trace to a closed loop with vertex **potentials** (an authority/instruction field) and
observed **edge values** (the transition field), and emits:

- `accept` — closed loop, **observed circulation `sum(edge_values) = 0`**;
- `structural-zero` — closed loop, observed circulation `≠ 0` (flag / halt);
- `quarantine` — malformed data.

H-III's hook: *a prompt injection looks locally ordinary but creates a nonzero loop
anomaly*, so the circulation receipt catches it. The executable companion is grounded
in the proved `Sundogcert.DiscreteHolonomy.closed_gauge_sum_zero`: a pure gauge
(gradient) field telescopes to zero around any closed loop.

## §2 The defect — the proved theorem IS the blind spot

A loop circulation measures only the **non-conservative (curl / flux)** component of the
trace field (the cohomologically nontrivial part). The **instruction hierarchy** is
carried by the **potentials** — the **conservative (gradient / gauge)** component — and
`closed_gauge_sum_zero` proves a gradient contributes **exactly zero to every loop**. So
the filter watches the wrong Hodge component: it certifies the curl part is zero while
the hierarchy lives in the exact part it provably cannot see. Gauge invariance
(`A → A + grad χ` leaves the loop observable fixed) becomes the **attack's cloak**.

## §3 The three legs (all fire against the live filter)

| leg | construction | filter says | truth |
|---|---|---|---|
| **A — gradient hijack invisible** (false negative, the killer) | re-level the authority potentials so `injected` outranks `system`; let the trace follow the new gradient (`edge_values` = gauge steps) | **`accept`, circulation 0** — identical to benign | the **top authority flipped `system → injected`**: the hierarchy was hijacked |
| **A′ — gauge-transform invariance** | add a gauge transform `χ` to a benign potential (the attack vector) | **observed circulation invariant**, still `accept` | the ranking moved `system → injected` under an invisible `A → A + grad χ` |
| **B — benign curl** (false positive) | clean monotone potentials, no injection, but observed edges `(1,1,1)` have real curl | **`structural-zero`** (flag/halt), circulation 3 | benign asymmetric OOD reasoning, no hierarchy violation |

**Control (detector not trivially broken):** a non-conservative attack with edges
`(5,5,5)` → circulation 15 → **`structural-zero` (caught)**. The filter *does* see the
curl component; it is specifically blind to the gradient component. So the legs are not
"the detector is dead" — they are "it measures curl, but the hierarchy attack is
gradient." `falsifier_fires = True ∧ control_holds = True`.

## §4 Why this is a mis-specification, not a tunable threshold

No threshold on `observed_circulation` recovers the missing component: leg A's
circulation is **exactly 0** (by the zero-out theorem), so any nonzero alarm threshold
still `accept`s the hijack, while lowering the threshold to flag leg A would flag every
benign closed loop. The curl and the gradient are orthogonal Hodge components; a loop
integral is, by construction, a functional of the curl alone. The hierarchy cannot be
read off it at any threshold.

## §5 The fix direction (the re-spec, not yet built)

Mirroring H-I (bind the decisive indices) and H-II (re-spec around the fold count): a
faithful injection filter must monitor the **gradient / potential (exact) component** —
the very part `closed_gauge_sum_zero` says loops cannot see — e.g. a receipt over the
**endpoint potential differences along the authority ordering** (a path/coboundary
check), or a Hodge split certifying *both* the curl is zero **and** the potential
ranking is unviolated. The discrete theorem already in `DiscreteHolonomy`
(`gauge_sum_eq_endpoint`) is the right surface: the endpoint difference, not the loop
sum, carries the hierarchy. Promotion now requires that re-spec before any ML-filter
claim.

## §6 Scope / honesty

- This is a **runtime** falsifier on the filter's measurement map, not a claim about
  catastrophe/gauge theory (which is correct) or about transformer attention (the
  trace→holonomy map remains the unbuilt imported wall — the falsifier shows the filter
  would mislabel even synthetic traces, so the wall cannot yet be tested faithfully).
- The legs are deterministic, receipt-verifiable (`verify_holonomy_receipt`), and frozen
  as a test (`scripts/test_h3_holonomy_filter_falsifier.py`, 5 cases). The control
  discriminates a curl attack from the gradient attack, so the instrument is live.

Artifacts: `scripts/h3_holonomy_filter_falsifier.py`,
`scripts/test_h3_holonomy_filter_falsifier.py`.
