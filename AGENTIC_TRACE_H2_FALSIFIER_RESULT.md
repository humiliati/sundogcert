# H-II FALSIFIER — the cusp detector detects inflections, not fold-pair annihilations

**Frozen:** 2026-06-27, repo HEAD `86621ff` (master).
**Status:** **FALSIFIER FIRES** — H-II's own pre-registered falsifier (both forms)
is satisfied by a runnable, receipt-checkable counterexample against the live
`scripts/cusp_detector.py`. A fired falsifier on a **second-wave** hypothesis is a
banked SUCCESS: it is caught before any Lean work, and it localizes the exact
re-spec the detector needs.
**Lane:** sundogcert agentic-trace slate, Hypothesis II (Whitney A3 Cusp for
Context Decay).

---

## §1 What was attacked

H-II proposes: treat memory retrieval as a one-parameter regularized risk curve,
detect a **cusp-like transition** (a Whitney A3 fold-pair annihilation) in a local
jet of the retrieval score, and quarantine memory until the topology returns to the
smooth side. Its runtime spec is `cusp_detector.make_cusp_receipt`: five evenly
spaced samples → three second differences `c2` and two third differences `c3`;
`structural-zero` (a cusp signature) is declared when `c2` changes sign across the
center, the center `c2` is exactly 0, both flanks clear a magnitude, and `c3` is
bounded.

The slate pre-registers the falsifier:

> find stale-context failures with no cusp signature, or clean fresh-context
> retrievals that repeatedly trigger the cusp detector.

## §2 The defect

An **A3 cusp is a fold-pair annihilation**: as a control parameter varies, two
extrema of the score (`f' = 0` points) merge and vanish; at the cusp the critical
point is degenerate (`f' = f'' = 0`). The detector inspects only the **second**
difference (`c2 ≈ f''`, curvature) of **one** 1-D jet. It never looks at the
**first** difference (`f'`, slope / whether extrema exist), and a single 1-D jet
cannot see a control-parameter event. So its signature — "`c2` sign-change with
center 0" — is an **inflection**, which is neither necessary nor sufficient for the
fold-pair annihilation it claims.

## §3 The counterexample (3 legs, all verified against the live detector)

| leg | construction | detector says | should be |
|---|---|---|---|
| **A — false positive** | a monotone, **fold-free** S-curve `[-5,-3,0,3,5]` (0 interior extrema; a healthy saturating retrieval score) | **`structural-zero`** | accept |
| **B — annihilation-blind** | the canonical unfolding `x³ − e·x` for `e = 3,1,0,-1,-3` | **identical** `structural-zero`, `c2 = (-6,0,6)` for every `e` | the verdict must CHANGE as the fold pair (2 interior extrema at `e=3`) annihilates into a monotone curve (`e≤0`) |
| **C — false negative** | the genuine cusp germ `x³` sampled **off-center** (`-1.5 … 2.5`) | **`accept`** | structural-zero |

```
[A] monotone S-curve [-5,-3,0,3,5] (interior_extrema=0) -> structural-zero   FIRES
[B] e=+3 structural-zero c2=(-6,0,6) interior_extrema=2   <- fold pair present
    e=+0 structural-zero c2=(-6,0,6) interior_extrema=0   <- annihilated
    e=-3 structural-zero c2=(-6,0,6) interior_extrema=0   <- monotone
    verdict_invariant=True  FIRES  (blind to the annihilation between e=3 and e=0)
[C] x^3 off-center -> accept   FIRES (missed)
control: parabola->accept  demo_cusp->structural-zero   (detector still discriminates)
```

Why B is decisive: the second difference of *any* cubic at evenly spaced points is
linear in `x`, hence antisymmetric about the center, hence always `(-6,0,6)` — so
the detector's verdict is **invariant** along the entire unfolding, including across
the annihilation event it exists to find. It is detecting "is this curve cubic /
odd-curved," not "did a fold pair just die."

Frozen as `scripts/h2_cusp_detector_falsifier.py` (+ `test_h2_cusp_detector_falsifier.py`,
5 tests; 12 pass with the existing cusp tests).

## §4 What it means (H-II's detector spec must be re-specified, not patched)

The 1-D `c2`-sign-change signature is a **mis-specification**, not a tunable
threshold. No setting of `min_abs_c2` / `max_abs_center_c2` / `max_abs_c3` fixes
legs A–C, because the quantity measured (curvature of one jet) is the wrong
quantity. A faithful cusp/fold-pair detector must:

- examine the **first** difference (track interior extrema / critical points), so a
  monotone fold-free curve is rejected (kills leg A) and the *presence* of a fold
  pair is actually measured; and
- operate on the **two-parameter unfolding** (watch extrema merge as the control
  parameter varies), since the annihilation is a control-parameter event a single
  1-D jet cannot witness (kills leg B); the off-center brittleness (leg C) is a
  symptom of pinning to one fragile exact condition rather than the topological
  count of extrema.

This is a deeper re-spec than the H-I fix (which was a binding addition): H-II's
detector needs rebuilding around the extrema/critical-point structure before any
Lean quarantine theorem is worth writing.

**Slate effect.** H-II promotion status moves from "second wave — needs a detector
spec" to **falsifier-gated: the detector spec is falsified and must be re-specified
(first-difference / fold-count + two-parameter unfolding) before Lean work.**

## §5 Reproduce

```sh
python scripts/h2_cusp_detector_falsifier.py
python scripts/h2_cusp_detector_falsifier.py --json
python -m pytest scripts/test_h2_cusp_detector_falsifier.py -q
```

## §6 Scope / honesty

- This is a **runtime** falsifier on the detector spec, not a claim about
  catastrophe theory (which is correct) or about any vector database (the
  memory→cusp mapping remains the unbuilt imported wall — the falsifier shows the
  detector would mislabel even synthetic curves, so the wall cannot yet be tested
  faithfully).
- The detector is not trivially broken (the control discriminates parabola from the
  demo cusp); the legs are deliberate fold-free / annihilating / off-center
  constructions, all deterministic and test-pinned.
