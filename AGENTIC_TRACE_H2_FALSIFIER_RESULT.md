# H-II FALSIFIER — the cusp detector detects inflections, not fold-pair annihilations

**Frozen:** 2026-06-27, repo HEAD `86621ff` (master).
**Status:** **FALSIFIER FIRES → FIX LANDED (§7) → LEAN CORE LANDED (§8).** H-II's
own pre-registered falsifier (both forms) was satisfied by a runnable counterexample
against the live `scripts/cusp_detector.py`; the re-specified fold-pair detector in
§7 closes all three legs; the §8 Lean module pins the quarantine rule's deductive
core, axiom-clean. A fired falsifier on a **second-wave** hypothesis is a banked
SUCCESS: caught before any Lean work, it localized the exact re-spec — and the re-spec is
done.
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

## §7 FIX LANDED — the re-specified fold-pair detector (2026-06-27)

`scripts/foldpair_detector.py` measures the right object on both axes the c2 spec
ignored:

- **first difference (slope) → fold count.** `count_interior_extrema` counts the
  sign-changes of the first difference (the interior extrema = *folds*) of each
  curve. A monotone curve has 0 folds, so it can never be a cusp.
- **two-parameter family → annihilation.** The detector takes curves ordered by
  increasing control (staleness); a fold-pair annihilation is a clean drop of the
  fold count **by 2** between adjacent controls. A single 1-D jet cannot witness
  this; the family can.

Outcomes: `structural-zero` (an annihilation occurred → decay/quarantine),
`accept` (no annihilation), `quarantine` (malformed: < 2 curves, < 5 evenly spaced
samples, non-increasing control, or an *unpaired* fold-count change — odd or
`|Δ|>2` — i.e. the sweep is too coarse to assert one clean fold pair). Receipts are
exact `Fraction`s and re-verifiable, matching `cusp_detector`'s shape.

**It closes the three falsifier legs** (`scripts/test_foldpair_detector.py`, the
legs re-cast as the families they should have been):

| leg | old `cusp_detector` | new `foldpair_detector` |
|---|---|---|
| A monotone fold-free S-curve | `structural-zero` (false positive) | **`accept`** (fold_counts all 0) |
| B `x³ − e·x` unfolding | invariant `structural-zero` (blind) | **`structural-zero`**, annihilation witnessed (fold count 2 → 0) |
| C cusp germ sampled off-center | `accept` (missed) | **`structural-zero`** (fold count is robust to centering — in fact resolves the shallow folds better off-center) |

```
demo annihilation (x^3 - e*x, e:3->0): fold_counts=[2,2,0,0] annihilations=(1->2) -> structural-zero
demo monotone:                          fold_counts=[0,0,0]   annihilations=none   -> accept
```

**What it does not claim.** It is a faithful *detector* of a fold-pair annihilation
in a sampled 2-parameter family; it is **not** the vector-memory → A3-cusp mapping
(still the imported wall — now testable on synthetic families without being
mislabelled). 20 tests pass (8 fold-pair fix + 5 falsifier + 7 existing cusp).

## §8 LEAN CORE — what an annihilation receipt licenses (2026-06-27)

`Sundogcert/ContextDecay.lean` pins the deductive content of the quarantine rule, the
way `AgenticTrace.decisive_*` pinned the H-I fix. The fold family is `FoldCounts :=
List ℕ` (fold count per curve, increasing-control order); `Decays cs` ⟺ some adjacent
pair drops by exactly two (the A3 event). Five theorems, all `omega`/`simp`-only, all
inside the foundational triple — in fact a **subset**: `[propext, Quot.sound]`, no
`Classical.choice`, no `sorryAx`, no `native_decide`. Enforced by `#guard_msgs` in
`Sundogcert/AxiomAudit.lean`; the full `lake build` is green (3538 jobs).

| theorem | content | H-I analog |
|---|---|---|
| `decay_earned` | a flagged decay exhibits a genuine fold pair (≥ 2 folds) that is annihilated | `decisive_kept` |
| `foldfree_no_decay` | a fold-free family (all counts 0) is **never** flagged — leg A, formalized | (the no-false-positive direction) |
| `stable_no_decay` | a constant fold count is never flagged | — |
| `decays_iff_foldpair` | **headline:** decay is licensed *iff* a fold pair (≥ 2) annihilates — soundness ∧ completeness | `decisive_receipt_safe_and_preserving` |
| `annihilation_budget` | along a pure annihilation chain, `2 · (#annihilations) ≤ initial fold count` — you can't annihilate more pairs than you have | `branch_count_le_budget` |

**What the Lean does not claim** (the named wall): it formalizes what an annihilation
*receipt* licenses, on the abstract fold-count family. It does **not** prove the
vector-memory → A3-cusp mapping. (The root-count grounding — that the cubic germ
actually realizes the count drop — is now landed in §9.)

## §9 CUSP-GERM GROUNDING — the cubic realizes the annihilation (2026-06-27)

`Sundogcert/CuspGerm.lean` grounds the abstract rule in the real catastrophe germ,
the way `AgenticTrace.decisive_*` is grounded in the RS `agree`/`Polynomial`
structure. The canonical fold-catastrophe **score curve** is `f_a(x) = x³ − a·x`; its
folds are the critical points = real roots of `f_a'(x) = 3x² − a`:

| theorem | content |
|---|---|
| `critSet_pos` / `critCount_pos` | `a > 0` → critical points are `±√(a/3)`, **fold count = 2** (a genuine max+min pair) |
| `critSet_neg` / `critCount_neg` | `a < 0` → `3x² − a > 0` everywhere, **fold count = 0** (monotone, the `accept` side) |
| `cubic_realizes_annihilation` | for `a₀ < 0 < a₁`, `[critCount a₁, critCount a₀] = [2, 0]` is a `ContextDecay.Decays` event — the germ produces the abstract drop-by-two |
| `cubic_foldpair_witness` | read through the `decays_iff_foldpair` headline: a genuine fold pair (≥ 2) annihilates |

> **Count correction.** For the *score curve* `x³ − a·x` the fold count is **2 for
> `a > 0`, 0 for `a < 0`** (a single fold pair born/annihilated). The "3 → 1" figure
> belongs to the degree-4 *potential* `x⁴/4 + a·x²/2`; the runtime detector and
> `ContextDecay` both key on the drop-**by-2** of the score curve, so the cubic germ
> is the faithful witness. The cusp point `a = 0` is the degenerate annihilation
> locus (the pair has merged into an inflection, `critSet` = `{0}`, no sign change);
> the annihilation is witnessed strictly between `a₁ > 0` and `a₀ < 0`, so the proof
> never leans on `a = 0`.

These four are real-analysis (`Real.sqrt`, `Set.ncard`) so they sit in the **full**
foundational triple `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`native_decide` — enforced by `#guard_msgs` in `AxiomAudit.lean`; full `lake build`
green (3539 jobs). The named wall is now narrower: only the vector-memory → cubic-germ
*mapping* remains an import; that the germ realizes the rule is proved.

## §10 MAPPING — the attractor-memory landscape realizes the rule (2026-06-27)

`Sundogcert/RetrievalCusp.lean` takes the last H-II step: it does **not** prove a real
vector database *is* a cusp (that stays the import), but it shrinks the import to a
crisp, interpretable model and proves the model realizes `ContextDecay`. The model is
the canonical associative/attractor memory — a Hopfield-style double-well energy whose
minima are the stored patterns:

  `V_a(x) = x⁴/4 − a·x²/2`,  `V_a'(x) = x³ − a·x = x(x² − a)`,  `V_a''(x) = 3x² − a`,

with control `a` = pattern separation / freshness. Its critical points (the stored
memories *and* the barrier between them) are the roots of `V_a'`:

| theorem | content |
|---|---|
| `critCountW_pos` | `a > 0` → critical points `{0, ±√a}`: **count 3** (two memories `±√a` + a barrier `0`) |
| `critCountW_neg` | `a < 0` → critical point `{0}`: **count 1** (barrier gone, wells merged) |
| `memories_are_minima` | `a > 0` → `V'' > 0` at `±√a` (stable, retrievable **memories**) and `V'' < 0` at `0` (the **barrier**) |
| `retrieval_realizes_annihilation` | for freshness `a₀ < 0 < a₁`, `[critCountW a₁, critCountW a₀] = [3, 1]` is a `ContextDecay.Decays` event — as freshness decays, two stored memories **merge** |
| `retrieval_foldpair_witness` | through `decays_iff_foldpair`: a genuine fold pair (≥ 2) annihilates as freshness decays |

So the structural story is fully machine-checked end to end: two stable memories +
a barrier (`memories_are_minima`) → barrier decays → the count drops 3 → 1
(`critCountW_*`) → that is a `ContextDecay` annihilation
(`retrieval_realizes_annihilation`), and the quarantine rule's deductive core
(`decays_iff_foldpair`, etc., §8) says what that licenses. Five theorems, real-analysis,
full triple `[propext, Classical.choice, Quot.sound]`, axiom-clean; full `lake build`
green (3540 jobs).

**The named import, now minimal.** The only unproved bridge left is: *a real retrieval
landscape is (locally) this attractor energy with a decaying barrier.* That is an
empirical/modelling claim, not a deductive one — testable, not provable — and the
natural test is `scripts/foldpair_detector.py` run on retrieval-score curves extracted
from a real embedding memory over a freshness/staleness sweep (the H-I-style empirical
complement). Everything from "given the model" onward is proved.
