/-
# U-4 — The definability rate: an explicit uniform piece-count modulus for ReLU nets.

The universal-approximation ladder proves every continuous `f` on `[0,1]` is ReLU-approximable,
and `ExactRepr.net_hasPieceCover` proves every net realizes a *continuous piecewise-linear*
function (finitely many affine pieces): `∀ g : Net 1, ∃ k, HasPieceCover (realize1N g) k`. That
existence statement is the qualitative **tameness** content — the one consequence of o-minimality
the ReLU/semilinear family actually lives inside (a definable function has finitely many pieces).

Slate-4 U-4 asked whether "definability" adds anything **checkable** beyond the trivial
"PL ⊆ semialgebraic", *without* an o-minimal substrate (mathlib v4.30.0 has none: no o-minimal
structures, no semialgebraic sets, no cell decomposition). It does — and no such substrate is
needed. The `∃ k` above hides a **fully explicit, computed** bound: this module exposes it as a
piece-count **modulus** `netPieceBound : Net 1 → ℕ` and proves the cover at that explicit rate.
That is the checkable uniform-definability rate the H-A5 hook wanted — the finiteness *modulus* of
the PL fragment, self-contained (piecewise-linear functions are the simplest tame class, needing
only the lane's own cut-set calculus in `PieceCover` / `RegionPoly`).

**Honest scope.** This is NOT a formalization of o-minimality (still absent from mathlib, a
separate project). It is the concrete **PL finiteness-modulus** — the checkable shadow of the
o-minimal uniform-finiteness theorem, specialized to the ReLU family. It defeats the
`DEFINABILITY_ADDS_NOTHING` falsifier (which fires iff the only content is the trivial inclusion
with no checkable rate) by producing an explicit rate; it does **not** claim general definable
sets, cell decomposition, or the monotonicity theorem. The modulus is **representation-dependent**
(tight for monotone/additive circuits, exponentially loose for folding ones — the same tree-vs-DAG
honesty as U-3's cost bound), which is itself the honest verdict, not a defect.
-/
import Sundogcert.ExactRepr
import Sundogcert.AnalyticGate

namespace Sundog.DefinableRate

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.ExactRepr Sundog.RegionPoly
  Sundog.AnalyticGate

/-- **The explicit structural piece-count modulus** of a 1-D ReLU net: a computed upper bound on
the number of affine pieces of its realization. Mirrors the per-gate piece calculus — `+` adds
pieces, `scale` preserves them, `relu` at most doubles them (a new cut per existing piece where the
argument crosses zero). This is the witness hidden inside `ExactRepr.net_hasPieceCover`'s `∃ k`. -/
def netPieceBound : Net 1 → ℕ
  | Net.var _     => 1
  | Net.const _   => 1
  | Net.add a b   => netPieceBound a + netPieceBound b
  | Net.scale _ a => netPieceBound a
  | Net.relu a    => 2 * netPieceBound a

/-- **The definability rate (U-4 headline).** Every ReLU net realizes a piecewise-linear function
covered by `netPieceBound g` explicit affine pieces — the `∃ k` of `net_hasPieceCover` promoted to
a **computed, checkable modulus**. This is the uniform-definability rate for the PL/ReLU family:
the finiteness-of-pieces consequence of o-minimality, made concrete with no o-minimal substrate. -/
theorem net_pieceBound_cover : ∀ g : Net 1, HasPieceCover (realize1N g) (netPieceBound g) := by
  intro g
  induction g with
  | var i =>
    have h : realize1N (Net.var i) = (id : ℝ → ℝ) := by funext t; simp [realize1N]
    rw [h]; exact hasPieceCover_id
  | const c =>
    have h : realize1N (Net.const c) = (fun _ => c) := by funext t; simp [realize1N]
    rw [h]; exact hasPieceCover_const c
  | add a b iha ihb =>
    rw [realize1N_add]; exact hasPieceCover_add iha ihb
  | scale c a ih =>
    rw [realize1N_scale]; exact hasPieceCover_smul c ih
  | relu a ih =>
    rw [realize1N_relu]; exact hasPieceCover_relu ih

/-- The modulus is monotone-friendly: a pure `add`/`scale` combination stays **linear** in its
parts (no doubling). Witness of the "tight" regime. -/
example (a b : Net 1) : netPieceBound (Net.add a b) = netPieceBound a + netPieceBound b := rfl

/-- The `relu` gate **doubles** the modulus: a depth-`d` `relu` chain gives `2^d` — the "loose"
(folding) regime, matching `DepthSeparation`'s `2^d`-piece tent. So the definability modulus is
**representation-dependent**: linear for additive circuits, exponential for folding ones — the same
tree-vs-DAG gap U-3 fenced for cost (`SHARED_SIZE_NOT_CAPTURED`), now for definable complexity. The
honest content of the rate, not a defect of it. -/
example : netPieceBound (Net.relu (Net.relu (Net.relu (Net.var 0)))) = 8 := rfl

/-- **Corollary — the family definability rate for the analytic gate.** The secant interpolant for
`x²` is realized by `sqNet n`, whose realization is covered by `netPieceBound (sqNet n)` pieces,
while its L∞ error is `≤ 1/(4n²)` (`AnalyticGate.sqNet_le`). So `x²` has PL ε-approximants of
explicitly bounded definable complexity — the o-minimal reading of the ε > 0 approximation result:
*approximable by uniformly-definable functions with a checkable complexity modulus*. -/
theorem sqNet_definable_rate (n : ℕ) :
    HasPieceCover (realize1N (sqNet n)) (netPieceBound (sqNet n)) :=
  net_pieceBound_cover (sqNet n)

end Sundog.DefinableRate
