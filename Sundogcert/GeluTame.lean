/-
# Dimension-one GELU — the first non-monotone activation, reduced to one analytic fact.

GELU escapes the monotone factory: `gelu(x) = x·Φ(x)` has a minimum near `x ≈ −0.75`,
so it is not injective. It is also unexpressible in raw mathlib (no Gaussian CDF `Φ`) —
but it IS expressible via THIS lane's error function, since `Φ(x) = (1 + erf(x/√2))/2`.
So we define it here, in-lane, and reduce its dimension-one tameness to exactly one
statement using the finite-fiber core.

- `gelu`, `gelu_continuous`, `gelu_affine_continuous` — GELU is in the lane and
  continuous (`erf_continuous` composed and scaled).
- `GeluFibersFinite` — THE remaining obligation: every level set `{x | gelu x = c}` is
  finite. This is true (two monotone branches ⇒ ≤ 2 points per fiber) but its proof is
  a genuine analytic lift — GELU unimodality via `gelu' = Φ + x·φ` having a single sign
  change, which needs Gaussian tail/integral facts on top of the hand-rolled `erf`. NOT
  proved here; stated as the single hypothesis.
- `gelu_lt_tame … gelu_dnf_tame` — GIVEN `GeluFibersFinite`, every one-variable
  affine-GELU threshold, band, and finite DNF is tame. The finite-fiber core carries
  the whole reduction; affine pre-composition preserves finite fibers
  (`gelu_affine_fiber_finite`, preimage under an injective affine map).

This is the honest state of GELU: in-lane, continuous, and tame modulo one finiteness
lemma — the first activation whose tameness is not free from monotonicity, filed with
its exact obstruction rather than faked.
-/
import Sundogcert.ErfTame
import Sundogcert.FiniteFiberTame

namespace Sundog.OMinimalGelu

open Sundog.OMinimalOne Sundog.OMinimalFiber Sundog.OMinimalErf Sundog.OMinimalSigmoid

/-! ### GELU, via the lane's error function -/

/-- The Gaussian Error Linear Unit `gelu(x) = x·Φ(x)`, with the standard normal CDF
`Φ(x) = (1 + erf(x/√2))/2` supplied by the lane's `erf`. -/
noncomputable def gelu (x : ℝ) : ℝ := x * (1 + erf (x / Real.sqrt 2)) / 2

theorem gelu_continuous : Continuous gelu := by
  unfold gelu
  have h1 : Continuous fun x : ℝ => erf (x / Real.sqrt 2) :=
    erf_continuous.comp (continuous_id.div_const _)
  exact (continuous_id.mul (continuous_const.add h1)).div_const _

theorem gelu_affine_continuous (a b : ℝ) : Continuous fun x => gelu (a * x + b) :=
  gelu_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

/-! ### The single remaining obligation -/

/-- **The one open lemma.** GELU's level sets are finite — true (two monotone branches
⇒ at most two points), but its proof is an analytic lift (unimodality via
`gelu' = Φ + x·φ`, needing Gaussian tail facts). Everything below is unconditional in
this hypothesis. -/
def GeluFibersFinite : Prop := ∀ c : ℝ, {x | gelu x = c}.Finite

/-- Affine pre-composition preserves finite fibers (preimage under an injective map). -/
theorem gelu_affine_fiber_finite {a : ℝ} (ha : a ≠ 0) (b c : ℝ)
    (hfin : {x | gelu x = c}.Finite) : {x | gelu (a * x + b) = c}.Finite := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  have e : {x | gelu (a * x + b) = c} = (fun x => a * x + b) ⁻¹' {y | gelu y = c} := rfl
  rw [e]
  exact hfin.preimage haff.injOn

/-! ### The dimension-one GELU class is tame — given `GeluFibersFinite` -/

section Reduction

variable (hfin : GeluFibersFinite)
include hfin

theorem gelu_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu (a * x + b) < r} :=
  tame_sublevel_of_finite (gelu_affine_continuous a b)
    (gelu_affine_fiber_finite ha b r (hfin r))

theorem gelu_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < gelu (a * x + b)} :=
  tame_superlevel_of_finite (gelu_affine_continuous a b)
    (gelu_affine_fiber_finite ha b r (hfin r))

theorem gelu_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu (a * x + b) ≤ r} :=
  tame_le_of_finite (gelu_affine_continuous a b)
    (gelu_affine_fiber_finite ha b r (hfin r))

theorem gelu_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ gelu (a * x + b)} :=
  tame_ge_of_finite (gelu_affine_continuous a b)
    (gelu_affine_fiber_finite ha b r (hfin r))

theorem gelu_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu (a * x + b) = r} :=
  tame_level_of_finite (gelu_affine_fiber_finite ha b r (hfin r))

/-- A two-sided GELU band is tame (given the finiteness obligation). -/
theorem gelu_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < gelu (a * x + b) ∧ gelu (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (gelu_gt_tame hfin ha b r₁) (gelu_lt_tame hfin ha b r₂)

/-- **The class closes** (given the finiteness obligation): any finite union of
one-variable GELU bands is tame. -/
theorem gelu_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ))
    (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < gelu (s.1 * x + s.2.1) ∧
          gelu (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact gelu_band_tame hfin (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Reduction

end Sundog.OMinimalGelu
