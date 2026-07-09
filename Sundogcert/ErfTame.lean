/-
# Dimension-one erf tameness — the fifth monotone-activation witness off R1.

Unlike sigmoid/tanh/softplus/arctan, mathlib has **no error function** (prior-art check
2026-07-09: `Real.erf` absent). So this witness is not reuse — erf is defined here from
scratch as the Gaussian primitive, and its two core facts are proved by real analysis:

  `erf(x) = (2/√π) · ∫₀ˣ e^{-t²} dt`.

- `erf_continuous` — the primitive of a continuous function is continuous
  (`intervalIntegral.continuous_primitive`).
- `erf_strictMono` — the integrand is strictly positive, so the integral strictly
  increases in its upper limit (`intervalIntegral_pos_of_pos_on` +
  `integral_add_adjacent_intervals`), and the positive constant preserves it — hence
  injective.

With those two facts the dimension-one factory (`SigmoidTame`) applies unchanged:
`erf_lt_tame … erf_dnf_tame`. Fifth confirmation, and the first requiring a from-scratch
definition. Same fence: dimension one only.

*Pre-registered falsifier* `ERF_ABSENT` — FIRED (mathlib lacks erf), fallback engaged:
erf built from the interval integral. `MONO_FRONTIER` / `BOOL_CLOSURE_LEAK`
inherited-cleared.
-/
import Sundogcert.SigmoidTame
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Sundog.OMinimalErf

open Sundog.OMinimalOne Sundog.OMinimalSigmoid MeasureTheory

/-! ### The error function, defined from the Gaussian primitive -/

/-- The error function `erf(x) = (2/√π) · ∫₀ˣ e^{-t²} dt`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

private theorem gauss_continuous : Continuous fun t : ℝ => Real.exp (-t ^ 2) := by fun_prop

private theorem gauss_ii (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t ^ 2)) volume a b :=
  gauss_continuous.intervalIntegrable a b

private theorem const_pos : (0 : ℝ) < 2 / Real.sqrt Real.pi :=
  div_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)

theorem erf_continuous : Continuous erf := by
  unfold erf
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_primitive gauss_ii 0

theorem erf_strictMono : StrictMono erf := by
  intro x y hxy
  unfold erf
  have hadd := intervalIntegral.integral_add_adjacent_intervals (gauss_ii 0 x) (gauss_ii x y)
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on
    (gauss_ii x y) (fun t _ => Real.exp_pos _) hxy
  have hlt : (∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2))
      < ∫ t in (0 : ℝ)..y, Real.exp (-t ^ 2) := by linarith
  exact mul_lt_mul_of_pos_left hlt const_pos

theorem erf_injective : Function.Injective erf := erf_strictMono.injective

/-! ### erf on an affine pre-image -/

theorem erf_affine_continuous (a b : ℝ) : Continuous fun x => erf (a * x + b) :=
  erf_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem erf_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => erf (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact erf_injective.comp haff

/-! ### The dimension-one erf class is tame -/

theorem erf_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | erf (a * x + b) < r} :=
  tame_sublevel_of_injective (erf_affine_continuous a b) (erf_affine_injective ha b) r

theorem erf_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < erf (a * x + b)} :=
  tame_superlevel_of_injective (erf_affine_continuous a b) (erf_affine_injective ha b) r

theorem erf_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | erf (a * x + b) ≤ r} :=
  tame_le_of_injective (erf_affine_continuous a b) (erf_affine_injective ha b) r

theorem erf_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ erf (a * x + b)} :=
  tame_ge_of_injective (erf_affine_continuous a b) (erf_affine_injective ha b) r

theorem erf_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | erf (a * x + b) = r} :=
  tame_level_of_injective (erf_affine_injective ha b) r

/-- A two-sided erf band is tame (an intersection of thresholds). -/
theorem erf_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < erf (a * x + b) ∧ erf (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (erf_gt_tame ha b r₁) (erf_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable erf bands is tame. -/
theorem erf_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ))
    (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < erf (s.1 * x + s.2.1) ∧
          erf (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact erf_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalErf
