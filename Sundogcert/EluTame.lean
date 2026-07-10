/-
# Dimension-one ELU tameness — a piecewise MONOTONE activation.

`elu(x) = x` for `x ≥ 0`, `eˣ − 1` for `x < 0` (α = 1). Unlike GELU/SiLU/Mish, ELU is
STRICTLY MONOTONE (increasing on both pieces, continuous at 0), so it belongs to the
MONOTONE injective-core route — NOT the non-monotone Rolle route. The new element is the
PIECEWISE (if-then-else) definition:

- `elu_continuous` — the two pieces glue continuously at `0` (`Continuous.if_le`, boundary
  condition `0 = x ⇒ x = eˣ − 1`, true at `x = 0`).
- `elu_strictMono` — strict monotonicity by cases on the signs of `x, y`: the cross case
  `x < 0 ≤ y` uses `eˣ − 1 < 0 ≤ y` (`eˣ < e⁰ = 1`).

Then the dimension-one factory (`SigmoidTame`'s continuous-injective threshold core)
applies unchanged: `elu_lt_tame … elu_dnf_tame`.

*Pre-registered falsifiers*: `ELU_PIECEWISE_CONT` (the if-then-else glues continuously) and
`ELU_STRICTMONO` (piecewise strict monotonicity) — cleared. No Rolle needed (ELU is
monotone).
-/
import Sundogcert.SigmoidTame

namespace Sundog.OMinimalElu

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-! ### The ELU activation -/

/-- The Exponential Linear Unit `elu(x) = x` (`x ≥ 0`) / `eˣ − 1` (`x < 0`). -/
noncomputable def elu (x : ℝ) : ℝ := if 0 ≤ x then x else Real.exp x - 1

theorem elu_continuous : Continuous elu := by
  unfold elu
  exact Continuous.if_le continuous_id (Real.continuous_exp.sub continuous_const)
    continuous_const continuous_id (fun x hx => by rw [← hx]; simp)

theorem elu_strictMono : StrictMono elu := by
  intro x y hxy
  unfold elu
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (le_trans hx hxy.le)]; exact hxy
  · rw [if_neg hx]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]
      have hlt : Real.exp x < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (not_le.mp hx)
      linarith
    · rw [if_neg hy]
      have := Real.exp_lt_exp.mpr hxy
      linarith

theorem elu_injective : Function.Injective elu := elu_strictMono.injective

/-! ### ELU on an affine pre-image -/

theorem elu_affine_continuous (a b : ℝ) : Continuous fun x => elu (a * x + b) :=
  elu_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem elu_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => elu (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact elu_injective.comp haff

/-! ### The dimension-one ELU class is tame -/

theorem elu_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | elu (a * x + b) < r} :=
  tame_sublevel_of_injective (elu_affine_continuous a b) (elu_affine_injective ha b) r

theorem elu_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < elu (a * x + b)} :=
  tame_superlevel_of_injective (elu_affine_continuous a b) (elu_affine_injective ha b) r

theorem elu_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | elu (a * x + b) ≤ r} :=
  tame_le_of_injective (elu_affine_continuous a b) (elu_affine_injective ha b) r

theorem elu_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ elu (a * x + b)} :=
  tame_ge_of_injective (elu_affine_continuous a b) (elu_affine_injective ha b) r

theorem elu_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | elu (a * x + b) = r} :=
  tame_level_of_injective (elu_affine_injective ha b) r

/-- A two-sided ELU band is tame. -/
theorem elu_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < elu (a * x + b) ∧ elu (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (elu_gt_tame ha b r₁) (elu_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable ELU bands is tame. -/
theorem elu_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < elu (s.1 * x + s.2.1) ∧
          elu (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact elu_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalElu
