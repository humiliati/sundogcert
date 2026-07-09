/-
# Dimension-one arctan tameness — the fourth monotone-activation witness off R1.

`arctan` is a bounded (range `(-π/2, π/2)`), strictly increasing activation, and the
cleanest instance of the factory yet: mathlib hands over both facts the core needs.

- `Real.continuous_arctan` and `Real.arctan_strictMono` (mathlib) — continuity and
  strict monotonicity, hence injectivity.
- `arctan_lt_tame … arctan_eq_tame`, `arctan_band_tame`, `arctan_dnf_tame` — every
  one-variable affine-arctan threshold, band, and finite DNF is tame.

Fourth confirmation of the dimension-one monotone-activation factory
(`tame_{sub,super}level_of_injective`). Same fence: dimension one only.

*Pre-registered falsifier* `ARCTAN_INSTANCE_VACUOUS` (mathlib lacks arctan
continuity/monotonicity) — CLEARED. `MONO_FRONTIER` / `BOOL_CLOSURE_LEAK`
inherited-cleared (reused core).
-/
import Sundogcert.SigmoidTame
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace Sundog.OMinimalArctan

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-! ### The two facts the core needs are mathlib's -/

theorem arctan_injective : Function.Injective Real.arctan :=
  Real.arctan_strictMono.injective

/-! ### arctan on an affine pre-image -/

theorem arctan_affine_continuous (a b : ℝ) :
    Continuous fun x => Real.arctan (a * x + b) :=
  Real.continuous_arctan.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem arctan_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => Real.arctan (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact arctan_injective.comp haff

/-! ### The dimension-one arctan class is tame -/

theorem arctan_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | Real.arctan (a * x + b) < r} :=
  tame_sublevel_of_injective (arctan_affine_continuous a b)
    (arctan_affine_injective ha b) r

theorem arctan_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < Real.arctan (a * x + b)} :=
  tame_superlevel_of_injective (arctan_affine_continuous a b)
    (arctan_affine_injective ha b) r

theorem arctan_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | Real.arctan (a * x + b) ≤ r} :=
  tame_le_of_injective (arctan_affine_continuous a b)
    (arctan_affine_injective ha b) r

theorem arctan_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ Real.arctan (a * x + b)} :=
  tame_ge_of_injective (arctan_affine_continuous a b)
    (arctan_affine_injective ha b) r

theorem arctan_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | Real.arctan (a * x + b) = r} :=
  tame_level_of_injective (arctan_affine_injective ha b) r

/-- A two-sided arctan band is tame (an intersection of thresholds). -/
theorem arctan_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < Real.arctan (a * x + b) ∧ Real.arctan (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (arctan_gt_tame ha b r₁) (arctan_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable arctan bands is tame. -/
theorem arctan_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ))
    (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < Real.arctan (s.1 * x + s.2.1) ∧
          Real.arctan (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact arctan_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalArctan
