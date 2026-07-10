/-
# Dimension-one Leaky ReLU tameness — a piecewise-LINEAR monotone activation.

`lrelu(x) = x` for `x ≥ 0`, `α·x` for `x < 0` (canonical `α = 0.01`, any `α > 0`). This is
the piecewise-*linear* sibling of ELU: same shape (a slope change at `0`), but both branches
are linear, so it is even simpler than ELU. Both slopes are positive, so `lrelu` is STRICTLY
MONOTONE and belongs to the MONOTONE injective-core route — NOT the non-monotone Rolle route.

- `lrelu_continuous` — the two linear pieces glue continuously at `0` (`Continuous.if_le`,
  boundary condition `0 = x ⇒ x = α·x`, true at `x = 0`).
- `lrelu_strictMono` — strict monotonicity by cases on the signs of `x, y`: the cross case
  `x < 0 ≤ y` uses `α·x < 0 ≤ y` (`α > 0`, `x < 0`); no exponential needed (contrast ELU).

Then the dimension-one factory (`SigmoidTame`'s continuous-injective threshold core) applies
unchanged: `lrelu_lt_tame … lrelu_dnf_tame`.

*Pre-registered falsifiers*: `LEAKY_RELU_PIECEWISE_CONT` (the if-then-else glues continuously)
and `LEAKY_RELU_STRICTMONO` (both slopes positive ⇒ strictly increasing) — cleared. No Rolle
needed (Leaky ReLU is monotone). Note plain ReLU (`α = 0`) is flat on the negatives, hence
non-strict — it fits neither the injective nor the finite-fiber core; the *leaky* variant is
the ReLU-family member the monotone core captures.
-/
import Sundogcert.SigmoidTame

namespace Sundog.OMinimalLeakyRelu

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-! ### The Leaky ReLU activation -/

/-- The Leaky ReLU negative slope `α = 0.01`. -/
def lra : ℝ := 0.01

theorem lra_pos : 0 < lra := by unfold lra; norm_num

/-- The Leaky ReLU `lrelu(x) = x` (`x ≥ 0`) / `α·x` (`x < 0`). -/
noncomputable def lrelu (x : ℝ) : ℝ := if 0 ≤ x then x else lra * x

theorem lrelu_continuous : Continuous lrelu := by
  unfold lrelu
  exact Continuous.if_le continuous_id (continuous_const.mul continuous_id)
    continuous_const continuous_id (fun x hx => by rw [← hx]; simp)

theorem lrelu_strictMono : StrictMono lrelu := by
  intro x y hxy
  unfold lrelu
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (le_trans hx hxy.le)]; exact hxy
  · rw [if_neg hx]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]
      have hneg : lra * x < 0 := mul_neg_of_pos_of_neg lra_pos (not_le.mp hx)
      linarith
    · rw [if_neg hy]
      exact mul_lt_mul_of_pos_left hxy lra_pos

theorem lrelu_injective : Function.Injective lrelu := lrelu_strictMono.injective

/-! ### Leaky ReLU on an affine pre-image -/

theorem lrelu_affine_continuous (a b : ℝ) : Continuous fun x => lrelu (a * x + b) :=
  lrelu_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem lrelu_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => lrelu (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact lrelu_injective.comp haff

/-! ### The dimension-one Leaky ReLU class is tame -/

theorem lrelu_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | lrelu (a * x + b) < r} :=
  tame_sublevel_of_injective (lrelu_affine_continuous a b) (lrelu_affine_injective ha b) r

theorem lrelu_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < lrelu (a * x + b)} :=
  tame_superlevel_of_injective (lrelu_affine_continuous a b) (lrelu_affine_injective ha b) r

theorem lrelu_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | lrelu (a * x + b) ≤ r} :=
  tame_le_of_injective (lrelu_affine_continuous a b) (lrelu_affine_injective ha b) r

theorem lrelu_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ lrelu (a * x + b)} :=
  tame_ge_of_injective (lrelu_affine_continuous a b) (lrelu_affine_injective ha b) r

theorem lrelu_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | lrelu (a * x + b) = r} :=
  tame_level_of_injective (lrelu_affine_injective ha b) r

/-- A two-sided Leaky ReLU band is tame. -/
theorem lrelu_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < lrelu (a * x + b) ∧ lrelu (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (lrelu_gt_tame ha b r₁) (lrelu_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable Leaky ReLU bands is tame. -/
theorem lrelu_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < lrelu (s.1 * x + s.2.1) ∧
          lrelu (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact lrelu_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalLeakyRelu
