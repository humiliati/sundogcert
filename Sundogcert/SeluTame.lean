/-
# Dimension-one SELU tameness — scaled ELU, still monotone.

`selu(x) = λ·(x)` for `x ≥ 0`, `λ·α·(eˣ − 1)` for `x < 0`, with SELU's constants
`λ ≈ 1.0507`, `α ≈ 1.6733` (both positive). Since `λ, α > 0`, SELU is STRICTLY MONOTONE
(scaled ELU), so it is the MONOTONE injective-core route again — no Rolle.

We parametrize by `λ, α` with `0 < λ`, `0 < α`: the exact SELU constants are a specific
positive-real instance (they are defined by a self-normalization fixed point, irrational),
and the tameness holds for the whole positive-constant family — SELU, ELU (`λ = α = 1`),
and the scaled/leaky variants alike. Continuity needs no positivity; strict monotonicity
uses `0 < λ` (outer scale) and `0 < α` (the negative branch, `α(eˣ − 1) < 0 ≤ y`).

Then the dimension-one factory (`SigmoidTame`'s continuous-injective threshold core)
applies unchanged: `selu_lt_tame … selu_dnf_tame`.

*Pre-registered falsifier* `SELU_SCALED_MONOTONE` (positive scaling preserves ELU's strict
monotonicity, so the injective core applies) — cleared.
-/
import Sundogcert.SigmoidTame

namespace Sundog.OMinimalSelu

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-- The Scaled ELU `selu(x) = λ·(x)` (`x ≥ 0`) / `λ·α·(eˣ − 1)` (`x < 0`). -/
noncomputable def selu (lam alp x : ℝ) : ℝ :=
  lam * (if 0 ≤ x then x else alp * (Real.exp x - 1))

theorem selu_continuous (lam alp : ℝ) : Continuous (selu lam alp) := by
  unfold selu
  refine continuous_const.mul ?_
  exact Continuous.if_le continuous_id
    (continuous_const.mul (Real.continuous_exp.sub continuous_const))
    continuous_const continuous_id (fun x hx => by rw [← hx]; simp)

theorem selu_affine_continuous (lam alp a b : ℝ) :
    Continuous fun x => selu lam alp (a * x + b) :=
  (selu_continuous lam alp).comp ((continuous_const.mul continuous_id).add continuous_const)

section
variable {lam alp : ℝ} (hlam : 0 < lam) (halp : 0 < alp)
include hlam halp

theorem selu_strictMono : StrictMono (selu lam alp) := by
  intro x y hxy
  unfold selu
  refine mul_lt_mul_of_pos_left ?_ hlam
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (le_trans hx hxy.le)]; exact hxy
  · rw [if_neg hx]
    by_cases hy : 0 ≤ y
    · rw [if_pos hy]
      have hlt : Real.exp x < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (not_le.mp hx)
      have hneg : alp * (Real.exp x - 1) < 0 := mul_neg_of_pos_of_neg halp (by linarith)
      linarith
    · rw [if_neg hy]
      have := Real.exp_lt_exp.mpr hxy
      exact mul_lt_mul_of_pos_left (by linarith) halp

theorem selu_injective : Function.Injective (selu lam alp) :=
  (selu_strictMono hlam halp).injective

theorem selu_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => selu lam alp (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact (selu_injective hlam halp).comp haff

/-! ### The dimension-one SELU class is tame -/

theorem selu_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | selu lam alp (a * x + b) < r} :=
  tame_sublevel_of_injective (selu_affine_continuous lam alp a b)
    (selu_affine_injective hlam halp ha b) r

theorem selu_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < selu lam alp (a * x + b)} :=
  tame_superlevel_of_injective (selu_affine_continuous lam alp a b)
    (selu_affine_injective hlam halp ha b) r

theorem selu_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | selu lam alp (a * x + b) ≤ r} :=
  tame_le_of_injective (selu_affine_continuous lam alp a b)
    (selu_affine_injective hlam halp ha b) r

theorem selu_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ selu lam alp (a * x + b)} :=
  tame_ge_of_injective (selu_affine_continuous lam alp a b)
    (selu_affine_injective hlam halp ha b) r

theorem selu_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | selu lam alp (a * x + b) = r} :=
  tame_level_of_injective (selu_affine_injective hlam halp ha b) r

/-- A two-sided SELU band is tame. -/
theorem selu_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < selu lam alp (a * x + b) ∧ selu lam alp (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (selu_gt_tame hlam halp ha b r₁) (selu_lt_tame hlam halp ha b r₂)

/-- **The class closes.** Any finite union of one-variable SELU bands is tame. -/
theorem selu_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < selu lam alp (s.1 * x + s.2.1) ∧
          selu lam alp (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact selu_band_tame hlam halp (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end

end Sundog.OMinimalSelu
