/-
# Dimension-one Softsign tameness — a bounded smooth-ish monotone activation.

`softsign(x) = x / (1 + |x|)`. Strictly increasing (its derivative `1/(1+|x|)² > 0`
everywhere), continuous everywhere (the denominator `1 + |x| ≥ 1 > 0` never vanishes — no
removable singularity, unlike a naive `x/|x|`), and bounded into `(−1, 1)`. So it rides the
MONOTONE injective-core route (`SigmoidTame`'s continuous-injective threshold core), NOT the
non-monotone Rolle route.

The one new element versus the smooth monotone activations (sigmoid/tanh/…): the `|x|` in the
denominator, which forces a sign-case split for strict monotonicity —

- both `≥ 0`: `x/(1+x) < y/(1+y) ⟺ x(1+y) < y(1+x) ⟺ x < y` (`div_lt_div_iff₀`);
- both `< 0`: `x/(1−x) < y/(1−y) ⟺ x(1−y) < y(1−x) ⟺ x < y`;
- cross `x < 0 ≤ y`: `softsign x < 0 ≤ softsign y` directly.

Then the dimension-one factory applies unchanged: `softsign_lt_tame … softsign_dnf_tame`.

*Pre-registered falsifiers*: `SOFTSIGN_DENOM_POS` (`1 + |x| ≥ 1 > 0`, continuous everywhere)
and `SOFTSIGN_STRICTMONO` (strictly increasing by sign-cases) — cleared. No Rolle needed
(Softsign is monotone).
-/
import Sundogcert.SigmoidTame

namespace Sundog.OMinimalSoftsign

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-! ### The Softsign activation -/

/-- The Softsign activation `softsign(x) = x / (1 + |x|)`. -/
noncomputable def softsign (x : ℝ) : ℝ := x / (1 + |x|)

theorem softsign_continuous : Continuous softsign :=
  Continuous.div continuous_id (continuous_const.add continuous_abs) (fun x => by positivity)

theorem softsign_strictMono : StrictMono softsign := by
  intro x y hxy
  simp only [softsign]
  by_cases hx : 0 ≤ x
  · -- x ≥ 0 ⇒ y > x ≥ 0: both nonnegative
    have hy : 0 ≤ y := le_trans hx hxy.le
    rw [abs_of_nonneg hx, abs_of_nonneg hy,
      div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hxy]
  · replace hx : x < 0 := not_le.mp hx
    by_cases hy : 0 ≤ y
    · -- x < 0 ≤ y: softsign x < 0 ≤ softsign y
      rw [abs_of_neg hx, abs_of_nonneg hy]
      have h1 : x / (1 + -x) < 0 := div_neg_of_neg_of_pos hx (by linarith)
      have h2 : 0 ≤ y / (1 + y) := div_nonneg hy (by linarith)
      linarith
    · -- both negative
      replace hy : y < 0 := not_le.mp hy
      rw [abs_of_neg hx, abs_of_neg hy,
        div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith [hxy]

theorem softsign_injective : Function.Injective softsign := softsign_strictMono.injective

/-! ### Softsign on an affine pre-image -/

theorem softsign_affine_continuous (a b : ℝ) : Continuous fun x => softsign (a * x + b) :=
  softsign_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem softsign_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => softsign (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact softsign_injective.comp haff

/-! ### The dimension-one Softsign class is tame -/

theorem softsign_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | softsign (a * x + b) < r} :=
  tame_sublevel_of_injective (softsign_affine_continuous a b) (softsign_affine_injective ha b) r

theorem softsign_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < softsign (a * x + b)} :=
  tame_superlevel_of_injective (softsign_affine_continuous a b) (softsign_affine_injective ha b) r

theorem softsign_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | softsign (a * x + b) ≤ r} :=
  tame_le_of_injective (softsign_affine_continuous a b) (softsign_affine_injective ha b) r

theorem softsign_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ softsign (a * x + b)} :=
  tame_ge_of_injective (softsign_affine_continuous a b) (softsign_affine_injective ha b) r

theorem softsign_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | softsign (a * x + b) = r} :=
  tame_level_of_injective (softsign_affine_injective ha b) r

/-- A two-sided Softsign band is tame. -/
theorem softsign_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < softsign (a * x + b) ∧ softsign (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (softsign_gt_tame ha b r₁) (softsign_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable Softsign bands is tame. -/
theorem softsign_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < softsign (s.1 * x + s.2.1) ∧
          softsign (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact softsign_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalSoftsign
