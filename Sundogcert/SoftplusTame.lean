/-
# Dimension-one softplus tameness — the third monotone-activation witness off R1.

`softplus(x) = log(1 + eˣ)` — a strictly increasing, UNBOUNDED activation (range `(0,∞)`,
unlike the bounded sigmoid/tanh), and equally transcendental. Its dimension-one
tameness is again free off R1's continuous-injective threshold core (`SigmoidTame`):

- `softplus_continuous` (`Continuous.log` on the positive `1 + eˣ`) and
  `softplus_strictMono` (`Real.log_lt_log`, hence injective) — the two facts the core
  needs.
- `softplus_lt_tame … softplus_eq_tame` — every one-variable affine-softplus threshold
  is tame.
- `softplus_band_tame`, `softplus_dnf_tame` — the class closes under finite Boolean
  combination.

Third confirmation that `tame_{sub,super}level_of_injective` is a dimension-one
monotone-activation factory. Same fence: dimension one only; the exponential structure
(Wilkie) for composition / dim ≥ 2 stays a parked wall.

*Pre-registered falsifier* `SOFTPLUS_INSTANCE_VACUOUS` (mathlib lacks `Continuous.log` /
`Real.log_lt_log`) — CLEARED. `MONO_FRONTIER` / `BOOL_CLOSURE_LEAK` inherited-cleared
(reused core).
-/
import Sundogcert.SigmoidTame
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Sundog.OMinimalSoftplus

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-! ### The softplus activation -/

/-- The softplus activation `log(1 + eˣ)`. -/
noncomputable def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

theorem softplus_arg_pos (x : ℝ) : (0 : ℝ) < 1 + Real.exp x := by positivity

theorem softplus_continuous : Continuous softplus := by
  unfold softplus
  exact (continuous_const.add Real.continuous_exp).log fun x => (softplus_arg_pos x).ne'

theorem softplus_strictMono : StrictMono softplus := by
  intro x y hxy
  unfold softplus
  refine Real.log_lt_log (softplus_arg_pos x) ?_
  have h : Real.exp x < Real.exp y := Real.exp_lt_exp.mpr hxy
  linarith

theorem softplus_injective : Function.Injective softplus := softplus_strictMono.injective

/-! ### Softplus on an affine pre-image -/

theorem softplus_affine_continuous (a b : ℝ) :
    Continuous fun x => softplus (a * x + b) :=
  softplus_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem softplus_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => softplus (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact softplus_injective.comp haff

/-! ### The dimension-one softplus class is tame -/

theorem softplus_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | softplus (a * x + b) < r} :=
  tame_sublevel_of_injective (softplus_affine_continuous a b)
    (softplus_affine_injective ha b) r

theorem softplus_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < softplus (a * x + b)} :=
  tame_superlevel_of_injective (softplus_affine_continuous a b)
    (softplus_affine_injective ha b) r

theorem softplus_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | softplus (a * x + b) ≤ r} :=
  tame_le_of_injective (softplus_affine_continuous a b)
    (softplus_affine_injective ha b) r

theorem softplus_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ softplus (a * x + b)} :=
  tame_ge_of_injective (softplus_affine_continuous a b)
    (softplus_affine_injective ha b) r

theorem softplus_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | softplus (a * x + b) = r} :=
  tame_level_of_injective (softplus_affine_injective ha b) r

/-- A two-sided softplus band is tame (an intersection of thresholds). -/
theorem softplus_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < softplus (a * x + b) ∧ softplus (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (softplus_gt_tame ha b r₁) (softplus_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable softplus bands — a
disjunctive normal form over affine-softplus thresholds — is tame. -/
theorem softplus_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ))
    (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < softplus (s.1 * x + s.2.1) ∧
          softplus (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact softplus_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalSoftplus
