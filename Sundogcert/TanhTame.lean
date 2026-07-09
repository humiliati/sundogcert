/-
# Dimension-one tanh tameness — the second monotone-activation witness off R1.

`tanh` is the exponential activation's other standard form (`tanh = 2·σ(2·) − 1`),
equally transcendental — not reachable through the semialgebraic witness. Its
dimension-one tameness is free off R1's continuous-injective threshold core, and even
cleaner than sigmoid: mathlib supplies `Real.tanh_injective` outright, and continuity
follows from `tanh = sinh / cosh` with `cosh > 0`, so NO strict-monotonicity proof is
needed — the general core (`SigmoidTame`) asks only for continuity + injectivity.

- `tanh_continuous` + mathlib's `Real.tanh_injective` — the two facts the core needs.
- `tanh_lt_tame … tanh_eq_tame` — every one-variable affine-tanh threshold is tame.
- `tanh_band_tame`, `tanh_dnf_tame` — the class closes under finite Boolean combination.

Same fence as sigmoid: dimension one only; composition and dim ≥ 2 need the exponential
structure (`expStructure : OMinStructure`, Wilkie / Pfaffian–Khovanskii) — a parked wall.

*Pre-registered falsifier* `TANH_INSTANCE_VACUOUS` (mathlib lacks tanh continuity +
injectivity) — CLEARED: injectivity is `Real.tanh_injective`, continuity is `sinh / cosh`.
The `MONO_FRONTIER` and `BOOL_CLOSURE_LEAK` falsifiers are inherited-cleared — the core
lemmas are reused, already discharged.
-/
import Sundogcert.SigmoidTame
import Mathlib.Analysis.SpecialFunctions.Artanh

namespace Sundog.OMinimalTanh

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-! ### The two facts the threshold core needs -/

theorem tanh_continuous : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

/-! ### tanh on an affine pre-image -/

theorem tanh_affine_continuous (a b : ℝ) :
    Continuous fun x => Real.tanh (a * x + b) :=
  tanh_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem tanh_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => Real.tanh (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact Real.tanh_injective.comp haff

/-! ### The dimension-one tanh class is tame -/

theorem tanh_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | Real.tanh (a * x + b) < r} :=
  tame_sublevel_of_injective (tanh_affine_continuous a b)
    (tanh_affine_injective ha b) r

theorem tanh_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < Real.tanh (a * x + b)} :=
  tame_superlevel_of_injective (tanh_affine_continuous a b)
    (tanh_affine_injective ha b) r

theorem tanh_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | Real.tanh (a * x + b) ≤ r} :=
  tame_le_of_injective (tanh_affine_continuous a b)
    (tanh_affine_injective ha b) r

theorem tanh_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ Real.tanh (a * x + b)} :=
  tame_ge_of_injective (tanh_affine_continuous a b)
    (tanh_affine_injective ha b) r

theorem tanh_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | Real.tanh (a * x + b) = r} :=
  tame_level_of_injective (tanh_affine_injective ha b) r

/-- A two-sided tanh band is tame (an intersection of thresholds). -/
theorem tanh_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < Real.tanh (a * x + b) ∧ Real.tanh (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (tanh_gt_tame ha b r₁) (tanh_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable tanh bands — a disjunctive
normal form over affine-tanh thresholds — is tame. -/
theorem tanh_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ))
    (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < Real.tanh (s.1 * x + s.2.1) ∧
          Real.tanh (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact tanh_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalTanh
