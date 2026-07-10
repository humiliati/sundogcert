/-
# Dimension-one GELU-sigmoid approximation tameness.

`gelu_sigmoid(x) = x·σ(k·x)`, `k = 1.702` — the sigmoid approximation of GELU (a
scaled-argument SiLU). Non-monotone (Rolle route), and the cleanest instance: the
SiLU-style transform gives

  `gelu_sigmoid(x) = C  ⟺  (x − C)·e^{k x} = C`,

and `g_C(x) = (x − C)e^{k x}` has `g_C' = e^{k x}·(1 + k(x − C))`, whose zero set is the
SINGLE point `{C − 1/k}` (the critical equation is LINEAR, even simpler than SiLU's). One
Rolle step gives `{gelu_sigmoid = C}` finite — `gelu_sigmoid_dnf_tame`, unconditional.

*Pre-registered falsifier* `GELU_SIGMOID_LINEAR_CRITICAL` (the transformed critical equation
is linear, single root) — cleared.
-/
import Sundogcert.FiniteFiberRolle
import Sundogcert.FiniteFiberTame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Sundog.OMinimalGeluSigmoid

open Sundog.OMinimalOne Sundog.OMinimalFiber Sundog.OMinimalSigmoid

/-- The GELU sigmoid-approximation scale `k = 1.702`. -/
def gsk : ℝ := 1.702

theorem gsk_pos : 0 < gsk := by unfold gsk; norm_num

/-- The sigmoid approximation of GELU `gelu_sigmoid(x) = x·σ(k·x)`. -/
noncomputable def gelu_sigmoid (x : ℝ) : ℝ := x * sigmoid (gsk * x)

theorem gelu_sigmoid_continuous : Continuous gelu_sigmoid :=
  continuous_id.mul (sigmoid_continuous.comp (continuous_const.mul continuous_id))

/-- **The equation transform.** `gelu_sigmoid(x) = C` iff `(x − C)·e^{k x} = C`. -/
theorem gelu_sigmoid_eq_iff (C x : ℝ) :
    gelu_sigmoid x = C ↔ (x - C) * Real.exp (gsk * x) = C := by
  have hepos : (0 : ℝ) < Real.exp (gsk * x) := Real.exp_pos _
  have hkey : gelu_sigmoid x
      = x * Real.exp (gsk * x) / (Real.exp (gsk * x) + 1) := by
    unfold gelu_sigmoid sigmoid
    rw [Real.exp_neg]
    field_simp
  rw [hkey, div_eq_iff (by positivity : Real.exp (gsk * x) + 1 ≠ 0)]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- The transformed function's derivative, with its single critical point. -/
theorem hgc (C x : ℝ) :
    HasDerivAt (fun y => (y - C) * Real.exp (gsk * y))
      ((1 + gsk * (x - C)) * Real.exp (gsk * x)) x := by
  have hexp := HasDerivAt.comp x (Real.hasDerivAt_exp (gsk * x))
    (HasDerivAt.const_mul gsk (hasDerivAt_id x))
  have hsub : HasDerivAt (fun y : ℝ => y - C) 1 x := HasDerivAt.sub_const C (hasDerivAt_id x)
  have h := HasDerivAt.mul hsub hexp
  convert h using 1
  simp only [Function.comp_apply]
  ring

theorem gc_zeros (C : ℝ) :
    {x : ℝ | (1 + gsk * (x - C)) * Real.exp (gsk * x) = 0}.Finite := by
  apply Set.Finite.subset (Set.finite_singleton (C - gsk⁻¹))
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  rcases mul_eq_zero.mp hx with h | h
  · rw [Set.mem_singleton_iff]
    have hgsk : gsk ≠ 0 := ne_of_gt gsk_pos
    field_simp
    linear_combination h
  · exact absurd h (Real.exp_ne_zero _)

theorem geluSigmoidFibersFinite (C : ℝ) : {x : ℝ | gelu_sigmoid x = C}.Finite := by
  have hset : {x : ℝ | gelu_sigmoid x = C}
      = {x : ℝ | (x - C) * Real.exp (gsk * x) = C} := by
    ext x; simp only [Set.mem_setOf_eq, gelu_sigmoid_eq_iff]
  rw [hset]
  exact finite_fiber_of_finite_deriv_zeros (fun x => hgc C x) (gc_zeros C) C

theorem gelu_sigmoid_affine_fiber_finite {a : ℝ} (ha : a ≠ 0) (b C : ℝ) :
    {x : ℝ | gelu_sigmoid (a * x + b) = C}.Finite := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  have e : {x : ℝ | gelu_sigmoid (a * x + b) = C}
      = (fun x => a * x + b) ⁻¹' {y | gelu_sigmoid y = C} := rfl
  rw [e]
  exact (geluSigmoidFibersFinite C).preimage haff.injOn

/-! ### The dimension-one GELU-sigmoid class is tame -/

theorem gelu_sigmoid_affine_continuous (a b : ℝ) :
    Continuous fun x => gelu_sigmoid (a * x + b) :=
  gelu_sigmoid_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem gelu_sigmoid_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu_sigmoid (a * x + b) < r} :=
  tame_sublevel_of_finite (gelu_sigmoid_affine_continuous a b)
    (gelu_sigmoid_affine_fiber_finite ha b r)

theorem gelu_sigmoid_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < gelu_sigmoid (a * x + b)} :=
  tame_superlevel_of_finite (gelu_sigmoid_affine_continuous a b)
    (gelu_sigmoid_affine_fiber_finite ha b r)

theorem gelu_sigmoid_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu_sigmoid (a * x + b) ≤ r} :=
  tame_le_of_finite (gelu_sigmoid_affine_continuous a b)
    (gelu_sigmoid_affine_fiber_finite ha b r)

theorem gelu_sigmoid_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ gelu_sigmoid (a * x + b)} :=
  tame_ge_of_finite (gelu_sigmoid_affine_continuous a b)
    (gelu_sigmoid_affine_fiber_finite ha b r)

theorem gelu_sigmoid_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu_sigmoid (a * x + b) = r} :=
  tame_level_of_finite (gelu_sigmoid_affine_fiber_finite ha b r)

/-- A two-sided GELU-sigmoid band is tame. -/
theorem gelu_sigmoid_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < gelu_sigmoid (a * x + b) ∧ gelu_sigmoid (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (gelu_sigmoid_gt_tame ha b r₁) (gelu_sigmoid_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable GELU-sigmoid bands is tame. -/
theorem gelu_sigmoid_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < gelu_sigmoid (s.1 * x + s.2.1) ∧
          gelu_sigmoid (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact gelu_sigmoid_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalGeluSigmoid
