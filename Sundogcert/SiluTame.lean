/-
# Dimension-one SiLU/swish tameness — the second non-monotone activation.

`silu(x) = x·σ(x) = x/(1 + e^{-x})` — non-monotone (a minimum near `x ≈ −1.28`), like
GELU. But the GELU trick does NOT transfer: differentiating GELU introduces
polynomial-in-`x` factors (`φ' = −xφ`), so `gelu'' = φ·(2 − x²)` clears to a polynomial.
SiLU's sigmoid gives `σ' = σ(1 − σ)` — polynomial in `σ`, not in `x` — so
`silu'' = σ(1−σ)·(2 + x(1 − 2σ))` stays TRANSCENDENTAL at every derivative level. The
direct "differentiate to a polynomial" route stalls.

The Rolle ENGINE still closes it, via an equation transform:

  `silu(x) = c  ⟺  (x − c)·eˣ = c`,

and `g_c(x) = (x − c)·eˣ` has a SINGLE critical point (`g_c' = (x − c + 1)·eˣ`, zero only
at `x = c − 1`). So ONE application of `finite_fiber_of_finite_deriv_zeros` gives
`{silu = c}` finite — hence `silu_dnf_tame`, unconditional.

*Pre-registered falsifiers*: `SILU_DERIV_NONPOLY` (silu's derivatives don't clear to a
polynomial — CONFIRMED, hence the transform) and `SILU_TRANSFORM_FINITE` (the transform +
one counting step closes fibers) — cleared.
-/
import Sundogcert.FiniteFiberRolle
import Sundogcert.FiniteFiberTame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Sundog.OMinimalSilu

open Sundog.OMinimalOne Sundog.OMinimalFiber Sundog.OMinimalSigmoid

/-! ### SiLU / swish -/

/-- The SiLU / swish activation `silu(x) = x·σ(x)`. -/
noncomputable def silu (x : ℝ) : ℝ := x * sigmoid x

theorem silu_continuous : Continuous silu := continuous_id.mul sigmoid_continuous

/-- **The equation transform.** `silu(x) = c` iff `(x − c)·eˣ = c`. -/
theorem silu_eq_iff (c x : ℝ) : silu x = c ↔ (x - c) * Real.exp x = c := by
  have hepos : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hkey : silu x = x * Real.exp x / (Real.exp x + 1) := by
    unfold silu sigmoid
    rw [Real.exp_neg]
    field_simp
  rw [hkey, div_eq_iff (by positivity : Real.exp x + 1 ≠ 0)]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-! ### The transformed function has a single critical point -/

theorem hgc (c x : ℝ) :
    HasDerivAt (fun y => (y - c) * Real.exp y) ((x - c + 1) * Real.exp x) x := by
  have hsub : HasDerivAt (fun y : ℝ => y - c) 1 x := HasDerivAt.sub_const c (hasDerivAt_id x)
  have h := HasDerivAt.mul hsub (Real.hasDerivAt_exp x)
  convert h using 1
  ring

theorem gc_zeros (c : ℝ) : {x : ℝ | (x - c + 1) * Real.exp x = 0}.Finite := by
  apply Set.Finite.subset (Set.finite_singleton (c - 1))
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  rcases mul_eq_zero.mp hx with h | h
  · rw [Set.mem_singleton_iff]; linarith
  · exact absurd h (Real.exp_ne_zero x)

/-! ### Fibers finite -/

/-- **SiLU's level sets are finite** — via the transform and one Rolle-counting step. -/
theorem siluFibersFinite (c : ℝ) : {x : ℝ | silu x = c}.Finite := by
  have hset : {x : ℝ | silu x = c} = {x : ℝ | (x - c) * Real.exp x = c} := by
    ext x; simp only [Set.mem_setOf_eq, silu_eq_iff]
  rw [hset]
  exact finite_fiber_of_finite_deriv_zeros (fun x => hgc c x) (gc_zeros c) c

theorem silu_affine_fiber_finite {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    {x : ℝ | silu (a * x + b) = c}.Finite := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  have e : {x : ℝ | silu (a * x + b) = c} = (fun x => a * x + b) ⁻¹' {y | silu y = c} := rfl
  rw [e]
  exact (siluFibersFinite c).preimage haff.injOn

/-! ### The dimension-one SiLU class is tame — unconditionally -/

theorem silu_affine_continuous (a b : ℝ) : Continuous fun x => silu (a * x + b) :=
  silu_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem silu_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | silu (a * x + b) < r} :=
  tame_sublevel_of_finite (silu_affine_continuous a b) (silu_affine_fiber_finite ha b r)

theorem silu_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < silu (a * x + b)} :=
  tame_superlevel_of_finite (silu_affine_continuous a b) (silu_affine_fiber_finite ha b r)

theorem silu_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | silu (a * x + b) ≤ r} :=
  tame_le_of_finite (silu_affine_continuous a b) (silu_affine_fiber_finite ha b r)

theorem silu_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ silu (a * x + b)} :=
  tame_ge_of_finite (silu_affine_continuous a b) (silu_affine_fiber_finite ha b r)

theorem silu_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | silu (a * x + b) = r} :=
  tame_level_of_finite (silu_affine_fiber_finite ha b r)

/-- A two-sided SiLU band is tame. -/
theorem silu_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < silu (a * x + b) ∧ silu (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (silu_gt_tame ha b r₁) (silu_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable SiLU bands is tame. -/
theorem silu_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < silu (s.1 * x + s.2.1) ∧
          silu (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact silu_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalSilu
