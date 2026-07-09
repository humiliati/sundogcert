/-
# `GeluFibersFinite`, proved — closing GELU unconditionally.

The one open obligation from `GeluTame`. Route: the Rolle counting lemma
(`finite_fiber_of_finite_deriv_zeros`) applied twice. GELU is `C²` with

  `gelu''(x) = Ed(x)·(2 − x²)/2`,   `Ed(x) = (2/√π)·e^{−(x/√2)²}·(√2)⁻¹ > 0`,

so `{gelu'' = 0} = {±√2}` (needs only `exp_pos` — NO Gaussian integral, NO tail bounds).
Then `{gelu'' = 0}` finite ⇒ `{gelu' = 0}` finite ⇒ `{gelu = c}` finite.

Deliverables: `geluFibersFinite : GeluFibersFinite`, and the UNCONDITIONAL
`gelu_dnf_tame'` — GELU's dimension-one class is tame, full stop. The first non-monotone
activation closed.
-/
import Sundogcert.GeluTame
import Sundogcert.FiniteFiberRolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Sundog.OMinimalGelu

open Sundog.OMinimalErf Sundog.OMinimalFiber Sundog.OMinimalOne Sundog.OMinimalSigmoid
open MeasureTheory

/-! ### The error function's derivative (FTC) -/

private theorem gauss_cont : Continuous fun t : ℝ => Real.exp (-t ^ 2) := by fun_prop

theorem herf (x : ℝ) :
    HasDerivAt erf (2 / Real.sqrt Real.pi * Real.exp (-x ^ 2)) x := by
  have hp : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, Real.exp (-t ^ 2))
      (Real.exp (-x ^ 2)) x := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact gauss_cont.intervalIntegrable 0 x
    · exact gauss_cont.stronglyMeasurableAtFilter volume (nhds x)
    · exact gauss_cont.continuousAt
  exact HasDerivAt.const_mul (2 / Real.sqrt Real.pi) hp

/-! ### The Gaussian bump and its derivative -/

/-- `bump(x) = e^{−(x/√2)²}` — the positive factor in every GELU derivative. -/
noncomputable def bump (x : ℝ) : ℝ := Real.exp (-(x / Real.sqrt 2) ^ 2)

theorem bump_pos (x : ℝ) : 0 < bump x := Real.exp_pos _

theorem hbump (x : ℝ) : HasDerivAt bump (-x * bump x) x := by
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hdiv : HasDerivAt (fun y : ℝ => y / Real.sqrt 2) ((Real.sqrt 2)⁻¹) x := by
    simpa [one_div] using HasDerivAt.div_const (hasDerivAt_id x) (Real.sqrt 2)
  have h1 : HasDerivAt (fun y : ℝ => (y / Real.sqrt 2) ^ 2)
      (2 * (x / Real.sqrt 2) * (Real.sqrt 2)⁻¹) x := by
    simpa using HasDerivAt.pow hdiv 2
  have h2 : (2 : ℝ) * (x / Real.sqrt 2) * (Real.sqrt 2)⁻¹ = x := by
    have hinv : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := by rw [← mul_inv, hss]
    rw [div_eq_mul_inv,
      show (2 : ℝ) * (x * (Real.sqrt 2)⁻¹) * (Real.sqrt 2)⁻¹
        = 2 * x * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) by ring, hinv]
    ring
  rw [h2] at h1
  have hinner : HasDerivAt (fun y : ℝ => -(y / Real.sqrt 2) ^ 2) (-x) x := by
    simpa using HasDerivAt.neg h1
  have hcomp : HasDerivAt bump (Real.exp (-(x / Real.sqrt 2) ^ 2) * -x) x :=
    HasDerivAt.comp x (Real.hasDerivAt_exp _) hinner
  have heq : Real.exp (-(x / Real.sqrt 2) ^ 2) * -x = -x * bump x := by
    unfold bump; ring
  rwa [heq] at hcomp

/-! ### GELU's first and second derivatives -/

/-- `E(x) = erf(x/√2)` (so `Φ(x) = (1 + E(x))/2`). -/
noncomputable def E (x : ℝ) : ℝ := erf (x / Real.sqrt 2)

/-- `Ed = E'` — strictly positive. -/
noncomputable def Ed (x : ℝ) : ℝ := 2 / Real.sqrt Real.pi * bump x * (Real.sqrt 2)⁻¹

theorem Ed_pos (x : ℝ) : 0 < Ed x := by
  have hsπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold Ed
  exact mul_pos (mul_pos (div_pos (by norm_num) hsπ) (bump_pos x)) (inv_pos.mpr hs2)

theorem hE (x : ℝ) : HasDerivAt E (Ed x) x := by
  have hdiv : HasDerivAt (fun y : ℝ => y / Real.sqrt 2) ((Real.sqrt 2)⁻¹) x := by
    simpa [one_div] using HasDerivAt.div_const (hasDerivAt_id x) (Real.sqrt 2)
  have hc := HasDerivAt.comp x (herf (x / Real.sqrt 2)) hdiv
  convert hc using 1

theorem hEd (x : ℝ) : HasDerivAt Ed (-x * Ed x) x := by
  have h2 : HasDerivAt Ed
      (2 / Real.sqrt Real.pi * (-x * bump x) * (Real.sqrt 2)⁻¹) x :=
    HasDerivAt.mul_const (HasDerivAt.const_mul (2 / Real.sqrt Real.pi) (hbump x))
      ((Real.sqrt 2)⁻¹)
  have heq : 2 / Real.sqrt Real.pi * (-x * bump x) * (Real.sqrt 2)⁻¹ = -x * Ed x := by
    unfold Ed; ring
  rwa [heq] at h2

/-- `gelu' = g1`. -/
noncomputable def g1 (x : ℝ) : ℝ := (1 + E x + x * Ed x) / 2

theorem hgelu (x : ℝ) : HasDerivAt gelu (g1 x) x := by
  have hA : HasDerivAt (fun y : ℝ => 1 + E y) (Ed x) x :=
    HasDerivAt.const_add 1 (hE x)
  have hprod : HasDerivAt (fun y : ℝ => y * (1 + E y)) (1 + E x + x * Ed x) x := by
    have h := HasDerivAt.mul (hasDerivAt_id x) hA
    simp only [id_eq] at h
    convert h using 1
    ring
  exact HasDerivAt.div_const hprod 2

/-- `gelu'' = g2`. -/
noncomputable def g2 (x : ℝ) : ℝ := (Ed x + (Ed x + x * (-x * Ed x))) / 2

theorem hg1 (x : ℝ) : HasDerivAt g1 (g2 x) x := by
  have hA : HasDerivAt (fun y : ℝ => 1 + E y) (Ed x) x :=
    HasDerivAt.const_add 1 (hE x)
  have hB : HasDerivAt (fun y : ℝ => y * Ed y) (Ed x + x * (-x * Ed x)) x := by
    have h := HasDerivAt.mul (hasDerivAt_id x) (hEd x)
    simp only [id_eq] at h
    convert h using 1
    ring
  have hnum := HasDerivAt.add hA hB
  exact HasDerivAt.div_const hnum 2

/-! ### The second derivative has finitely many zeros -/

theorem g2_factor (x : ℝ) : g2 x = Ed x * (2 - x ^ 2) / 2 := by
  unfold g2; ring

theorem hg2_zero : {x : ℝ | g2 x = 0}.Finite := by
  apply Set.Finite.subset (s := {Real.sqrt 2, -Real.sqrt 2})
    ((Set.finite_singleton _).insert _)
  intro x hx
  rw [Set.mem_setOf_eq, g2_factor] at hx
  have hEdne : Ed x ≠ 0 := ne_of_gt (Ed_pos x)
  have hx2 : x ^ 2 = 2 := by
    have h : Ed x * (2 - x ^ 2) = 0 := by
      rcases div_eq_zero_iff.mp hx with h | h
      · exact h
      · norm_num at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hEdne
    · linarith
  have hss : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfac : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by nlinarith [hx2, hss]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Set.mem_insert_iff.mpr (Or.inl (sub_eq_zero.mp h1))
  · exact Set.mem_insert_iff.mpr
      (Or.inr (Set.mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h1)))

/-! ### The obligation, discharged -/

/-- **`GeluFibersFinite`, proved.** -/
theorem geluFibersFinite : GeluFibersFinite := by
  have hg1zero : {x : ℝ | g1 x = 0}.Finite :=
    finite_fiber_of_finite_deriv_zeros hg1 hg2_zero 0
  intro c
  exact finite_fiber_of_finite_deriv_zeros hgelu hg1zero c

/-! ### GELU tameness, unconditional -/

/-- **The dimension-one GELU class is tame — unconditionally.** -/
theorem gelu_dnf_tame' (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < gelu (s.1 * x + s.2.1) ∧
          gelu (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) :=
  gelu_dnf_tame geluFibersFinite specs ha

theorem gelu_lt_tame' {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu (a * x + b) < r} :=
  gelu_lt_tame geluFibersFinite ha b r

end Sundog.OMinimalGelu
