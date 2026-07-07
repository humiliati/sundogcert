/-
# TS-QE, TS-2c: between-roots signs — the derivative family and monotonicity.

The real-analysis input of Cohen–Hörmander: between consecutive roots of the derivative, a
polynomial is strictly monotone, so it has AT MOST ONE root there and its full sign diagram
on the interval is one of six shapes, determined by endpoint data. Combined with TS-2b
(signs AT roots via remainders) and TS-1 (the cut partition), this is everything the
elimination recursion (TS-2d) needs to reconstruct a polynomial's sign diagram from the
lower-degree family `{derivative} ∪ {remainders}`.

- **`spec_derivative`** — the parametric derivative commutes with specialization
  (mathlib's `derivative_map`): the derivative family exists parametrically.
- **`strictMonoOn_of_derivative_pos` / `strictAntiOn_of_derivative_neg`** — derivative sign
  on the open interval gives strict monotonicity on the closed one
  (`strictMonoOn_of_deriv_pos` + `Polynomial.deriv`).
- **`strictMonoOn_sign_zones` / `strictAntiOn_sign_zones`** — on a monotone interval the
  sign diagram is: all-positive, all-negative, or one interior root with clean strict-sign
  zones on both sides (endpoint trichotomy + IVT).
- **`deriv_free_sign_zones` (the capstone)** — on any interval free of derivative roots, a
  nonzero polynomial is all-positive, all-negative, or has EXACTLY the one-root two-zone
  diagram (in one of two orientations). TS-1's `poly_sign_constant` on the derivative
  picks the orientation; the constant case dies by `eq_C_of_derivative_eq_zero`.
- **End behavior** — `eventually_pos_atTop`/`eventually_neg_atTop` (leading-coefficient
  sign, via the tendsto asymptotics; constants handled separately) and the `−∞` mirrors
  with the `(−1)^deg` parity twist via `comp (−X)` and `leadingCoeff_comp`.

**Honest fence.** TS-2c only: no recursion, no correctness (2d).
-/
import Sundogcert.PseudoRemainder
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic

namespace Sundog.TarskiQE

open Polynomial

/-! ### The parametric derivative -/

variable {n : ℕ}

/-- The derivative commutes with specialization: the derivative family is parametric. -/
theorem spec_derivative (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    spec g (derivative P) = derivative (spec g P) :=
  (Polynomial.derivative_map P (MvPolynomial.eval g)).symm

/-! ### Monotonicity from derivative sign -/

theorem strictMonoOn_of_derivative_pos (p : ℝ[X]) {a b : ℝ}
    (h : ∀ x ∈ Set.Ioo a b, 0 < p.derivative.eval x) :
    StrictMonoOn (fun x => p.eval x) (Set.Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv]
  exact h x hx

theorem strictAntiOn_of_derivative_neg (p : ℝ[X]) {a b : ℝ}
    (h : ∀ x ∈ Set.Ioo a b, p.derivative.eval x < 0) :
    StrictAntiOn (fun x => p.eval x) (Set.Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) p.continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [Polynomial.deriv]
  exact h x hx

/-! ### The sign zones on a monotone interval -/

/-- On a strictly increasing interval: all-positive, all-negative, or one root with a
`(−,0,+)` diagram. -/
theorem strictMonoOn_sign_zones (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Icc a b)) :
    (∀ x ∈ Set.Ioo a b, 0 < p.eval x) ∨
    (∀ x ∈ Set.Ioo a b, p.eval x < 0) ∨
    (∃ ρ ∈ Set.Ioo a b, p.eval ρ = 0 ∧
      (∀ x ∈ Set.Ioo a ρ, p.eval x < 0) ∧ (∀ x ∈ Set.Ioo ρ b, 0 < p.eval x)) := by
  by_cases ha : 0 ≤ p.eval a
  · refine Or.inl fun x hx => ?_
    have h := hmono (Set.left_mem_Icc.mpr hab.le) ⟨hx.1.le, hx.2.le⟩ hx.1
    exact lt_of_le_of_lt ha h
  · by_cases hb : p.eval b ≤ 0
    · refine Or.inr (Or.inl fun x hx => ?_)
      have h := hmono ⟨hx.1.le, hx.2.le⟩ (Set.right_mem_Icc.mpr hab.le) hx.2
      exact lt_of_lt_of_le h hb
    · push Not at ha hb
      obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn
        (Set.mem_Ioo.mpr ⟨ha, hb⟩)
      refine Or.inr (Or.inr ⟨ρ, hρI, hρ, ?_, ?_⟩)
      · intro x hx
        have h := hmono ⟨hx.1.le, le_trans hx.2.le hρI.2.le⟩
          ⟨hρI.1.le, hρI.2.le⟩ hx.2
        exact hρ ▸ h
      · intro x hx
        have h := hmono ⟨hρI.1.le, hρI.2.le⟩
          ⟨le_trans hρI.1.le hx.1.le, hx.2.le⟩ hx.1
        exact hρ ▸ h

/-- On a strictly decreasing interval: all-positive, all-negative, or one root with a
`(+,0,−)` diagram. -/
theorem strictAntiOn_sign_zones (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Icc a b)) :
    (∀ x ∈ Set.Ioo a b, 0 < p.eval x) ∨
    (∀ x ∈ Set.Ioo a b, p.eval x < 0) ∨
    (∃ ρ ∈ Set.Ioo a b, p.eval ρ = 0 ∧
      (∀ x ∈ Set.Ioo a ρ, 0 < p.eval x) ∧ (∀ x ∈ Set.Ioo ρ b, p.eval x < 0)) := by
  by_cases ha : p.eval a ≤ 0
  · refine Or.inr (Or.inl fun x hx => ?_)
    have h := hanti (Set.left_mem_Icc.mpr hab.le) ⟨hx.1.le, hx.2.le⟩ hx.1
    exact lt_of_lt_of_le h ha
  · by_cases hb : 0 ≤ p.eval b
    · refine Or.inl fun x hx => ?_
      have h := hanti ⟨hx.1.le, hx.2.le⟩ (Set.right_mem_Icc.mpr hab.le) hx.2
      exact lt_of_le_of_lt hb h
    · push Not at ha hb
      obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn
        (Set.mem_Ioo.mpr ⟨hb, ha⟩)
      refine Or.inr (Or.inr ⟨ρ, hρI, hρ, ?_, ?_⟩)
      · intro x hx
        have h := hanti ⟨hx.1.le, le_trans hx.2.le hρI.2.le⟩
          ⟨hρI.1.le, hρI.2.le⟩ hx.2
        exact hρ ▸ h
      · intro x hx
        have h := hanti ⟨hρI.1.le, hρI.2.le⟩
          ⟨le_trans hρI.1.le hx.1.le, hx.2.le⟩ hx.1
        exact hρ ▸ h

/-! ### The capstone: derivative-root-free intervals -/

/-- **TS-2c: the between-roots diagram.** On an interval free of derivative roots, a
nonzero polynomial is all-positive, all-negative, or has exactly one interior root with
clean strict-sign zones in one of the two orientations. -/
theorem deriv_free_sign_zones (p : ℝ[X]) (hp : p ≠ 0) {a b : ℝ} (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, ¬ p.derivative.IsRoot x) :
    (∀ x ∈ Set.Ioo a b, 0 < p.eval x) ∨
    (∀ x ∈ Set.Ioo a b, p.eval x < 0) ∨
    (∃ ρ ∈ Set.Ioo a b, p.eval ρ = 0 ∧
      (((∀ x ∈ Set.Ioo a ρ, p.eval x < 0) ∧ (∀ x ∈ Set.Ioo ρ b, 0 < p.eval x)) ∨
       ((∀ x ∈ Set.Ioo a ρ, 0 < p.eval x) ∧ (∀ x ∈ Set.Ioo ρ b, p.eval x < 0)))) := by
  by_cases hd0 : p.derivative = 0
  · have hC := Polynomial.eq_C_of_derivative_eq_zero hd0
    rcases lt_trichotomy (p.coeff 0) 0 with h | h | h
    · refine Or.inr (Or.inl fun x _ => ?_)
      rw [hC, Polynomial.eval_C]
      exact h
    · exact absurd (by rw [hC, h, Polynomial.C_0]) hp
    · refine Or.inl fun x _ => ?_
      rw [hC, Polynomial.eval_C]
      exact h
  · rcases poly_sign_constant p.derivative hfree with hpos | hneg
    · rcases strictMonoOn_sign_zones p hab (strictMonoOn_of_derivative_pos p hpos)
        with h | h | ⟨ρ, hρI, hρ, hz1, hz2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨ρ, hρI, hρ, Or.inl ⟨hz1, hz2⟩⟩)
    · rcases strictAntiOn_sign_zones p hab (strictAntiOn_of_derivative_neg p hneg)
        with h | h | ⟨ρ, hρI, hρ, hz1, hz2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨ρ, hρI, hρ, Or.inr ⟨hz1, hz2⟩⟩)

/-! ### End behavior -/

/-- Positive leading coefficient: eventually positive at `+∞`. -/
theorem eventually_pos_atTop (p : ℝ[X]) (hlead : 0 < p.leadingCoeff) :
    ∃ M : ℝ, ∀ x, M < x → 0 < p.eval x := by
  by_cases hdeg : 0 < p.degree
  · have ht := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p hdeg hlead.le
    have hev := ht.eventually_gt_atTop 0
    rw [Filter.eventually_atTop] at hev
    obtain ⟨M, hM⟩ := hev
    exact ⟨M, fun x hx => hM x hx.le⟩
  · refine ⟨0, fun x _ => ?_⟩
    have hC := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    have hcoeff : p.leadingCoeff = p.coeff 0 := by
      rw [Polynomial.leadingCoeff,
        Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (not_lt.mp hdeg)]
    rw [hC, Polynomial.eval_C, ← hcoeff]
    exact hlead

/-- Negative leading coefficient: eventually negative at `+∞`. -/
theorem eventually_neg_atTop (p : ℝ[X]) (hlead : p.leadingCoeff < 0) :
    ∃ M : ℝ, ∀ x, M < x → p.eval x < 0 := by
  obtain ⟨M, hM⟩ := eventually_pos_atTop (-p)
    (by rw [Polynomial.leadingCoeff_neg]; exact neg_pos.mpr hlead)
  refine ⟨M, fun x hx => ?_⟩
  have h := hM x hx
  rw [Polynomial.eval_neg] at h
  exact neg_pos.mp h

private theorem eval_comp_neg_X (p : ℝ[X]) (x : ℝ) :
    (p.comp (-X)).eval x = p.eval (-x) := by
  rw [Polynomial.eval_comp]
  simp

private theorem leadingCoeff_comp_neg_X (p : ℝ[X]) :
    (p.comp (-X)).leadingCoeff = p.leadingCoeff * (-1) ^ p.natDegree := by
  rw [Polynomial.leadingCoeff_comp (by simp)]
  congr 1
  simp

/-- The `−∞` end, with the parity twist: sign there is `(−1)^deg ·` leading coefficient. -/
theorem eventually_pos_atBot (p : ℝ[X])
    (hlead : 0 < (-1) ^ p.natDegree * p.leadingCoeff) :
    ∃ M : ℝ, ∀ x, x < M → 0 < p.eval x := by
  obtain ⟨M, hM⟩ := eventually_pos_atTop (p.comp (-X))
    (by rw [leadingCoeff_comp_neg_X, mul_comm]; exact hlead)
  refine ⟨-M, fun x hx => ?_⟩
  have h := hM (-x) (by linarith)
  rw [eval_comp_neg_X, neg_neg] at h
  exact h

theorem eventually_neg_atBot (p : ℝ[X])
    (hlead : (-1) ^ p.natDegree * p.leadingCoeff < 0) :
    ∃ M : ℝ, ∀ x, x < M → p.eval x < 0 := by
  obtain ⟨M, hM⟩ := eventually_pos_atBot (-p) (by
    rw [Polynomial.natDegree_neg, Polynomial.leadingCoeff_neg]
    rw [mul_neg]
    exact neg_pos.mpr hlead)
  refine ⟨M, fun x hx => ?_⟩
  have h := hM x hx
  rw [Polynomial.eval_neg] at h
  exact neg_pos.mp h

end Sundog.TarskiQE
