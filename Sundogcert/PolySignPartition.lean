/-
# TS-QE, TS-1: the univariate sign partition.

The first rung of Tarski–Seidenberg (route: Cohen–Hörmander, set-level over concrete ℝ).
For a finite family of nonzero real polynomials there is ONE finite cut set — the union of
the root sets — off which, on every cut-avoiding interval, each member keeps a constant
strict sign (`family_sign_partition`), hence the whole sign vector is constant
(`family_sign_eq`, the form the elimination's correctness will cite).

The real-analysis core is a single IVT argument (`poly_sign_constant`): a polynomial with no
root on an interval cannot change sign there — a change would manufacture a root by the
intermediate value theorem. This is exactly the payoff of the TS-0 route decision: over the
concrete reals the univariate substrate is analysis, not abstract real-closed-field algebra.

Also banked: `tame_zeroSet` (root sets are tame), completing R1's `polyDef_tame` picture on
the exact-sign atoms. Interface note: the cut set is a `Finset` and the clauses quantify over
cut-avoiding intervals — the same shape as the R4 ladder's `avoid_finset`/`master_refinement`
plumbing, so TS-2 composes directly.

**Honest fence.** TS-1 only: no sign matrix at the cuts, no parametric coefficients, no
elimination (TS-2a–d).
-/
import Sundogcert.OMinimalOne
import Mathlib.Topology.Order.IntermediateValue

namespace Sundog.TarskiQE

open Sundog.OMinimalOne Polynomial

/-! ### The IVT core -/

/-- **Sign constancy off roots**: a polynomial with no root on an open interval has constant
strict sign there. -/
theorem poly_sign_constant (p : ℝ[X]) {a b : ℝ}
    (hfree : ∀ x ∈ Set.Ioo a b, ¬ p.IsRoot x) :
    (∀ x ∈ Set.Ioo a b, 0 < p.eval x) ∨ (∀ x ∈ Set.Ioo a b, p.eval x < 0) := by
  by_cases hall : ∀ x ∈ Set.Ioo a b, 0 < p.eval x
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x₀, hx₀I, hx₀⟩ := hall
    have hx₀neg : p.eval x₀ < 0 :=
      lt_of_le_of_ne hx₀ (fun h => hfree x₀ hx₀I h)
    refine Or.inr fun y hyI => ?_
    by_contra hy
    have hypos : 0 < p.eval y :=
      lt_of_le_of_ne (not_lt.mp hy) (fun h => hfree y hyI h.symm)
    rcases lt_trichotomy x₀ y with hlt | rfl | hgt
    · obtain ⟨c, hcI, hc⟩ := intermediate_value_Ioo hlt.le
        (p.continuous.continuousOn) (Set.mem_Ioo.mpr ⟨hx₀neg, hypos⟩)
      exact hfree c ⟨lt_trans hx₀I.1 hcI.1, lt_trans hcI.2 hyI.2⟩ hc
    · exact absurd hypos (not_lt.mpr hx₀neg.le)
    · obtain ⟨c, hcI, hc⟩ := intermediate_value_Ioo' hgt.le
        (p.continuous.continuousOn) (Set.mem_Ioo.mpr ⟨hx₀neg, hypos⟩)
      exact hfree c ⟨lt_trans hyI.1 hcI.1, lt_trans hcI.2 hx₀I.2⟩ hc

/-! ### The family cut set -/

/-- The roots of a finite family of nonzero polynomials form a finite set. -/
theorem finite_familyRoots {F : List ℝ[X]} (hF : ∀ p ∈ F, p ≠ 0) :
    {x : ℝ | ∃ p ∈ F, p.IsRoot x}.Finite := by
  have he : {x : ℝ | ∃ p ∈ F, p.IsRoot x} = ⋃ p ∈ F, {x : ℝ | p.IsRoot x} := by
    ext x
    simp
  rw [he]
  exact Set.Finite.biUnion F.finite_toSet
    (fun p hp => Polynomial.finite_setOf_isRoot (hF p hp))

/-! ### The sign partition -/

/-- **TS-1: the univariate sign partition.** One finite cut set for the whole family, off
which each member keeps a constant strict sign on every cut-avoiding interval. -/
theorem family_sign_partition (F : List ℝ[X]) (hF : ∀ p ∈ F, p ≠ 0) :
    ∃ C : Finset ℝ, ∀ a b : ℝ, a < b → (∀ s ∈ C, s ∉ Set.Ioo a b) →
      ∀ p ∈ F, (∀ x ∈ Set.Ioo a b, 0 < p.eval x) ∨
        (∀ x ∈ Set.Ioo a b, p.eval x < 0) := by
  refine ⟨(finite_familyRoots hF).toFinset, ?_⟩
  intro a b hab havoid p hp
  apply poly_sign_constant p
  intro x hx hroot
  exact havoid x ((finite_familyRoots hF).mem_toFinset.mpr ⟨p, hp, hroot⟩) hx

/-- **Sign-vector constancy**: on a cut-avoiding interval the full sign vector of the family
is constant — the form the elimination's correctness cites. -/
theorem family_sign_eq (F : List ℝ[X]) (hF : ∀ p ∈ F, p ≠ 0) :
    ∃ C : Finset ℝ, ∀ a b : ℝ, a < b → (∀ s ∈ C, s ∉ Set.Ioo a b) →
      ∀ p ∈ F, ∀ x ∈ Set.Ioo a b, ∀ x' ∈ Set.Ioo a b,
        ((0 < p.eval x ↔ 0 < p.eval x') ∧ (p.eval x = 0 ↔ p.eval x' = 0) ∧
          (p.eval x < 0 ↔ p.eval x' < 0)) := by
  obtain ⟨C, hC⟩ := family_sign_partition F hF
  refine ⟨C, fun a b hab havoid p hp x hx x' hx' => ?_⟩
  rcases hC a b hab havoid p hp with hpos | hneg
  · exact ⟨⟨fun _ => hpos x' hx', fun _ => hpos x hx⟩,
      ⟨fun h => absurd (hpos x hx) (by rw [h]; exact lt_irrefl 0),
        fun h => absurd (hpos x' hx') (by rw [h]; exact lt_irrefl 0)⟩,
      ⟨fun h => absurd (hpos x hx) (not_lt.mpr h.le),
        fun h => absurd (hpos x' hx') (not_lt.mpr h.le)⟩⟩
  · exact ⟨⟨fun h => absurd (hneg x hx) (not_lt.mpr h.le),
        fun h => absurd (hneg x' hx') (not_lt.mpr h.le)⟩,
      ⟨fun h => absurd (hneg x hx) (by rw [h]; exact lt_irrefl 0),
        fun h => absurd (hneg x' hx') (by rw [h]; exact lt_irrefl 0)⟩,
      ⟨fun _ => hneg x' hx', fun _ => hneg x hx⟩⟩

/-! ### The exact-sign atoms are tame -/

/-- Root sets of nonzero polynomials are tame. -/
theorem tame_zeroSet {p : ℝ[X]} (hp : p ≠ 0) : Tame {x : ℝ | p.eval x = 0} := by
  have hfin : {x : ℝ | p.eval x = 0}.Finite := Polynomial.finite_setOf_isRoot hp
  unfold Tame
  refine (hfin.subset ?_)
  intro x hx
  have hcl : closure {x : ℝ | p.eval x = 0} = {x : ℝ | p.eval x = 0} :=
    hfin.isClosed.closure_eq
  rw [frontier_eq_closure_inter_closure] at hx
  rw [← hcl]
  exact hx.1

end Sundog.TarskiQE
