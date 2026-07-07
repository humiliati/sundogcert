/-
# TS-QE, TS-2a: branch trees — the parametric machinery.

Polynomials in one distinguished variable with coefficients that are polynomials in the
parameters: `Polynomial (MvPolynomial (Fin n) ℝ)`, connected to `MvPolynomial (Fin (n+1)) ℝ`
by mathlib's `finSuccEquiv` (first variable distinguished; the last-variable form our
`OMinStructure` projection uses is recovered by a rename at TS-3 — noted, not needed here).

- **`spec g`** — specialize the parameters: map every coefficient through
  `MvPolynomial.eval g`. The bridge `spec_eval_cons` (mathlib's `eval_eq_eval_mv_eval'`)
  turns evaluation of an `(n+1)`-variate polynomial at `Fin.cons y g` into evaluation of the
  specialized univariate polynomial at `y`.
- **`resolve g`** — the branch-tree truncation: strip leading coefficients while they vanish
  at `g` (well-founded on the support size). `resolve_spec`: truncation does not change the
  specialization. `resolve_faithful`: the result is zero or has non-vanishing leading
  coefficient — so specialization is degree-exact on resolved polynomials
  (`spec_natDegree_eq`, `spec_eq_zero_iff`, `spec_leadingCoeff_eq`): the parametric degree
  bookkeeping that the elimination recursion (TS-2d) case-splits on.
- **`truncChain`** — the finite chain `P, P.eraseLead, …, 0` that `resolve g P` always lands
  in (`resolve_mem_truncChain`), with the compositional branch conditions
  (`resolve_eq_self_iff`, `resolve_of_lead_vanish`) from which TS-2d builds each branch's
  polynomial (non)vanishing conditions.
- **The measure** — `famDegrees` (the multiset of `y`-degrees); mathlib's Dershowitz–Manna
  order (`Multiset.instWellFoundedIsDershowitzMannaLT`) is the pre-registered well-founded
  measure for the elimination recursion.

**Honest fence.** TS-2a only: no sign matrix (2b), no between-roots analysis (2c), no
elimination (2d).
-/
import Sundogcert.PolySignPartition
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Data.Multiset.DershowitzManna

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Specialization -/

/-- Specialize the parameters: evaluate every coefficient at `g`. -/
noncomputable def spec (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Polynomial ℝ :=
  P.map (MvPolynomial.eval g)

/-- The `finSuccEquiv` bridge: evaluating an `(n+1)`-variate polynomial at `Fin.cons y g`
is evaluating its specialized head-form at `y`. -/
theorem spec_eval_cons (g : Fin n → ℝ) (y : ℝ) (f : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.eval (Fin.cons y g) f
      = (spec g (MvPolynomial.finSuccEquiv ℝ n f)).eval y :=
  MvPolynomial.eval_eq_eval_mv_eval' g y f

/-! ### The branch-tree truncation -/

/-- Strip leading coefficients while they vanish at `g`. -/
noncomputable def resolve (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Polynomial (MvPolynomial (Fin n) ℝ) :=
  if _hP : P = 0 then 0
  else if MvPolynomial.eval g P.leadingCoeff = 0 then resolve g P.eraseLead
  else P
termination_by P.support.card
decreasing_by exact Polynomial.eraseLead_support_card_lt _hP

private theorem resolve_unfold (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    resolve g P =
      if _hP : P = 0 then 0
      else if MvPolynomial.eval g P.leadingCoeff = 0 then resolve g P.eraseLead
      else P := by
  rw [resolve]

/-- The reusable case principle for `resolve`-facts. -/
private theorem resolve_cases (g : Fin n → ℝ)
    (motive : Polynomial (MvPolynomial (Fin n) ℝ) →
      Polynomial (MvPolynomial (Fin n) ℝ) → Prop)
    (hzero : motive 0 0)
    (hkeep : ∀ P, P ≠ 0 → MvPolynomial.eval g P.leadingCoeff ≠ 0 → motive P P)
    (hdrop : ∀ P, P ≠ 0 → MvPolynomial.eval g P.leadingCoeff = 0 →
      motive P.eraseLead (resolve g P.eraseLead) → motive P (resolve g P.eraseLead)) :
    ∀ P, motive P (resolve g P) := by
  suffices H : ∀ (N : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℝ)),
      P.support.card ≤ N → motive P (resolve g P) by
    exact fun P => H P.support.card P le_rfl
  intro N
  induction N with
  | zero =>
    intro P hP
    have h0 : P = 0 := by
      rw [← Polynomial.support_eq_empty, ← Finset.card_eq_zero]
      omega
    subst h0
    rw [resolve_unfold, dif_pos rfl]
    exact hzero
  | succ N ih =>
    intro P hP
    by_cases h0 : P = 0
    · subst h0
      rw [resolve_unfold, dif_pos rfl]
      exact hzero
    · rw [resolve_unfold, dif_neg h0]
      by_cases hl : MvPolynomial.eval g P.leadingCoeff = 0
      · rw [if_pos hl]
        refine hdrop P h0 hl (ih P.eraseLead ?_)
        have := Polynomial.eraseLead_support_card_lt h0
        omega
      · rw [if_neg hl]
        exact hkeep P h0 hl

/-- Truncation does not change the specialization. -/
theorem spec_eraseLead_of_lead_vanish (g : Fin n → ℝ)
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (h : MvPolynomial.eval g P.leadingCoeff = 0) :
    spec g P.eraseLead = spec g P := by
  conv_rhs => rw [← Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff P]
  rw [spec, spec, Polynomial.map_add, Polynomial.map_monomial, h,
    Polynomial.monomial_zero_right, add_zero]

/-- **`resolve` preserves the specialization.** -/
theorem resolve_spec (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    spec g (resolve g P) = spec g P := by
  refine resolve_cases g (fun P R => spec g R = spec g P) rfl (fun P _ _ => rfl) ?_ P
  intro P hP hl ih
  rw [ih]
  exact spec_eraseLead_of_lead_vanish g P hl

/-- **The resolved polynomial is zero or degree-faithful at `g`.** -/
theorem resolve_faithful (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    resolve g P = 0 ∨ MvPolynomial.eval g (resolve g P).leadingCoeff ≠ 0 := by
  refine resolve_cases g
    (fun _ R => R = 0 ∨ MvPolynomial.eval g R.leadingCoeff ≠ 0)
    (Or.inl rfl) (fun P _ hl => Or.inr hl) (fun P _ _ ih => ih) P

theorem resolve_natDegree_le (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    (resolve g P).natDegree ≤ P.natDegree := by
  refine resolve_cases g (fun P R => R.natDegree ≤ P.natDegree)
    le_rfl (fun _ _ _ => le_rfl) ?_ P
  intro P hP _ ih
  exact le_trans ih (le_trans (Polynomial.eraseLead_natDegree_le P) (Nat.sub_le _ _))

/-! ### Degree-exactness of specialization -/

/-- The specialization vanishes exactly when the resolution does. -/
theorem spec_eq_zero_iff (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    spec g P = 0 ↔ resolve g P = 0 := by
  rw [← resolve_spec g P]
  rcases resolve_faithful g P with h0 | hl
  · rw [h0]
    simp [spec]
  · constructor
    · intro h
      by_contra hR
      have hcoeff : (spec g (resolve g P)).coeff (resolve g P).natDegree
          = MvPolynomial.eval g (resolve g P).leadingCoeff := by
        rw [spec, Polynomial.coeff_map]
        rfl
      rw [h] at hcoeff
      simp at hcoeff
      exact hl hcoeff.symm
    · intro h
      rw [h]
      simp [spec]

/-- **Specialization is degree-exact on the resolution.** -/
theorem spec_natDegree_eq (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    (spec g P).natDegree = (resolve g P).natDegree := by
  rw [← resolve_spec g P]
  rcases resolve_faithful g P with h0 | hl
  · rw [h0]
    simp [spec]
  · exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hl

/-- The specialized leading coefficient is the evaluated resolved leading coefficient. -/
theorem spec_leadingCoeff_eq (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    (spec g P).leadingCoeff = MvPolynomial.eval g (resolve g P).leadingCoeff := by
  rw [← resolve_spec g P]
  rcases resolve_faithful g P with h0 | hl
  · rw [h0]
    simp [spec]
  · rw [spec, Polynomial.leadingCoeff, Polynomial.coeff_map,
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hl]
    rfl

/-! ### The truncation chain and the branch conditions -/

/-- The finite chain of truncations `P, P.eraseLead, …, 0`. -/
noncomputable def truncChain (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    List (Polynomial (MvPolynomial (Fin n) ℝ)) :=
  if _hP : P = 0 then [0] else P :: truncChain P.eraseLead
termination_by P.support.card
decreasing_by exact Polynomial.eraseLead_support_card_lt _hP

private theorem truncChain_unfold (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    truncChain P = if _hP : P = 0 then [0] else P :: truncChain P.eraseLead := by
  rw [truncChain]

/-- Every branch lands in the chain. -/
theorem resolve_mem_truncChain (g : Fin n → ℝ)
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) : resolve g P ∈ truncChain P := by
  refine resolve_cases g (fun P R => R ∈ truncChain P) ?_ ?_ ?_ P
  · change (0 : Polynomial (MvPolynomial (Fin n) ℝ)) ∈ truncChain 0
    rw [truncChain_unfold, dif_pos rfl]
    exact List.mem_singleton.mpr rfl
  · intro P hP _
    change P ∈ truncChain P
    rw [truncChain_unfold, dif_neg hP]
    exact List.mem_cons_self
  · intro P hP _ ih
    change resolve g P.eraseLead ∈ truncChain P
    rw [truncChain_unfold, dif_neg hP]
    exact List.mem_cons_of_mem _ ih

/-- Chain members do not exceed the head degree. -/
theorem truncChain_natDegree_le (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∀ Q ∈ truncChain P, Q.natDegree ≤ P.natDegree := by
  suffices H : ∀ (N : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℝ)),
      P.support.card ≤ N → ∀ Q ∈ truncChain P, Q.natDegree ≤ P.natDegree by
    exact H P.support.card P le_rfl
  intro N
  induction N with
  | zero =>
    intro P hP Q hQ
    have h0 : P = 0 := by
      rw [← Polynomial.support_eq_empty, ← Finset.card_eq_zero]
      omega
    subst h0
    rw [truncChain_unfold, dif_pos rfl, List.mem_singleton] at hQ
    subst hQ
    exact le_rfl
  | succ N ih =>
    intro P hP Q hQ
    by_cases h0 : P = 0
    · subst h0
      rw [truncChain_unfold, dif_pos rfl, List.mem_singleton] at hQ
      subst hQ
      exact le_rfl
    · rw [truncChain_unfold, dif_neg h0, List.mem_cons] at hQ
      rcases hQ with rfl | hQ
      · exact le_rfl
      · have hcard := Polynomial.eraseLead_support_card_lt h0
        exact le_trans (ih P.eraseLead (by omega) Q hQ)
          (le_trans (Polynomial.eraseLead_natDegree_le P) (Nat.sub_le _ _))

/-- Branch condition, base form: the branch keeps `P` iff `P` is zero or its leading
coefficient survives at `g`. -/
theorem resolve_eq_self_iff (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    resolve g P = P ↔ (P = 0 ∨ MvPolynomial.eval g P.leadingCoeff ≠ 0) := by
  constructor
  · intro h
    rcases resolve_faithful g P with h0 | hl
    · exact Or.inl (h ▸ h0)
    · exact Or.inr (by rw [← h]; exact hl)
  · rintro (rfl | hl)
    · rw [resolve_unfold, dif_pos rfl]
    · rw [resolve_unfold]
      by_cases h0 : P = 0
      · rw [dif_pos h0, h0]
      · rw [dif_neg h0, if_neg hl]

/-- Branch condition, step form: a vanishing leading coefficient descends the chain. -/
theorem resolve_of_lead_vanish (g : Fin n → ℝ) {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (h0 : P ≠ 0) (hl : MvPolynomial.eval g P.leadingCoeff = 0) :
    resolve g P = resolve g P.eraseLead := by
  rw [resolve_unfold, dif_neg h0, if_pos hl]

/-! ### The elimination measure -/

/-- The multiset of head-variable degrees — the Dershowitz–Manna measure the elimination
recursion (TS-2d) will descend on (`Multiset.instWellFoundedIsDershowitzMannaLT`). -/
noncomputable def famDegrees (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) : Multiset ℕ :=
  (F.map Polynomial.natDegree : List ℕ)

end Sundog.TarskiQE
