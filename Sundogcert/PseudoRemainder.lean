/-
# TS-QE, TS-2b: the mod-trick — sign transfer at roots.

The elimination determines signs of a family at the roots of a member `P` by replacing each
`Q` with a remainder of `y`-degree `< deg P`. Over the parametric coefficient ring
(no division!) this is **pseudo-division**: `c^k · Q = S · P + rem` with `c = P`'s leading
coefficient — built here from scratch (mathlib has none), generic over any `CommRing`:

- **`pstep`** — one cancellation step `C c · Q − C (lead Q) · X^d · P`; the top coefficients
  cancel exactly (`pstep_coeff_eq_zero`), no domain hypothesis needed.
- **`pseudoModExp`** — the recursion (well-founded on a zero-guarded degree measure), with
  the identity `∃ S, C c ^ k · Q = S · P + rem` (`pseudoModExp_identity`) and the degree
  guard `rem = 0 ∨ deg rem < deg P` (`pseudoModExp_rem`).
- **`emod`/`eexp` — the even-exponent trick**: pad `k` to even by one more `C c` factor, so
  the transfer factor `c(g)^k` is strictly positive on the live branch — the sign twist
  bookkeeping of classical Cohen–Hörmander disappears entirely.

Then specialize (TS-2a's `spec`) and evaluate at a root `ρ` of `spec g P`: the `S · P` term
dies and (`emod_eval_at_root`)
`(spec g (emod P Q)).eval ρ = c(g)^k · (spec g Q).eval ρ` — whence **`sign_transfer`**: on
the branch where `P`'s leading coefficient survives at `g`, the full three-way sign of any
`Q` at any root of `spec g P` equals that of its evenized pseudo-remainder, a polynomial of
strictly smaller `y`-degree. This is the elimination's degree-descent engine.

**Honest fence.** TS-2b only: no between-roots analysis (2c), no recursion (2d).
-/
import Sundogcert.PolyBranchTrees

namespace Sundog.TarskiQE

open Polynomial

/-! ### Pseudo-division over a commutative ring -/

section PseudoDivision

variable {R : Type*} [CommRing R]

/-- One pseudo-division step: multiply by the divisor's leading coefficient and cancel the
top term. -/
noncomputable def pstep (P Q : R[X]) : R[X] :=
  C P.leadingCoeff * Q - C Q.leadingCoeff * (X ^ (Q.natDegree - P.natDegree) * P)

theorem pstep_coeff_eq_zero (P Q : R[X]) (hdeg : P.natDegree ≤ Q.natDegree) :
    ∀ m : ℕ, Q.natDegree ≤ m → (pstep P Q).coeff m = 0 := by
  intro m hm
  rw [pstep, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  rcases eq_or_lt_of_le hm with heq | hlt
  · rw [if_pos (by omega)]
    have h1 : m - (Q.natDegree - P.natDegree) = P.natDegree := by omega
    rw [h1, ← heq, Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]
    ring
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, if_pos (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : P.natDegree < m - (Q.natDegree - P.natDegree))]
    ring

theorem pstep_degree (P Q : R[X]) (hdeg : P.natDegree ≤ Q.natDegree) :
    pstep P Q = 0 ∨ (pstep P Q).natDegree < Q.natDegree := by
  by_cases h0 : pstep P Q = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Polynomial.natDegree_lt_iff_degree_lt h0,
      Polynomial.degree_lt_iff_coeff_zero]
    exact pstep_coeff_eq_zero P Q hdeg

open Classical in
/-- Pseudo-division: the exponent and the remainder. The quotient is existential
(`pseudoModExp_identity`). -/
noncomputable def pseudoModExp (P Q : R[X]) : ℕ × R[X] :=
  if _hQ0 : Q = 0 then (0, 0)
  else if _hdeg : Q.natDegree < P.natDegree then (0, Q)
  else ((pseudoModExp P (pstep P Q)).1 + 1, (pseudoModExp P (pstep P Q)).2)
termination_by if Q = 0 then 0 else Q.natDegree + 1
decreasing_by
  all_goals {
    have hm := pstep_degree P Q (not_lt.mp _hdeg)
    by_cases hps : pstep P Q = 0
    · rw [if_pos hps, if_neg _hQ0]
      omega
    · rw [if_neg hps, if_neg _hQ0]
      rcases hm with h0 | hlt
      · exact absurd h0 hps
      · omega
  }

open Classical in
private theorem pseudoModExp_unfold (P Q : R[X]) :
    pseudoModExp P Q =
      if _hQ0 : Q = 0 then (0, 0)
      else if _hdeg : Q.natDegree < P.natDegree then (0, Q)
      else ((pseudoModExp P (pstep P Q)).1 + 1, (pseudoModExp P (pstep P Q)).2) := by
  rw [pseudoModExp]

/-- **The pseudo-division identity**: `c^k · Q = S · P + rem`. -/
theorem pseudoModExp_identity (P : R[X]) : ∀ Q : R[X],
    ∃ S : R[X], C P.leadingCoeff ^ (pseudoModExp P Q).1 * Q
      = S * P + (pseudoModExp P Q).2 := by
  classical
  suffices H : ∀ (N : ℕ) (Q : R[X]), (if Q = 0 then 0 else Q.natDegree + 1) ≤ N →
      ∃ S : R[X], C P.leadingCoeff ^ (pseudoModExp P Q).1 * Q
        = S * P + (pseudoModExp P Q).2 by
    exact fun Q => H _ Q le_rfl
  intro N
  induction N with
  | zero =>
    intro Q hQ
    have hQ0 : Q = 0 := by
      by_contra h
      rw [if_neg h] at hQ
      omega
    subst hQ0
    rw [pseudoModExp_unfold, dif_pos rfl]
    exact ⟨0, by simp⟩
  | succ N ih =>
    intro Q hQ
    rw [pseudoModExp_unfold]
    by_cases hQ0 : Q = 0
    · rw [dif_pos hQ0]
      subst hQ0
      exact ⟨0, by simp⟩
    rw [dif_neg hQ0]
    by_cases hdeg : Q.natDegree < P.natDegree
    · rw [dif_pos hdeg]
      exact ⟨0, by simp⟩
    · rw [dif_neg hdeg]
      have hmeas : (if pstep P Q = 0 then 0 else (pstep P Q).natDegree + 1) ≤ N := by
        rw [if_neg hQ0] at hQ
        have hm := pstep_degree P Q (not_lt.mp hdeg)
        by_cases hps : pstep P Q = 0
        · rw [if_pos hps]
          omega
        · rw [if_neg hps]
          rcases hm with h0 | hlt
          · exact absurd h0 hps
          · omega
      obtain ⟨S', hS'⟩ := ih (pstep P Q) hmeas
      refine ⟨S' + C P.leadingCoeff ^ (pseudoModExp P (pstep P Q)).1 *
        (C Q.leadingCoeff * X ^ (Q.natDegree - P.natDegree)), ?_⟩
      have hdef : pstep P Q
          = C P.leadingCoeff * Q
            - C Q.leadingCoeff * (X ^ (Q.natDegree - P.natDegree) * P) := rfl
      rw [pow_succ]
      linear_combination hS' - C P.leadingCoeff ^ (pseudoModExp P (pstep P Q)).1 * hdef

/-- The remainder degree guard. -/
theorem pseudoModExp_rem (P : R[X]) : ∀ Q : R[X],
    (pseudoModExp P Q).2 = 0 ∨ ((pseudoModExp P Q).2).natDegree < P.natDegree := by
  classical
  suffices H : ∀ (N : ℕ) (Q : R[X]), (if Q = 0 then 0 else Q.natDegree + 1) ≤ N →
      (pseudoModExp P Q).2 = 0 ∨ ((pseudoModExp P Q).2).natDegree < P.natDegree by
    exact fun Q => H _ Q le_rfl
  intro N
  induction N with
  | zero =>
    intro Q hQ
    have hQ0 : Q = 0 := by
      by_contra h
      rw [if_neg h] at hQ
      omega
    subst hQ0
    rw [pseudoModExp_unfold, dif_pos rfl]
    exact Or.inl rfl
  | succ N ih =>
    intro Q hQ
    rw [pseudoModExp_unfold]
    by_cases hQ0 : Q = 0
    · rw [dif_pos hQ0]
      exact Or.inl rfl
    rw [dif_neg hQ0]
    by_cases hdeg : Q.natDegree < P.natDegree
    · rw [dif_pos hdeg]
      exact Or.inr hdeg
    · rw [dif_neg hdeg]
      have hmeas : (if pstep P Q = 0 then 0 else (pstep P Q).natDegree + 1) ≤ N := by
        rw [if_neg hQ0] at hQ
        have hm := pstep_degree P Q (not_lt.mp hdeg)
        by_cases hps : pstep P Q = 0
        · rw [if_pos hps]
          omega
        · rw [if_neg hps]
          rcases hm with h0 | hlt
          · exact absurd h0 hps
          · omega
      exact ih (pstep P Q) hmeas

/-! ### The even-exponent trick -/

open Classical in
/-- The evenized pseudo-remainder. -/
noncomputable def emod (P Q : R[X]) : R[X] :=
  if Even (pseudoModExp P Q).1 then (pseudoModExp P Q).2
  else C P.leadingCoeff * (pseudoModExp P Q).2

open Classical in
/-- The evenized exponent. -/
noncomputable def eexp (P Q : R[X]) : ℕ :=
  if Even (pseudoModExp P Q).1 then (pseudoModExp P Q).1 else (pseudoModExp P Q).1 + 1

theorem eexp_even (P Q : R[X]) : Even (eexp P Q) := by
  rw [eexp]
  split_ifs with h
  · exact h
  · exact Nat.even_add_one.mpr h

/-- The evenized identity. -/
theorem emod_identity (P Q : R[X]) :
    ∃ S : R[X], C P.leadingCoeff ^ eexp P Q * Q = S * P + emod P Q := by
  obtain ⟨S, hS⟩ := pseudoModExp_identity P Q
  rw [emod, eexp]
  split_ifs with h
  · exact ⟨S, hS⟩
  · refine ⟨C P.leadingCoeff * S, ?_⟩
    rw [pow_succ]
    linear_combination C P.leadingCoeff * hS

/-- The evenized remainder keeps the degree guard. -/
theorem emod_rem (P Q : R[X]) :
    emod P Q = 0 ∨ (emod P Q).natDegree < P.natDegree := by
  rcases pseudoModExp_rem P Q with h0 | hlt
  · rw [emod]
    split_ifs
    · exact Or.inl h0
    · rw [h0, mul_zero]
      exact Or.inl rfl
  · rw [emod]
    split_ifs
    · exact Or.inr hlt
    · by_cases hC : C P.leadingCoeff * (pseudoModExp P Q).2 = 0
      · exact Or.inl hC
      · exact Or.inr (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hlt)

end PseudoDivision

/-! ### The transfer, specialized -/

variable {n : ℕ}

/-- At a root of `spec g P`, the evenized remainder evaluates to the positive-power
multiple of `Q`'s value. -/
theorem emod_eval_at_root (g : Fin n → ℝ) (P Q : Polynomial (MvPolynomial (Fin n) ℝ))
    {ρ : ℝ} (hroot : (spec g P).eval ρ = 0) :
    (spec g (emod P Q)).eval ρ
      = (MvPolynomial.eval g P.leadingCoeff) ^ eexp P Q * (spec g Q).eval ρ := by
  obtain ⟨S, hS⟩ := emod_identity P Q
  have h := congrArg (fun T => (spec g T).eval ρ) hS
  simp only [spec, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_C] at h
  rw [show (P.map (MvPolynomial.eval g)).eval ρ = 0 from hroot, mul_zero, zero_add] at h
  exact h.symm

/-- **TS-2b: sign transfer at roots.** On the branch where `P`'s leading coefficient
survives at `g`, the full three-way sign of any `Q` at any root of `spec g P` equals that
of its evenized pseudo-remainder — a polynomial of `y`-degree `< deg P`. -/
theorem sign_transfer (g : Fin n → ℝ) (P Q : Polynomial (MvPolynomial (Fin n) ℝ))
    (hlead : MvPolynomial.eval g P.leadingCoeff ≠ 0)
    {ρ : ℝ} (hroot : (spec g P).eval ρ = 0) :
    (0 < (spec g Q).eval ρ ↔ 0 < (spec g (emod P Q)).eval ρ) ∧
    ((spec g Q).eval ρ = 0 ↔ (spec g (emod P Q)).eval ρ = 0) ∧
    ((spec g Q).eval ρ < 0 ↔ (spec g (emod P Q)).eval ρ < 0) := by
  have hpos : 0 < (MvPolynomial.eval g P.leadingCoeff) ^ eexp P Q :=
    (eexp_even P Q).pow_pos hlead
  rw [emod_eval_at_root g P Q hroot]
  refine ⟨⟨fun h => mul_pos hpos h, fun h => ?_⟩,
    ⟨fun h => by rw [h, mul_zero], fun h => ?_⟩,
    ⟨fun h => mul_neg_of_pos_of_neg hpos h, fun h => ?_⟩⟩
  · by_contra hle
    exact absurd h (not_lt.mpr
      (mul_nonpos_of_nonneg_of_nonpos hpos.le (not_lt.mp hle)))
  · rcases mul_eq_zero.mp h with hc | ht
    · exact absurd hc (ne_of_gt hpos)
    · exact ht
  · by_contra hle
    exact absurd h (not_lt.mpr (mul_nonneg hpos.le (not_lt.mp hle)))

end Sundog.TarskiQE
