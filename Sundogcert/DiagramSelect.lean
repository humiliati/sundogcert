/-
# TS-QE, TS-2's recursion (first pitch): the selection transport + end-sign branches.

Two of the recursion's three remaining legs:

- **`realizes_selectFam`** — the selection transport: a realized diagram restricts to
  ANY family whose members all occur in the original, with columns re-read through
  first-occurrence indices (`idxOf`). Membership suffices — duplicate members carry
  equal sign entries, so multiplicity and order are irrelevant. ONE lemma subsumes all
  the remaining reshaping: dropping `Pd` from the walked family
  `P :: Pd :: F.erase P`, and returning to the ORIGINAL `F` in its original order
  (`Q ∈ F → Q = P ∨ Q ∈ F.erase P` membership-wise). No permutation machinery needed.
- **`topSign_live` / `botSign_live`** — the end tags pinned by the evaluated leading
  coefficient: on a live lead, `TopSign` is the sign of `eval g P.leadingCoeff` and
  `BotSign` twists it by `(-1)^natDegree` (degree exactness via
  `resolve_eq_self_iff` + `spec_natDegree_eq`/`spec_leadingCoeff_eq`). The pinning
  conditions `{g | SignType.sign (eval g c) = s}` are ALREADY `SADef` by the 2d-1
  sign-condition algebra — so on a sign-refined branch the master's `(εm, εp)` inputs
  are constants.

**Honest fence.** The last leg is the vanishing-lead branch layer (`truncChain`
assignments: on each `SADef` cell "top coefficients vanish, next is live", members
behave as their truncations via `resolve_spec`) and the Dershowitz–Manna assembly
closing `DiagramPartition` for every family.
-/
import Sundogcert.DiagramMaster

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Degree exactness on a live lead -/

theorem spec_natDegree_live {g : Fin n → ℝ}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (h : MvPolynomial.eval g P.leadingCoeff ≠ 0) :
    (spec g P).natDegree = P.natDegree := by
  rw [spec_natDegree_eq, (resolve_eq_self_iff g P).mpr (Or.inr h)]

theorem spec_leadingCoeff_live {g : Fin n → ℝ}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (h : MvPolynomial.eval g P.leadingCoeff ≠ 0) :
    (spec g P).leadingCoeff = MvPolynomial.eval g P.leadingCoeff := by
  rw [spec_leadingCoeff_eq, (resolve_eq_self_iff g P).mpr (Or.inr h)]

/-! ### End signs from the leading coefficient -/

/-- On a live lead, the `+∞` tag is the sign of the evaluated leading coefficient. -/
theorem topSign_live {g : Fin n → ℝ} {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (h : MvPolynomial.eval g P.leadingCoeff ≠ 0) :
    TopSign g P (SignType.sign (MvPolynomial.eval g P.leadingCoeff)) := by
  rcases lt_trichotomy (MvPolynomial.eval g P.leadingCoeff) 0 with hlt | h0 | hgt
  · rw [sign_neg hlt]
    exact eventually_neg_atTop _ (by rw [spec_leadingCoeff_live h]; exact hlt)
  · exact absurd h0 h
  · rw [sign_pos hgt]
    exact eventually_pos_atTop _ (by rw [spec_leadingCoeff_live h]; exact hgt)

/-- On a live lead, the `-∞` tag is the leading sign twisted by degree parity. -/
theorem botSign_live {g : Fin n → ℝ} {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (h : MvPolynomial.eval g P.leadingCoeff ≠ 0) :
    BotSign g P (SignType.sign
      ((-1 : ℝ) ^ P.natDegree * MvPolynomial.eval g P.leadingCoeff)) := by
  have hkey : (-1 : ℝ) ^ (spec g P).natDegree * (spec g P).leadingCoeff
      = (-1 : ℝ) ^ P.natDegree * MvPolynomial.eval g P.leadingCoeff := by
    rw [spec_natDegree_live h, spec_leadingCoeff_live h]
  rcases lt_trichotomy
    ((-1 : ℝ) ^ P.natDegree * MvPolynomial.eval g P.leadingCoeff) 0 with hlt | h0 | hgt
  · rw [sign_neg hlt]
    exact eventually_neg_atBot _ (by rw [hkey]; exact hlt)
  · exfalso
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact h h1
  · rw [sign_pos hgt]
    exact eventually_pos_atBot _ (by rw [hkey]; exact hgt)

/-! ### The selection transport -/

/-- Re-read a column of `F`'s diagram as a column of `F₁`'s, through first-occurrence
indices. -/
noncomputable def selectFam (F F₁ : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (c : List SignType) : List SignType :=
  F₁.map fun Q => (c[F.idxOf Q]?).getD 0

private theorem selectFam_signVec (g : Fin n → ℝ)
    {F F₁ : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hmem : ∀ Q ∈ F₁, Q ∈ F) (y : ℝ) :
    selectFam F F₁ (signVec F g y) = signVec F₁ g y := by
  conv_rhs => rw [signVec]
  rw [selectFam]
  refine List.map_congr_left fun Q hQ => ?_
  have hlt : F.idxOf Q < F.length := List.idxOf_lt_length_of_mem (hmem Q hQ)
  rw [signVec_getElem?, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
  rfl

private theorem colsFrom_selectFam (g : Fin n → ℝ)
    {F F₁ : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hmem : ∀ Q ∈ F₁, Q ∈ F) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g F lo ξ cols →
    ColsFrom g F₁ lo ξ (cols.map (selectFam F F₁)) := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc
    match cols, hc with
    | [c], hc =>
      change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F₁ g y = selectFam F F₁ c
      intro y hy
      rw [← hc y hy, selectFam_signVec g hmem]
  | cons x xs ih =>
    intro lo cols hc
    match cols, hc with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      refine ⟨hlox, ?_, ?_, ih (some x) rest hrest⟩
      · intro y hy hyx
        rw [← hgap y hy hyx, selectFam_signVec g hmem]
      · rw [← hpt, selectFam_signVec g hmem]

/-- **The selection transport.** A realized diagram restricts to any family whose
members all occur in the original: columns re-read through first-occurrence indices.
Subsumes dropping a member, reordering, and duplication — the recursion's whole
reshaping layer. -/
theorem realizes_selectFam {g : Fin n → ℝ}
    {F F₁ : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hmem : ∀ Q ∈ F₁, Q ∈ F) {D : List (List SignType)}
    (h : Realizes g F D) : Realizes g F₁ (D.map (selectFam F F₁)) := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  exact ⟨ξ, hpair, fun Q hQ h0 y hy => hroots Q (hmem Q hQ) h0 y hy,
    colsFrom_selectFam g hmem ξ none D hcols⟩

end Sundog.TarskiQE
