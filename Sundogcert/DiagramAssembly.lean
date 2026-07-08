/-
# TS-QE, TS-2's last theorem: the Dershowitz–Manna assembly.

**`diagramPartition_all`** — every family of parametric polynomials has a diagram
partition — and its corollary **`elim_signVector`** — the existential sign-vector set
is semialgebraic in the parameters: Tarski–Seidenberg's elimination step, closed.

The recursion (`famDegrees_induction`): for a family `F`, cover parameter space by the
resolve-cells (`cellsOf`/`exists_resolve_cell`); on each cell the family behaves as its
truncation `T` (`realizes_congr`). If `T` is all-constants, `diagramPartition_of_constants`
finishes. Otherwise pick a max-degree member `tP` (maximality bounds the remainder
degrees), form the derived family `(tPd :: bres) ++ remainders` from the LIVE part of
`T`, recurse (the measure drops: `famDegrees_derived_lt`, then the sub-multiset and
componentwise-truncation comparisons chained by `IsDershowitzMannaLT.trans`), and on
each recursive branch × end-sign cell run the pipeline:
`realizes_readAnnot` (the machine-checked reconstruction step) → `realizes_zero_cons`
(zero truncations rejoin) → `realizes_selectFam` (back to `T`) → `realizes_congr`
(back to `F`). Every branch diagram is a pure function of the recursive branch diagram
and the two end tags; every branch set is `SADef` by the resolve-cell and sign-condition
algebra.
-/
import Sundogcert.DiagramBranches

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Dershowitz–Manna micro-lemmas -/

private theorem dm_sub {M N : Multiset ℕ} (hN : N ≠ 0) :
    Multiset.IsDershowitzMannaLT M (M + N) :=
  ⟨M, 0, N, hN, (add_zero M).symm, rfl, fun y hy => by simp at hy⟩

private theorem dm_cons (a : ℕ) {M N : Multiset ℕ}
    (h : Multiset.IsDershowitzMannaLT M N) :
    Multiset.IsDershowitzMannaLT (a ::ₘ M) (a ::ₘ N) := by
  obtain ⟨X, Y, Z, hZ, hM, hN, hd⟩ := h
  exact ⟨a ::ₘ X, Y, Z, hZ, by rw [hM, Multiset.cons_add],
    by rw [hN, Multiset.cons_add], hd⟩

private theorem dm_single {a b : ℕ} (hab : a < b) (M : Multiset ℕ) :
    Multiset.IsDershowitzMannaLT (a ::ₘ M) (b ::ₘ M) := by
  refine ⟨M, {a}, {b}, by simp, ?_, ?_, ?_⟩
  · rw [add_comm, Multiset.singleton_add]
  · rw [add_comm, Multiset.singleton_add]
  · intro y hy
    rw [Multiset.mem_singleton] at hy
    subst hy
    exact ⟨b, Multiset.mem_singleton_self b, hab⟩

private theorem famDegrees_le_dm
    {F T : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (h : List.Forall₂ (fun q t => t.natDegree ≤ q.natDegree) F T) :
    famDegrees T = famDegrees F ∨
      Multiset.IsDershowitzMannaLT (famDegrees T) (famDegrees F) := by
  induction h with
  | nil => exact Or.inl rfl
  | cons hqt _ ih =>
    rw [famDegrees_cons, famDegrees_cons]
    rcases lt_or_eq_of_le hqt with hlt | heq
    · refine Or.inr ?_
      rcases ih with heq' | hdm
      · rw [heq']
        exact dm_single hlt _
      · exact (dm_cons _ hdm).trans (dm_single hlt _)
    · rw [heq]
      rcases ih with heq' | hdm
      · exact Or.inl (by rw [heq'])
      · exact Or.inr (dm_cons _ hdm)

/-! ### Small tools -/

private theorem exists_max_degree
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} (hne : F ≠ []) :
    ∃ P ∈ F, ∀ Q ∈ F, Q.natDegree ≤ P.natDegree := by
  induction F with
  | nil => exact absurd rfl hne
  | cons q F ih =>
    rcases eq_or_ne F [] with rfl | hF
    · refine ⟨q, List.mem_cons_self, fun Q hQ => ?_⟩
      rcases List.mem_cons.mp hQ with rfl | h
      · exact le_rfl
      · simp at h
    · obtain ⟨P, hP, hmax⟩ := ih hF
      rcases le_total q.natDegree P.natDegree with h | h
      · refine ⟨P, List.mem_cons_of_mem _ hP, fun Q hQ => ?_⟩
        rcases List.mem_cons.mp hQ with rfl | hQ'
        · exact h
        · exact hmax Q hQ'
      · refine ⟨q, List.mem_cons_self, fun Q hQ => ?_⟩
        rcases List.mem_cons.mp hQ with rfl | hQ'
        · exact le_rfl
        · exact le_trans (hmax Q hQ') h

private theorem spec_zero (g : Fin n → ℝ) :
    spec g (0 : Polynomial (MvPolynomial (Fin n) ℝ)) = 0 := by
  rw [spec]
  exact Polynomial.map_zero _

private theorem forall₂_flip_eq {g : Fin n → ℝ}
    {F T : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (h : List.Forall₂ (fun q t => spec g q = spec g t) F T) :
    List.Forall₂ (fun t q => spec g t = spec g q) T F := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hqt _ ih => exact List.Forall₂.cons hqt.symm ih

/-- On a live lead of positive degree, the derivative's lead is live. -/
private theorem derivative_lead_live {g : Fin n → ℝ}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)} (hd0 : P.natDegree ≠ 0)
    (hlive : MvPolynomial.eval g P.leadingCoeff ≠ 0) :
    MvPolynomial.eval g (derivative P).leadingCoeff ≠ 0 := by
  have hP0 : P ≠ 0 := fun h => hd0 (by rw [h]; simp)
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hco := Polynomial.coeff_derivative P (P.natDegree - 1)
  rw [show P.natDegree - 1 + 1 = P.natDegree from by omega] at hco
  have hcast : ((P.natDegree - 1 : ℕ) : MvPolynomial (Fin n) ℝ) + 1
      = (P.natDegree : MvPolynomial (Fin n) ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ P.natDegree), Nat.cast_one]
    ring
  have hne : (derivative P).coeff (P.natDegree - 1) ≠ 0 := by
    rw [hco]
    refine mul_ne_zero hlc ?_
    rw [hcast]
    exact Nat.cast_ne_zero.mpr hd0
  have hdeg : (derivative P).natDegree = P.natDegree - 1 :=
    le_antisymm (Polynomial.natDegree_derivative_le P)
      (Polynomial.le_natDegree_of_ne_zero hne)
  have hlcd : (derivative P).leadingCoeff
      = P.leadingCoeff * (P.natDegree : MvPolynomial (Fin n) ℝ) := by
    rw [Polynomial.leadingCoeff, hdeg, hco, hcast]
    rfl
  rw [hlcd, map_mul, map_natCast]
  exact mul_ne_zero hlive (Nat.cast_ne_zero.mpr hd0)

/-! ### Cell enumeration -/

private noncomputable def cellsOf :
    List (Polynomial (MvPolynomial (Fin n) ℝ)) →
      List (List (Polynomial (MvPolynomial (Fin n) ℝ)))
  | [] => [[]]
  | q :: F => (truncChain q).flatMap fun t => (cellsOf F).map fun T => t :: T

private theorem mem_cellsOf
    {F T : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (h : List.Forall₂ (fun q t => t ∈ truncChain q) F T) : T ∈ cellsOf F := by
  induction h with
  | nil => simp [cellsOf]
  | @cons q t F' T' hqt _ ih =>
    simp only [cellsOf]
    exact List.mem_flatMap.mpr ⟨t, hqt, List.mem_map.mpr ⟨T', ih, rfl⟩⟩

private theorem cellsOf_forall₂ :
    ∀ {F T : List (Polynomial (MvPolynomial (Fin n) ℝ))}, T ∈ cellsOf F →
      List.Forall₂ (fun q t => t ∈ truncChain q) F T := by
  intro F
  induction F with
  | nil =>
    intro T hT
    simp only [cellsOf, List.mem_singleton] at hT
    subst hT
    exact List.Forall₂.nil
  | cons q F ih =>
    intro T hT
    simp only [cellsOf] at hT
    obtain ⟨t, ht, hT₂⟩ := List.mem_flatMap.mp hT
    obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hT₂
    exact List.Forall₂.cons ht (ih hT')

private def allSigns : List SignType := [SignType.zero, SignType.neg, SignType.pos]

private theorem mem_allSigns (s : SignType) : s ∈ allSigns := by
  cases s <;> simp [allSigns]

/-! ### The gluing lemma -/

private theorem diagramPartition_glue
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (cells : List (Set (Fin n → ℝ)))
    (hcover : ∀ g : Fin n → ℝ, ∃ c ∈ cells, g ∈ c)
    (hloc : ∀ c ∈ cells,
      ∃ branches : List (Set (Fin n → ℝ) × List (List SignType)),
        (∀ b ∈ branches, SADef n (b.1 ∩ c) ∧ ∀ g ∈ b.1 ∩ c, Realizes g F b.2) ∧
        (∀ g ∈ c, ∃ b ∈ branches, g ∈ b.1)) :
    DiagramPartition F := by
  refine ⟨cells.attach.flatMap fun c =>
    ((hloc c.1 c.2).choose.map fun b => (b.1 ∩ c.1, b.2)), ?_, ?_⟩
  · rintro b hb
    obtain ⟨⟨c, hc⟩, -, hbmem⟩ := List.mem_flatMap.mp hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hbmem
    obtain ⟨hSA, hval⟩ := (hloc c hc).choose_spec.1 b' hb'
    exact ⟨hSA, hval⟩
  · intro g
    obtain ⟨c, hc, hgc⟩ := hcover g
    obtain ⟨b', hb', hgb⟩ := (hloc c hc).choose_spec.2 g hgc
    exact ⟨(b'.1 ∩ c, b'.2),
      List.mem_flatMap.mpr ⟨⟨c, hc⟩, List.mem_attach _ _,
        List.mem_map.mpr ⟨b', hb', rfl⟩⟩, hgb, hgc⟩

/-! ### The recursion -/

/-- **TS-2's last theorem: every family has a diagram partition.** -/
theorem diagramPartition_all :
    ∀ F : List (Polynomial (MvPolynomial (Fin n) ℝ)), DiagramPartition F := by
  refine famDegrees_induction _ ?_
  intro F ih
  refine diagramPartition_glue F ((cellsOf F).map fun T =>
    {g : Fin n → ℝ | List.Forall₂ (fun q t => resolve g q = t) F T}) ?_ ?_
  · -- the cells cover
    intro g
    obtain ⟨T, h1, h2⟩ := exists_resolve_cell g F
    exact ⟨_, List.mem_map.mpr ⟨T, mem_cellsOf h2, rfl⟩, h1⟩
  · -- per cell
    rintro c hc
    obtain ⟨T, hTmem, rfl⟩ := List.mem_map.mp hc
    by_cases hconst : ∀ t ∈ T, t.natDegree = 0
    · -- constants route
      obtain ⟨branches, hval, hcov⟩ := diagramPartition_of_constants T hconst
      refine ⟨branches, ?_, fun g _ => hcov g⟩
      rintro b hb
      obtain ⟨hSA, hreal⟩ := hval b hb
      refine ⟨hSA.inter (sadef_resolve_cell F T), ?_⟩
      rintro g ⟨hgb, hgcell⟩
      exact realizes_congr (forall₂_flip_eq (resolve_cell_props hgcell).1)
        (hreal g hgb)
    · -- elimination route
      push Not at hconst
      obtain ⟨t₀, ht₀T, ht₀⟩ := hconst
      have hTne : T ≠ [] := fun h => by subst h; simp at ht₀T
      obtain ⟨tP, htPT, hmax⟩ := exists_max_degree hTne
      have htP0 : tP.natDegree ≠ 0 := fun h =>
        ht₀ (le_antisymm (h ▸ hmax t₀ ht₀T) (Nat.zero_le _))
      have htPne : tP ≠ 0 := fun h => htP0 (by rw [h]; simp)
      set tPd := derivative tP with htPddef
      set bres := (T.erase tP).filter (fun t => t ≠ 0) with hbresdef
      set F' := (tPd :: bres) ++ (tPd :: bres).map (fun r => emod r tP) with hF'def
      have hbres_mem : ∀ s ∈ bres, s ∈ T ∧ s ≠ 0 := by
        intro s hs
        rw [hbresdef, List.mem_filter] at hs
        exact ⟨List.mem_of_mem_erase hs.1, by simpa using hs.2⟩
      -- the measure drops
      have h1 : Multiset.IsDershowitzMannaLT (famDegrees F')
          (famDegrees (tP :: bres)) := by
        refine famDegrees_derived_lt (Polynomial.natDegree_derivative_lt htP0) ?_
        intro r hr
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
        rcases emod_rem s tP with h0 | hlt
        · rw [h0]
          simpa using Nat.pos_of_ne_zero htP0
        · rcases List.mem_cons.mp hs with rfl | hs'
          · exact lt_trans hlt (Polynomial.natDegree_derivative_lt htP0)
          · exact lt_of_lt_of_le hlt (hmax s (hbres_mem s hs').1)
      have h2le : famDegrees (tP :: bres) ≤ famDegrees T := by
        have hb : (↑bres : Multiset (Polynomial (MvPolynomial (Fin n) ℝ)))
            ≤ ↑(T.erase tP) := by
          rw [hbresdef]
          exact Multiset.coe_le.mpr (List.filter_sublist).subperm
        have hsub : (↑(tP :: bres) :
            Multiset (Polynomial (MvPolynomial (Fin n) ℝ))) ≤ ↑T := by
          calc (↑(tP :: bres) : Multiset (Polynomial (MvPolynomial (Fin n) ℝ)))
              = tP ::ₘ ↑bres := rfl
            _ ≤ tP ::ₘ ↑(T.erase tP) := Multiset.cons_le_cons _ hb
            _ = tP ::ₘ (T : Multiset (Polynomial (MvPolynomial (Fin n) ℝ))).erase tP := by
                rw [Multiset.coe_erase]
            _ = (T : Multiset (Polynomial (MvPolynomial (Fin n) ℝ))) :=
                Multiset.cons_erase (Multiset.mem_coe.mpr htPT)
        have hm := Multiset.map_le_map (f := Polynomial.natDegree) hsub
        rw [Multiset.map_coe, Multiset.map_coe] at hm
        exact hm
      have h3 := famDegrees_le_dm (List.Forall₂.imp
        (fun q t ht => truncChain_natDegree_le q t ht) (cellsOf_forall₂ hTmem))
      have hmeas : Multiset.IsDershowitzMannaLT (famDegrees F') (famDegrees F) := by
        obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h2le
        rcases eq_or_ne u 0 with rfl | hu0
        · rw [add_zero] at hu
          rw [← hu] at h1
          rcases h3 with heq | hdm
          · rw [heq] at h1
            exact h1
          · exact h1.trans hdm
        · have hTdm : Multiset.IsDershowitzMannaLT (famDegrees (tP :: bres))
              (famDegrees T) := by
            rw [hu]
            exact dm_sub hu0
          rcases h3 with heq | hdm
          · rw [← heq]
            exact h1.trans hTdm
          · exact (h1.trans hTdm).trans hdm
      -- the recursion
      obtain ⟨branchesR, hvalR, hcovR⟩ := ih F' hmeas
      -- the branch list for this cell
      refine ⟨branchesR.flatMap fun b => allSigns.flatMap fun εm =>
        allSigns.map fun εp =>
          (b.1 ∩ ({g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g
              ((-1 : MvPolynomial (Fin n) ℝ) ^ tP.natDegree * tP.leadingCoeff)) = εm}
            ∩ {g : Fin n → ℝ |
              SignType.sign (MvPolynomial.eval g tP.leadingCoeff) = εp}),
           ((graftWalk (readAnnot (tPd :: bres).length εp εm b.2).1
              (readAnnot (tPd :: bres).length εp εm b.2).2
              (baseDrop (tPd :: bres).length b.2)).map
                fun col => (0 : SignType) :: col).map
             (selectFam (0 :: tP :: tPd :: bres) T)), ?_, ?_⟩
      · -- validity
        rintro bF hbF
        obtain ⟨b, hb, hbF₂⟩ := List.mem_flatMap.mp hbF
        obtain ⟨εm, -, hbF₃⟩ := List.mem_flatMap.mp hbF₂
        obtain ⟨εp, -, rfl⟩ := List.mem_map.mp hbF₃
        obtain ⟨hSAb, hrealb⟩ := hvalR b hb
        refine ⟨((hSAb.inter ((SADef.signEq _ εm).inter
          (SADef.signEq _ εp))).inter (sadef_resolve_cell F T)), ?_⟩
        rintro g ⟨⟨hgb, hgεm, hgεp⟩, hgcell⟩
        obtain ⟨hspecFT, hzl⟩ := resolve_cell_props hgcell
        have htPlive : MvPolynomial.eval g tP.leadingCoeff ≠ 0 := by
          rcases hzl tP htPT with h | h
          · exact absurd h htPne
          · exact h
        have hlive : ∀ q ∈ tPd :: bres,
            MvPolynomial.eval g q.leadingCoeff ≠ 0 := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact derivative_lead_live htP0 htPlive
          · obtain ⟨hsT, hs0⟩ := hbres_mem q hq'
            rcases hzl q hsT with h | h
            · exact absurd h hs0
            · exact h
        have hbot : BotSign g tP εm := by
          have hb := botSign_live htPlive
          have heval : MvPolynomial.eval g
              ((-1 : MvPolynomial (Fin n) ℝ) ^ tP.natDegree * tP.leadingCoeff)
              = (-1 : ℝ) ^ tP.natDegree * MvPolynomial.eval g tP.leadingCoeff := by
            rw [map_mul, map_pow, map_neg, map_one]
          rw [← heval, hgεm] at hb
          exact hb
        have htop : TopSign g tP εp := by
          have ht := topSign_live htPlive
          rw [hgεp] at ht
          exact ht
        have h₁ := realizes_readAnnot (spec_derivative g tP) hlive hbot htop
          (hrealb g hgb)
        have h₂ := realizes_zero_cons (spec_zero g) h₁
        have hmemT : ∀ t ∈ T, t ∈ 0 :: tP :: tPd :: bres := by
          intro t ht
          by_cases ht0 : t = 0
          · subst ht0
            exact List.mem_cons.mpr (Or.inl rfl)
          · by_cases httP : t = tP
            · subst httP
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
            · have htb : t ∈ bres := by
                rw [hbresdef, List.mem_filter]
                exact ⟨(List.mem_erase_of_ne httP).mpr ht, by simpa using ht0⟩
              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
                (List.mem_cons.mpr (Or.inr htb)))))
        have h₃ := realizes_selectFam hmemT h₂
        exact realizes_congr (forall₂_flip_eq hspecFT) h₃
      · -- cover on the cell
        intro g _hgcell
        obtain ⟨b, hb, hgb⟩ := hcovR g
        refine ⟨_, List.mem_flatMap.mpr ⟨b, hb, List.mem_flatMap.mpr
          ⟨SignType.sign (MvPolynomial.eval g
            ((-1 : MvPolynomial (Fin n) ℝ) ^ tP.natDegree * tP.leadingCoeff)),
            mem_allSigns _, List.mem_map.mpr
              ⟨SignType.sign (MvPolynomial.eval g tP.leadingCoeff),
                mem_allSigns _, rfl⟩⟩⟩, hgb, rfl, rfl⟩

/-- **TARSKI–SEIDENBERG, elimination form**: the set of parameters at which the family
attains a given sign vector somewhere on the line is semialgebraic. -/
theorem elim_signVector (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (σ : List SignType) :
    SADef n {g : Fin n → ℝ | ∃ y : ℝ, signVec F g y = σ} :=
  elim_of_diagramPartition (diagramPartition_all F) σ

end Sundog.TarskiQE
