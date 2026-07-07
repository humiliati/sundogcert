/-
# TS-QE, TS-2d-3: the fused master — the walked diagram from column data alone.

One strong induction over the full derived diagram (family
`(Pd :: bres) ++ (Pd :: bres).map (emod · P)`, live base leads) producing TOGETHER:

- `ColsFrom g (Pd :: bres) lo₀ ξk (baseDrop m cols)` — the projected-and-merged base
  diagram is realized on the kept samples, and
- `GraftData g P lo₀ ξk (readAnnot m εp sa cols)` — the READ annotation is valid,

so `realizes_graftWalk` fires with an annotation that is a pure function of
`(cols, sa, εp)` — branch-constant inputs give ONE `P :: Pd :: bres` diagram valid
branch-wide (**`realizes_readAnnot`**, the capstone).

**The pending-gap accumulator** (the design discovery of the previous pitch): the
induction carries the last KEPT barrier `lo₀` with its flank tag `sa` (`FlankTag`:
`BotSign` at `none`, the sample sign at `some`), while the structural barrier `lo`
advances through dropped samples; the carried pending fact states that the base sign
vector on `(lo₀, lo]` equals the base projection of the CURRENT gap column. Plan
validity is discharged only at keep time, over the whole merged gap, through the
`readPlan_valid_*` bridges; each drop re-establishes the pending fact by two projected
`signVec_eq_of_gap` applications (across the dropped sample and into the next gap).
With the keep-later walk functions, the drop case is pure plumbing: the recursion's
outputs ARE the goal outputs.

**Honest fence.** Remaining for `DiagramPartition`: the `SADef` branch conditions
pinning `(εm, εp)` and the live leads (`truncChain` refinement), the drop-a-member
projection (`Pd` out of the walked family), and the Dershowitz–Manna recursion.
-/
import Sundogcert.DiagramReads

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-- The left-flank tag at a kept barrier: an end sign at `none`, the sample sign at
`some`. -/
def FlankTag (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Option ℝ → SignType → Prop
  | none, sa => BotSign g P sa
  | some a, sa => SignType.sign ((spec g P).eval a) = sa

/-! ### Small tools -/

private theorem spec_ne_zero_of_live {g : Fin n → ℝ}
    {q : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hlive : MvPolynomial.eval g q.leadingCoeff ≠ 0) : spec g q ≠ 0 := by
  intro h0
  apply hlive
  have h1 : (spec g q).coeff q.natDegree = 0 := by
    rw [h0]
    simp
  rw [spec, Polynomial.coeff_map] at h1
  exact h1

private theorem pending_or_beyond (lo : Option ℝ) (y : ℝ) :
    (∃ l ∈ lo, y ≤ l) ∨ (∀ l ∈ lo, l < y) := by
  cases lo with
  | none => exact Or.inr fun l hl => by simp at hl
  | some l =>
    rcases le_or_gt y l with h | h
    · exact Or.inl ⟨l, rfl, h⟩
    · refine Or.inr fun l' hl' => ?_
      rw [Option.mem_def, Option.some.injEq] at hl'
      subst hl'
      exact h

private theorem headD_take {c : List SignType} {m : ℕ} (hm : 0 < m) :
    (c.take m).headD 0 = c.headD 0 := by
  match c, m with
  | [], _ => rw [List.take_nil]
  | _ :: _, 0 => exact absurd hm (lt_irrefl 0)
  | s :: rest, m + 1 => rw [List.take_succ_cons, List.headD_cons, List.headD_cons]

private theorem zero_mem_of_root {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    {q : Polynomial (MvPolynomial (Fin n) ℝ)} (hq : q ∈ F) {x : ℝ}
    (h0 : (spec g q).eval x = 0) : SignType.zero ∈ signVec F g x := by
  rw [signVec]
  refine List.mem_map.mpr ⟨q, hq, ?_⟩
  rw [h0]
  simp

private theorem root_of_zero_mem {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} {x : ℝ}
    (h : SignType.zero ∈ signVec F g x) :
    ∃ q ∈ F, (spec g q).eval x = 0 := by
  rw [signVec] at h
  obtain ⟨q, hq, hs⟩ := List.mem_map.mp h
  exact ⟨q, hq, sign_eq_zero_iff.mp hs⟩

/-! ### Shape equations for the walk functions -/

theorem baseDrop_cons (m : ℕ) (c cpt : List SignType) (rest : List (List SignType)) :
    baseDrop m (c :: cpt :: rest) =
      if SignType.zero ∈ cpt.take m then
        c.take m :: cpt.take m :: baseDrop m rest
      else
        match rest with
        | [] => [c.take m]
        | _ :: _ => baseDrop m rest := rfl

theorem readAnnot_cons (m : ℕ) (εp sa : SignType) (c cpt : List SignType)
    (rest : List (List SignType)) :
    readAnnot m εp sa (c :: cpt :: rest) =
      if SignType.zero ∈ cpt.take m then
        (readPtSign m cpt :: (readAnnot m εp (readPtSign m cpt) rest).1,
          readPlan (c.headD 0) sa (readPtSign m cpt)
            :: (readAnnot m εp (readPtSign m cpt) rest).2)
      else
        match rest with
        | [] => ([], [readPlan (c.headD 0) sa εp])
        | _ :: _ => readAnnot m εp sa rest := rfl

/-! ### The nil case, factored -/

private theorem master_nil (g : Fin n → ℝ)
    (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (bres : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (hd : spec g Pd = derivative (spec g P))
    (hlive : ∀ q ∈ Pd :: bres, MvPolynomial.eval g q.leadingCoeff ≠ 0)
    (εp : SignType) (htop : TopSign g P εp)
    (lo : Option ℝ) (c : List SignType) (lo₀ : Option ℝ) (sa : SignType)
    (hroots : ∀ Q ∈ (Pd :: bres) ++ (Pd :: bres).map fun r => emod r P,
      spec g Q ≠ 0 → ∀ z : ℝ, (∀ l ∈ lo, l < z) → (spec g Q).IsRoot z →
        z ∈ ([] : List ℝ))
    (hray : ∀ y : ℝ, (∀ l ∈ lo, l < y) →
      signVec ((Pd :: bres) ++ (Pd :: bres).map fun r => emod r P) g y = c)
    (hflank : FlankTag g P lo₀ sa)
    (hpend : ∀ y : ℝ, (∀ l₀ ∈ lo₀, l₀ < y) → (∃ l ∈ lo, y ≤ l) →
      signVec (Pd :: bres) g y = c.take (Pd :: bres).length) :
    ∃ ξk : List ℝ,
      (∀ l₀ ∈ lo₀, ∀ x ∈ ξk, l₀ < x) ∧
      (∀ Q ∈ Pd :: bres, ∀ z : ℝ, (∀ l₀ ∈ lo₀, l₀ < z) →
        (spec g Q).IsRoot z → z ∈ ξk) ∧
      ColsFrom g (Pd :: bres) lo₀ ξk [c.take (Pd :: bres).length] ∧
      GraftData g P lo₀ ξk ([] : List SignType) [readPlan (c.headD 0) sa εp] := by
  have hnz : ∀ q ∈ Pd :: bres, spec g q ≠ 0 :=
    fun q hq => spec_ne_zero_of_live (hlive q hq)
  have hbase : ∀ y : ℝ, (∀ l₀ ∈ lo₀, l₀ < y) →
      signVec (Pd :: bres) g y = c.take (Pd :: bres).length := by
    intro y hy
    rcases pending_or_beyond lo y with hpen | hby
    · exact hpend y hy hpen
    · rw [← take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g y,
        hray y hby]
  have hnoroot : ∀ Q ∈ Pd :: bres, ∀ z : ℝ, (∀ l₀ ∈ lo₀, l₀ < z) →
      ¬ (spec g Q).IsRoot z := by
    intro Q hQ z hz hzroot
    have hzero : SignType.zero ∈ c.take (Pd :: bres).length := by
      rw [← hbase z hz]
      exact zero_mem_of_root hQ hzroot
    obtain ⟨w, hwlo⟩ : ∃ w : ℝ, ∀ l ∈ lo, l < w := by
      cases lo with
      | none => exact ⟨0, fun l hl => by simp at hl⟩
      | some l =>
        refine ⟨l + 1, fun l' hl' => ?_⟩
        rw [Option.mem_def, Option.some.injEq] at hl'
        subst hl'
        linarith
    have hw : signVec (Pd :: bres) g w = c.take (Pd :: bres).length := by
      rw [← take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g w,
        hray w hwlo]
    rw [← hw] at hzero
    obtain ⟨q', hq', h0'⟩ := root_of_zero_mem hzero
    have hmem := hroots q' (List.mem_append_left _ hq') (hnz q' hq') w hwlo h0'
    simp at hmem
  have hσ : ∀ y : ℝ, (∀ l₀ ∈ lo₀, l₀ < y) →
      SignType.sign ((spec g Pd).eval y) = c.headD 0 := by
    intro y hy
    have h1 := headD_reads_gap_sign g Pd bres (hbase y hy)
    rw [headD_take (by simp)] at h1
    exact h1
  refine ⟨[], fun l hl x hx => by simp at hx,
    fun Q hQ z hz hzroot => absurd hzroot (hnoroot Q hQ z hz), ?_, ?_⟩
  · change ∀ y : ℝ, (∀ l₀ ∈ lo₀, l₀ < y) →
      signVec (Pd :: bres) g y = c.take (Pd :: bres).length
    exact hbase
  · rcases lo₀ with _ | a
    · have hba : BotSign g P sa := hflank
      exact readPlan_valid_line g P Pd hd
        (fun y => hσ y (fun l hl => by simp at hl)) hba htop
    · have hfa : SignType.sign ((spec g P).eval a) = sa := hflank
      have hval := readPlan_valid_right g P Pd hd
        (fun y hy => hσ y (some_mem_lt hy)) htop
      rw [hfa] at hval
      exact hval

/-! ### The master -/

/-- **The fused master.** Over the full derived diagram, the projected-and-merged base
diagram is realized on the kept samples and the READ annotation is valid — both pure
functions of the columns, the carried flank, and the end tag. -/
theorem colsFrom_master (g : Fin n → ℝ)
    (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (bres : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (hd : spec g Pd = derivative (spec g P))
    (hlive : ∀ q ∈ Pd :: bres, MvPolynomial.eval g q.leadingCoeff ≠ 0)
    (εp : SignType) (htop : TopSign g P εp) :
    ∀ (N : ℕ) (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType))
      (lo₀ : Option ℝ) (sa : SignType),
    ξ.length ≤ N →
    ξ.Pairwise (· < ·) →
    (∀ l ∈ lo, ∀ x ∈ ξ, l < x) →
    (∀ Q ∈ (Pd :: bres) ++ (Pd :: bres).map fun r => emod r P, spec g Q ≠ 0 →
      ∀ z : ℝ, (∀ l ∈ lo, l < z) → (spec g Q).IsRoot z → z ∈ ξ) →
    ColsFrom g ((Pd :: bres) ++ (Pd :: bres).map fun r => emod r P) lo ξ cols →
    FlankTag g P lo₀ sa →
    (∀ y : ℝ, (∀ l ∈ lo, l < y) → ∀ l₀ ∈ lo₀, l₀ < y) →
    (∀ y : ℝ, (∀ l₀ ∈ lo₀, l₀ < y) → (∃ l ∈ lo, y ≤ l) →
      signVec (Pd :: bres) g y = (cols.headD []).take (Pd :: bres).length) →
    ∃ ξk : List ℝ,
      (∀ l₀ ∈ lo₀, ∀ x ∈ ξk, l₀ < x) ∧
      (∀ Q ∈ Pd :: bres, ∀ z : ℝ, (∀ l₀ ∈ lo₀, l₀ < z) →
        (spec g Q).IsRoot z → z ∈ ξk) ∧
      ColsFrom g (Pd :: bres) lo₀ ξk (baseDrop (Pd :: bres).length cols) ∧
      GraftData g P lo₀ ξk
        (readAnnot (Pd :: bres).length εp sa cols).1
        (readAnnot (Pd :: bres).length εp sa cols).2 := by
  have hnz : ∀ q ∈ Pd :: bres, spec g q ≠ 0 :=
    fun q hq => spec_ne_zero_of_live (hlive q hq)
  intro N
  induction N with
  | zero =>
    intro ξ lo cols lo₀ sa hlen hpair hlo hroots hc hflank hlo₀ hpend
    have h0 : ξ = [] := List.length_eq_zero_iff.mp (by omega)
    subst h0
    match cols, hc with
    | [], hc => exact hc.elim
    | [c], hc =>
      exact master_nil g P Pd bres hd hlive εp htop lo c lo₀ sa hroots hc hflank hpend
    | _ :: _ :: _, hc => exact hc.elim
  | succ N ih =>
    intro ξ lo cols lo₀ sa hlen hpair hlo hroots hc hflank hlo₀ hpend
    match ξ, cols, hc with
    | [], [], hc => exact hc.elim
    | [], [c], hc =>
      exact master_nil g P Pd bres hd hlive εp htop lo c lo₀ sa hroots hc hflank hpend
    | [], _ :: _ :: _, hc => exact hc.elim
    | x :: xs, [], hc => exact hc.elim
    | x :: xs, [_], hc => exact hc.elim
    | x :: xs, c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      simp only [List.headD_cons] at hpend
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hlo₀x : ∀ l₀ ∈ lo₀, l₀ < x := hlo₀ x hlox
      by_cases hz : SignType.zero ∈ cpt.take (Pd :: bres).length
      · -- KEEP the sample
        have hz' : SignType.zero ∈ (signVec ((Pd :: bres)
            ++ (Pd :: bres).map fun r => emod r P) g x).take (Pd :: bres).length := by
          rw [hpt]
          exact hz
        have hsP := readPtSign_correct g P hlive hz'
        rw [hpt] at hsP
        obtain ⟨ξk', o1', o2', o3', o4'⟩ := ih xs (some x) rest (some x)
          (readPtSign (Pd :: bres).length cpt)
          (by simp at hlen; omega) htail
          (by
            intro l hl z hz2
            rw [Option.mem_def, Option.some.injEq] at hl
            subst hl
            exact hhead z hz2)
          (by
            intro Q hQ h0 z hzlo hzroot
            have hzx : x < z := hzlo x rfl
            have hmem := hroots Q hQ h0 z
              (fun l hl => lt_trans (hlox l hl) hzx) hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd hzx (lt_irrefl z)
            · exact hmem)
          hrest hsP.symm (fun y hy => hy)
          (by
            intro y hy hex
            obtain ⟨l, hl, hyl⟩ := hex
            rw [Option.mem_def, Option.some.injEq] at hl
            subst hl
            exact absurd (hy x rfl) (not_lt.mpr hyl))
        refine ⟨x :: ξk', ?_, ?_, ?_, ?_⟩
        · intro l₀ hl₀ z hzmem
          rcases List.mem_cons.mp hzmem with rfl | hzm
          · exact hlo₀x l₀ hl₀
          · exact lt_trans (hlo₀x l₀ hl₀) (o1' x rfl z hzm)
        · intro Q hQ z hzb hzroot
          rcases pending_or_beyond lo z with hpen | hby
          · exfalso
            have hzero : SignType.zero ∈ c.take (Pd :: bres).length := by
              rw [← hpend z hzb hpen]
              exact zero_mem_of_root hQ hzroot
            obtain ⟨w, hwlo, hwx⟩ : ∃ w : ℝ, (∀ l ∈ lo, l < w) ∧ w < x := by
              cases lo with
              | none =>
                obtain ⟨w, hw⟩ := exists_lt x
                exact ⟨w, by simp, hw⟩
              | some l =>
                obtain ⟨w, hw1, hw2⟩ := exists_between (by simpa using hlox l rfl)
                exact ⟨w, by simpa using hw1, hw2⟩
            have hw : signVec (Pd :: bres) g w = c.take (Pd :: bres).length := by
              rw [← take_signVec_append (Pd :: bres)
                ((Pd :: bres).map fun r => emod r P) g w, hgap w hwlo hwx]
            rw [← hw] at hzero
            obtain ⟨q', hq', h0'⟩ := root_of_zero_mem hzero
            have hmem := hroots q' (List.mem_append_left _ hq') (hnz q' hq')
              w hwlo h0'
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd hwx (lt_irrefl w)
            · exact absurd (hhead w hmem) (not_lt.mpr hwx.le)
          · have hmem := hroots Q (List.mem_append_left _ hQ) (hnz Q hQ) z hby hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact List.mem_cons.mpr (Or.inl rfl)
            · exact List.mem_cons.mpr
                (Or.inr (o2' Q hQ z (some_mem_lt (hhead z hmem)) hzroot))
        · rw [baseDrop_cons, if_pos hz]
          refine ⟨hlo₀x, ?_, ?_, o3'⟩
          · intro y hy hyx
            rcases pending_or_beyond lo y with hpen | hby
            · exact hpend y hy hpen
            · rw [← take_signVec_append (Pd :: bres)
                ((Pd :: bres).map fun r => emod r P) g y, hgap y hby hyx]
          · rw [← take_signVec_append (Pd :: bres)
              ((Pd :: bres).map fun r => emod r P) g x, hpt]
        · rw [readAnnot_cons, if_pos hz]
          refine ⟨?_, hsP.symm, o4'⟩
          have hσ : ∀ y : ℝ, (∀ l₀ ∈ lo₀, l₀ < y) → y < x →
              SignType.sign ((spec g Pd).eval y) = c.headD 0 := by
            intro y hy hyx
            rcases pending_or_beyond lo y with hpen | hby
            · have h1 := headD_reads_gap_sign g Pd bres (hpend y hy hpen)
              rw [headD_take (by simp)] at h1
              exact h1
            · exact headD_reads_gap_sign g Pd
                (bres ++ (Pd :: bres).map fun r => emod r P) (hgap y hby hyx)
          rcases lo₀ with _ | a
          · have hba : BotSign g P sa := hflank
            have hval := readPlan_valid_left g P Pd hd
              (fun y hy => hσ y (fun l hl => by simp at hl) hy) hba
            rw [← hsP] at hval
            exact hval
          · have hfa : SignType.sign ((spec g P).eval a) = sa := hflank
            have hax : a < x := hlo₀x a rfl
            have hval := readPlan_valid_gap g P Pd hd hax
              (fun y hy => hσ y (some_mem_lt hy.1) hy.2)
            rw [hfa, ← hsP] at hval
            exact hval
      · -- DROP the sample
        have hnorootx : ∀ q ∈ Pd :: bres, ¬ (spec g q).eval x = 0 := by
          intro q hq h0
          apply hz
          rw [← hpt,
            take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g x]
          exact zero_mem_of_root hq h0
        obtain ⟨w, hwlo, hwx⟩ : ∃ w : ℝ, (∀ l ∈ lo, l < w) ∧ w < x := by
          cases lo with
          | none =>
            obtain ⟨w, hw⟩ := exists_lt x
            exact ⟨w, by simp, hw⟩
          | some l =>
            obtain ⟨w, hw1, hw2⟩ := exists_between (by simpa using hlox l rfl)
            exact ⟨w, by simpa using hw1, hw2⟩
        have hceq : c.take (Pd :: bres).length = cpt.take (Pd :: bres).length := by
          rw [← hgap w hwlo hwx, ← hpt,
            take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g w,
            take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g x]
          refine signVec_eq_of_gap g (Pd :: bres) fun q hq h0 z hzI hzroot => ?_
          rw [min_eq_left hwx.le, max_eq_right hwx.le] at hzI
          have hzlo : ∀ l ∈ lo, l < z := fun l hl =>
            lt_of_lt_of_le (hwlo l hl) hzI.1
          have hmem := hroots q (List.mem_append_left _ hq) (hnz q hq) z hzlo hzroot
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hnorootx q hq hzroot
          · exact absurd (lt_of_le_of_lt hzI.2 (hhead z hmem)) (lt_irrefl z)
        match xs, rest, hrest with
        | [], [c'], hray =>
          obtain ⟨w', hw'⟩ := exists_gt x
          have hceq2 : cpt.take (Pd :: bres).length = c'.take (Pd :: bres).length := by
            rw [← hpt, ← hray w' (by simpa using hw'),
              take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g x,
              take_signVec_append (Pd :: bres)
                ((Pd :: bres).map fun r => emod r P) g w']
            refine signVec_eq_of_gap g (Pd :: bres) fun q hq h0 z hzI hzroot => ?_
            rw [min_eq_left hw'.le, max_eq_right hw'.le] at hzI
            have hzlo : ∀ l ∈ lo, l < z := fun l hl =>
              lt_of_lt_of_le (hlox l hl) hzI.1
            have hmem := hroots q (List.mem_append_left _ hq) (hnz q hq) z hzlo hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact hnorootx q hq hzroot
            · simp at hmem
          obtain ⟨ξk, o1', o2', o3', o4'⟩ := ih [] (some x) [c'] lo₀ sa
            (by simp) List.Pairwise.nil (by simp)
            (by
              intro Q hQ h0 z hzlo hzroot
              have hzx : x < z := hzlo x rfl
              have hmem := hroots Q hQ h0 z
                (fun l hl => lt_trans (hlox l hl) hzx) hzroot
              rw [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact absurd hzx (lt_irrefl z)
              · simp at hmem)
            hray hflank
            (fun y hy l₀ hl₀ => lt_trans (hlo₀x l₀ hl₀) (hy x rfl))
            (by
              intro y hy hex
              obtain ⟨l, hl, hyl⟩ := hex
              rw [Option.mem_def, Option.some.injEq] at hl
              subst hl
              simp only [List.headD_cons]
              rcases pending_or_beyond lo y with hpen | hby
              · rw [hpend y hy hpen, hceq, hceq2]
              · rcases lt_or_eq_of_le hyl with hylt | rfl
                · rw [← take_signVec_append (Pd :: bres)
                    ((Pd :: bres).map fun r => emod r P) g y,
                    hgap y hby hylt, hceq, hceq2]
                · rw [← take_signVec_append (Pd :: bres)
                    ((Pd :: bres).map fun r => emod r P) g y, hpt, hceq2])
          refine ⟨ξk, o1', o2', ?_, ?_⟩
          · rw [baseDrop_cons, if_neg hz]
            exact o3'
          · rw [readAnnot_cons, if_neg hz]
            exact o4'
        | x₂ :: xs₂, c' :: cpt₂ :: rest₃, ⟨hxx₂, hgap₂, hpt₂, hrest₂⟩ =>
          have hxx₂' : x < x₂ := hxx₂ x rfl
          have hceq2 : cpt.take (Pd :: bres).length = c'.take (Pd :: bres).length := by
            obtain ⟨w', hw'1, hw'2⟩ := exists_between hxx₂'
            rw [← hpt, ← hgap₂ w' (by simpa using hw'1) hw'2,
              take_signVec_append (Pd :: bres) ((Pd :: bres).map fun r => emod r P) g x,
              take_signVec_append (Pd :: bres)
                ((Pd :: bres).map fun r => emod r P) g w']
            refine signVec_eq_of_gap g (Pd :: bres) fun q hq h0 z hzI hzroot => ?_
            rw [min_eq_left hw'1.le, max_eq_right hw'1.le] at hzI
            have hzlo : ∀ l ∈ lo, l < z := fun l hl =>
              lt_of_lt_of_le (hlox l hl) hzI.1
            have hmem := hroots q (List.mem_append_left _ hq) (hnz q hq) z hzlo hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact hnorootx q hq hzroot
            · have hx₂z : x₂ ≤ z := by
                rw [List.mem_cons] at hmem
                rcases hmem with rfl | hmem
                · exact le_refl z
                · exact ((List.pairwise_cons.mp htail).1 z hmem).le
              exact absurd (lt_of_le_of_lt hzI.2 hw'2) (not_lt.mpr hx₂z)
          obtain ⟨ξk, o1', o2', o3', o4'⟩ := ih (x₂ :: xs₂) (some x)
            (c' :: cpt₂ :: rest₃) lo₀ sa
            (by simp at hlen ⊢; omega) htail
            (by
              intro l hl z hz2
              rw [Option.mem_def, Option.some.injEq] at hl
              subst hl
              exact hhead z hz2)
            (by
              intro Q hQ h0 z hzlo hzroot
              have hzx : x < z := hzlo x rfl
              have hmem := hroots Q hQ h0 z
                (fun l hl => lt_trans (hlox l hl) hzx) hzroot
              rw [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact absurd hzx (lt_irrefl z)
              · exact hmem)
            ⟨hxx₂, hgap₂, hpt₂, hrest₂⟩ hflank
            (fun y hy l₀ hl₀ => lt_trans (hlo₀x l₀ hl₀) (hy x rfl))
            (by
              intro y hy hex
              obtain ⟨l, hl, hyl⟩ := hex
              rw [Option.mem_def, Option.some.injEq] at hl
              subst hl
              simp only [List.headD_cons]
              rcases pending_or_beyond lo y with hpen | hby
              · rw [hpend y hy hpen, hceq, hceq2]
              · rcases lt_or_eq_of_le hyl with hylt | rfl
                · rw [← take_signVec_append (Pd :: bres)
                    ((Pd :: bres).map fun r => emod r P) g y,
                    hgap y hby hylt, hceq, hceq2]
                · rw [← take_signVec_append (Pd :: bres)
                    ((Pd :: bres).map fun r => emod r P) g y, hpt, hceq2])
          refine ⟨ξk, o1', o2', ?_, ?_⟩
          · rw [baseDrop_cons, if_neg hz]
            exact o3'
          · rw [readAnnot_cons, if_neg hz]
            exact o4'

/-! ### The capstone -/

/-- **The read annotation realizes the walked diagram.** From a realized diagram of
the derived family, `P :: Pd :: bres` realizes `graftWalk` of the READ annotation over
the projected-merged base diagram — every ingredient a pure function of `(D, εm, εp)`,
so on a branch with constant diagram and end tags this is ONE diagram valid
branch-wide. -/
theorem realizes_readAnnot {g : Fin n → ℝ}
    {P Pd : Polynomial (MvPolynomial (Fin n) ℝ)}
    {bres : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hd : spec g Pd = derivative (spec g P))
    (hlive : ∀ q ∈ Pd :: bres, MvPolynomial.eval g q.leadingCoeff ≠ 0)
    {εm εp : SignType} (hbot : BotSign g P εm) (htop : TopSign g P εp)
    {D : List (List SignType)}
    (h : Realizes g ((Pd :: bres) ++ (Pd :: bres).map fun r => emod r P) D) :
    Realizes g (P :: Pd :: bres)
      (graftWalk (readAnnot (Pd :: bres).length εp εm D).1
        (readAnnot (Pd :: bres).length εp εm D).2
        (baseDrop (Pd :: bres).length D)) := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  obtain ⟨ξk, _o1, o2, o3, o4⟩ := colsFrom_master g P Pd bres hd hlive εp htop
    ξ.length ξ none D none εm le_rfl hpair (by simp)
    (fun Q hQ h0 z _ hzroot => hroots Q hQ h0 z hzroot)
    hcols hbot (fun y _ l₀ hl₀ => by simp at hl₀)
    (fun y _ hex => by obtain ⟨l, hl, _⟩ := hex; simp at hl)
  exact realizes_graftWalk
    (fun Q hQ _ y hy => o2 Q hQ y (fun l hl => by simp at hl) hy)
    o3 o4

end Sundog.TarskiQE
