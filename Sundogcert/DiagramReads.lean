/-
# TS-QE, TS-2d-3 (the assembly, first pitch): the reads — GraftData from columns.

`realizes_graftWalk` consumes `GraftData`; `exists_graftData` produced it FROM `g`.
This module produces the annotation FROM COLUMN DATA — the functions the fused
induction will run, each with its correctness receipt:

- **`readZeroIdx` / `readPtSign` / `readPtSign_correct`** — the sample read: find the
  first base-prefix zero at position `i`, output the entry at `base.length + i`; by
  `column_reads_sample_sign` that entry IS `P`'s sign at the sample. A pure function of
  the column — the `sP` entries of `GraftData`, diagram-side.
- **`headD_reads_gap_sign`** — the gap read: with the family `Pd`-headed, the
  derivative's sign on a gap is `headD` of the gap column — the `σ'` input of
  `readPlan`, diagram-side.
- **`baseDrop` / `readAnnot`** — the two walk functions (structural, no fuel): project
  kept columns to the base, merge unkept point columns away; emit the sample reads and
  the `readPlan`s (the σ' read comes from the gap column adjacent to the closing kept
  sample — sound because the derivative has no roots at dropped samples).
- **`colsFrom_widen`** — barrier widening: a `ColsFrom` from an inner barrier extends
  to an outer one given the gap equation on the added stretch.

**The fused master (next pitch).** One strong induction over the full derived diagram
producing `ColsFrom g base lo ξk (baseDrop m cols)` and
`GraftData g P lo ξk (readAnnot m εp sa cols)` together. Design note, settled here: in
the drop case the annotation CANNOT be restated at the intermediate barrier (`P`'s
grafted root may lie left of a dropped sample), so the induction carries a pending-gap
accumulator — the last kept barrier `lo₀`, its flank tag `sa` (`FlankTag`-style:
`BotSign` at `none`, sample sign at `some`), and the pending projected gap column with
its no-zero invariant — and discharges plan validity only at keep time, over the whole
merged gap, via `readPlan_valid_*`; `colsFrom_widen` reattaches the output barriers.
-/
import Sundogcert.DiagramDescent

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### The sample read -/

/-- Index of the first `zero` among the first `m` entries. -/
def readZeroIdx : ℕ → List SignType → Option ℕ
  | 0, _ => none
  | _ + 1, [] => none
  | m + 1, s :: rest =>
      if s = SignType.zero then some 0 else (readZeroIdx m rest).map (· + 1)

theorem readZeroIdx_spec :
    ∀ (m : ℕ) (c : List SignType) (i : ℕ), readZeroIdx m c = some i →
      i < m ∧ c[i]? = some SignType.zero := by
  intro m
  induction m with
  | zero =>
    intro c i h
    simp [readZeroIdx] at h
  | succ m ih =>
    intro c i h
    match c with
    | [] => simp [readZeroIdx] at h
    | s :: rest =>
      simp only [readZeroIdx] at h
      by_cases hs : s = SignType.zero
      · rw [if_pos hs] at h
        have h0 : (0 : ℕ) = i := Option.some_injective _ h
        subst h0
        refine ⟨Nat.succ_pos m, ?_⟩
        rw [hs]
        rfl
      · rw [if_neg hs] at h
        match hr : readZeroIdx m rest with
        | none =>
          rw [hr] at h
          simp at h
        | some j =>
          rw [hr] at h
          have hj1 : j + 1 = i := Option.some_injective _ h
          subst hj1
          obtain ⟨hjm, hj⟩ := ih rest j hr
          exact ⟨by omega, by simpa using hj⟩

theorem readZeroIdx_isSome :
    ∀ (m : ℕ) (c : List SignType), SignType.zero ∈ c.take m →
      ∃ i : ℕ, readZeroIdx m c = some i := by
  intro m
  induction m with
  | zero =>
    intro c h
    simp at h
  | succ m ih =>
    intro c h
    match c with
    | [] => simp at h
    | s :: rest =>
      rw [List.take_succ_cons] at h
      by_cases hs : s = SignType.zero
      · exact ⟨0, by simp only [readZeroIdx]; rw [if_pos hs]⟩
      · rcases List.mem_cons.mp h with heq | hmem
        · exact absurd heq.symm hs
        · obtain ⟨j, hj⟩ := ih rest hmem
          refine ⟨j + 1, ?_⟩
          simp only [readZeroIdx]
          rw [if_neg hs, hj]
          rfl

/-- The sample read: the remainder entry paired to the first base-prefix zero. -/
def readPtSign (m : ℕ) (c : List SignType) : SignType :=
  match readZeroIdx m c with
  | some i => (c[m + i]?).getD 0
  | none => 0

/-- **The sample read is `P`'s sign.** On a full point column of the derived family
(layout `base ++ base.map (emod · P)`, live base leads) with a base-prefix zero, the
read equals `P`'s sign at the sample. -/
theorem readPtSign_correct (g : Fin n → ℝ)
    {base : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) {x : ℝ}
    (hlive : ∀ q ∈ base, MvPolynomial.eval g q.leadingCoeff ≠ 0)
    (hz : SignType.zero ∈
      (signVec (base ++ base.map fun r => emod r P) g x).take base.length) :
    readPtSign base.length (signVec (base ++ base.map fun r => emod r P) g x)
      = SignType.sign ((spec g P).eval x) := by
  obtain ⟨i, hi⟩ := readZeroIdx_isSome base.length _ hz
  obtain ⟨him, hci⟩ := readZeroIdx_spec base.length _ i hi
  have hq : base[i]? = some base[i] := List.getElem?_eq_getElem him
  have hread : readPtSign base.length (signVec (base ++ base.map fun r => emod r P) g x)
      = ((signVec (base ++ base.map fun r => emod r P) g x)[base.length + i]?).getD 0 := by
    unfold readPtSign
    rw [hi]
  rw [hread, column_reads_sample_sign g P hlive hq hci]
  rfl

/-! ### The gap read -/

/-- With the family `Pd`-headed, the derivative's gap sign is `headD` of the column. -/
theorem headD_reads_gap_sign (g : Fin n → ℝ)
    (Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (F₁ : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    {c : List SignType} {y : ℝ} (hcol : signVec (Pd :: F₁) g y = c) :
    SignType.sign ((spec g Pd).eval y) = c.headD 0 := by
  rw [← hcol, signVec_cons, List.headD_cons]

/-! ### The walk functions -/

/-- Project-and-merge: keep point columns with a base-prefix zero (projected to the
base), merge the rest away; the emitted gap column is the one adjacent to the closing
kept sample. -/
def baseDrop (m : ℕ) : List (List SignType) → List (List SignType)
  | [] => []
  | [c] => [c.take m]
  | c :: cpt :: rest =>
      if SignType.zero ∈ cpt.take m then c.take m :: cpt.take m :: baseDrop m rest
      else
        match rest with
        | [] => [c.take m]
        | _ :: _ => baseDrop m rest

/-- The annotation read off the full diagram: sample reads at kept point columns,
`readPlan`s from the adjacent gap reads, the carried left flank `sa`, and the end tag
`εp`. -/
def readAnnot (m : ℕ) (εp : SignType) : SignType → List (List SignType) →
    List SignType × List GapPlan
  | _, [] => ([], [])
  | sa, [c] => ([], [readPlan (c.headD 0) sa εp])
  | sa, c :: cpt :: rest =>
      if SignType.zero ∈ cpt.take m then
        (readPtSign m cpt :: (readAnnot m εp (readPtSign m cpt) rest).1,
          readPlan (c.headD 0) sa (readPtSign m cpt)
            :: (readAnnot m εp (readPtSign m cpt) rest).2)
      else
        match rest with
        | [] => ([], [readPlan (c.headD 0) sa εp])
        | _ :: _ => readAnnot m εp sa rest

/-! ### Barrier widening -/

/-- A `ColsFrom` from an inner barrier extends to an outer one, given the gap
equation on the added stretch. -/
theorem colsFrom_widen (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    {lo : Option ℝ} {x : ℝ} {ξ : List ℝ} {b : List SignType}
    {cols : List (List SignType)}
    (h : ColsFrom g F (some x) ξ (b :: cols))
    (hlo : ∀ l ∈ lo, l < x)
    (hext : ∀ y : ℝ, (∀ l ∈ lo, l < y) → y ≤ x → signVec F g y = b) :
    ColsFrom g F lo ξ (b :: cols) := by
  match ξ, cols, h with
  | [], [], hray =>
    change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F g y = b
    intro y hy
    rcases le_or_gt y x with hyx | hxy
    · exact hext y hy hyx
    · exact hray y (some_mem_lt hxy)
  | [], _ :: _, h => exact h.elim
  | x₂ :: xs, cpt :: rest, ⟨hbar, hgap, hpt, hrest⟩ =>
    have hxx₂ : x < x₂ := hbar x rfl
    refine ⟨fun l hl => lt_trans (hlo l hl) hxx₂, ?_, hpt, hrest⟩
    intro y hy hyx₂
    rcases le_or_gt y x with hyx | hxy
    · exact hext y hy hyx
    · exact hgap y (some_mem_lt hxy) hyx₂

end Sundog.TarskiQE
