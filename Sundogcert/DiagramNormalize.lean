/-
# TS-QE, TS-2d-2a: padding removal — the surgery's first pitch.

The reconstruction step reads a member's signs off the recursive diagram via the root
transfer (TS-2b), which reaches exactly the samples that are ROOTS of family members. A
diagram may carry padding samples (no member vanishes there) — and the diagram itself
knows them: a point-column with no zero entry. This module removes them, branch-uniformly:

- **`dropPadding`** — the pure diagram function (fuel-structured recursion for clean
  equations): scan point-columns; keep those containing `zero`, merge away the rest.
- **`PaddingFree`** + **`dropPadding_paddingFree`** — the output has a zero in every
  point-column.
- **`realizes_dropPadding`** — realization is preserved: in the drop case no member can be
  zero at `g` (a zero member puts `zero` in every column), the dropped sample is a root of
  nothing, the neighboring columns provably agree (`signVec_eq_of_gap` across the dropped
  sample), and root coverage survives.
- **`realizes_samples_root`** — the contract for 2d-2b: in a padding-free realized diagram,
  every sample is a root of some member — the transfer reaches every sample.

**Honest fence.** 2d-2a only: the P-column augmentation (2d-2b) and the root-insertion
splice (2d-2c) are the remaining pitches of the surgery.
-/
import Sundogcert.SignDiagrams

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### The padding-removal function (fuel-structured) -/

/-- Fuel-structured padding removal. -/
def dropPaddingAux : ℕ → List (List SignType) → List (List SignType)
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [c] => [c]
  | fuel + 1, c :: cpt :: rest =>
      if SignType.zero ∈ cpt then c :: cpt :: dropPaddingAux fuel rest
      else
        match rest with
        | [] => [c]
        | _ :: rest' => dropPaddingAux fuel (c :: rest')

private theorem dropPaddingAux_congr :
    ∀ (l : List (List SignType)) (f₁ f₂ : ℕ), l.length ≤ f₁ → l.length ≤ f₂ →
    dropPaddingAux f₁ l = dropPaddingAux f₂ l := by
  suffices H : ∀ (N : ℕ) (l : List (List SignType)) (f₁ f₂ : ℕ), l.length ≤ N →
      l.length ≤ f₁ → l.length ≤ f₂ → dropPaddingAux f₁ l = dropPaddingAux f₂ l by
    exact fun l f₁ f₂ h1 h2 => H l.length l f₁ f₂ le_rfl h1 h2
  intro N
  induction N with
  | zero =>
    intro l f₁ f₂ hN h1 h2
    have h0 : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst h0
    cases f₁ <;> cases f₂ <;> rfl
  | succ N ih =>
    intro l f₁ f₂ hN h1 h2
    match l with
    | [] => cases f₁ <;> cases f₂ <;> rfl
    | [c] =>
      match f₁, f₂ with
      | 0, _ => simp at h1
      | _ + 1, 0 => simp at h2
      | g₁ + 1, g₂ + 1 => rfl
    | c :: cpt :: rest =>
      match f₁, f₂ with
      | 0, _ => simp at h1
      | _ + 1, 0 => simp at h2
      | g₁ + 1, g₂ + 1 =>
        simp only [dropPaddingAux]
        simp only [List.length_cons] at hN h1 h2
        by_cases hz : SignType.zero ∈ cpt
        · rw [if_pos hz, if_pos hz, ih rest g₁ g₂ (by omega) (by omega) (by omega)]
        · rw [if_neg hz, if_neg hz]
          match rest with
          | [] => rfl
          | c' :: rest' =>
            simp only [List.length_cons] at hN h1 h2
            exact ih (c :: rest') g₁ g₂ (by simp; omega) (by simp; omega)
              (by simp; omega)

/-- Merge away point-columns with no zero entry. -/
def dropPadding (D : List (List SignType)) : List (List SignType) :=
  dropPaddingAux D.length D

theorem dropPadding_nil : dropPadding [] = [] := rfl

theorem dropPadding_single (c : List SignType) : dropPadding [c] = [c] := rfl

theorem dropPadding_cons (c cpt : List SignType) (rest : List (List SignType)) :
    dropPadding (c :: cpt :: rest) =
      if SignType.zero ∈ cpt then c :: cpt :: dropPadding rest
      else
        match rest with
        | [] => [c]
        | _ :: rest' => dropPadding (c :: rest') := by
  unfold dropPadding
  simp only [List.length_cons, dropPaddingAux]
  by_cases hz : SignType.zero ∈ cpt
  · rw [if_pos hz, if_pos hz,
      dropPaddingAux_congr rest (rest.length + 1) rest.length (by omega) le_rfl]
  · rw [if_neg hz, if_neg hz]
    match rest with
    | [] => rfl
    | c' :: rest' =>
      exact dropPaddingAux_congr (c :: rest') (rest'.length + 1 + 1)
        (c :: rest').length (by simp) le_rfl

/-! ### Padding-freeness (fuel-structured) -/

/-- Fuel-structured padding-freeness. -/
def PaddingFreeAux : ℕ → List (List SignType) → Prop
  | 0, _ => True
  | _ + 1, _ :: cpt :: rest => SignType.zero ∈ cpt ∧ PaddingFreeAux rest.length rest
  | _ + 1, _ => True

/-- Every point-column contains a zero. -/
def PaddingFree (D : List (List SignType)) : Prop :=
  PaddingFreeAux D.length D

theorem paddingFree_nil : PaddingFree [] := trivial

theorem paddingFree_single (c : List SignType) : PaddingFree [c] := trivial

theorem paddingFree_cons (c cpt : List SignType) (rest : List (List SignType)) :
    PaddingFree (c :: cpt :: rest) ↔ (SignType.zero ∈ cpt ∧ PaddingFree rest) := by
  rw [PaddingFree, PaddingFree]
  simp only [PaddingFreeAux]

/-- The output of `dropPadding` is padding-free. -/
theorem dropPadding_paddingFree :
    ∀ D : List (List SignType), PaddingFree (dropPadding D) := by
  suffices H : ∀ (N : ℕ) (D : List (List SignType)), D.length ≤ N →
      PaddingFree (dropPadding D) by
    exact fun D => H D.length D le_rfl
  intro N
  induction N with
  | zero =>
    intro D hD
    have h0 : D = [] := List.length_eq_zero_iff.mp (by omega)
    subst h0
    rw [dropPadding_nil]
    exact paddingFree_nil
  | succ N ih =>
    intro D hD
    match D with
    | [] =>
      rw [dropPadding_nil]
      exact paddingFree_nil
    | [c] =>
      rw [dropPadding_single]
      exact paddingFree_single c
    | c :: cpt :: rest =>
      rw [dropPadding_cons]
      simp only [List.length_cons] at hD
      by_cases hz : SignType.zero ∈ cpt
      · rw [if_pos hz, paddingFree_cons]
        exact ⟨hz, ih rest (by omega)⟩
      · rw [if_neg hz]
        match rest with
        | [] => exact paddingFree_single c
        | c' :: rest' =>
          simp only [List.length_cons] at hD
          exact ih (c :: rest') (by simp; omega)

/-! ### Zero entries -/

private theorem zero_mem_signVec_of_zero {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hP : P ∈ F) (h0 : spec g P = 0) (y : ℝ) : SignType.zero ∈ signVec F g y := by
  rw [signVec]
  refine List.mem_map.mpr ⟨P, hP, ?_⟩
  rw [h0]
  simp

private theorem zero_mem_signVec_of_root {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hP : P ∈ F) {y : ℝ} (hy : (spec g P).eval y = 0) :
    SignType.zero ∈ signVec F g y := by
  rw [signVec]
  refine List.mem_map.mpr ⟨P, hP, ?_⟩
  rw [hy]
  simp

/-! ### Realization is preserved -/

private theorem colsFrom_dropPadding (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (N : ℕ) (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ξ.length ≤ N →
    ξ.Pairwise (· < ·) →
    (∀ l ∈ lo, ∀ x ∈ ξ, l < x) →
    (∀ P ∈ F, spec g P ≠ 0 → ∀ z : ℝ, (∀ l ∈ lo, l < z) →
      (spec g P).IsRoot z → z ∈ ξ) →
    ColsFrom g F lo ξ cols →
    ∃ ξ' : List ℝ, ξ'.Pairwise (· < ·) ∧ (∀ l ∈ lo, ∀ x ∈ ξ', l < x) ∧
      (∀ P ∈ F, spec g P ≠ 0 → ∀ z : ℝ, (∀ l ∈ lo, l < z) →
        (spec g P).IsRoot z → z ∈ ξ') ∧
      ColsFrom g F lo ξ' (dropPadding cols) := by
  intro N
  induction N with
  | zero =>
    intro ξ lo cols hlen hpair hlo hroots hc
    have h0 : ξ = [] := List.length_eq_zero_iff.mp (by omega)
    subst h0
    match cols, hc with
    | [], hc => exact hc.elim
    | [c], hc =>
      exact ⟨[], List.Pairwise.nil, by simp, hroots, by rw [dropPadding_single]; exact hc⟩
    | _ :: _ :: _, hc => exact hc.elim
  | succ N ih =>
    intro ξ lo cols hlen hpair hlo hroots hc
    match ξ, cols, hc with
    | [], [], hc => exact hc.elim
    | [], [c], hc =>
      exact ⟨[], List.Pairwise.nil, by simp, hroots, by rw [dropPadding_single]; exact hc⟩
    | [], _ :: _ :: _, hc => exact hc.elim
    | x :: xs, [], hc => exact hc.elim
    | x :: xs, [_], hc => exact hc.elim
    | x :: xs, c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      by_cases hz : SignType.zero ∈ cpt
      · -- keep the sample
        obtain ⟨ξ'', hpair'', hlo'', hroots'', hcols''⟩ := ih xs (some x) rest
          (by simp at hlen; omega) htail
          (by
            intro l hl z hz'
            rw [Option.mem_def, Option.some.injEq] at hl
            subst hl
            exact hhead z hz')
          (by
            intro P hP h0 z hzlo hzroot
            have hzx : x < z := by simpa using hzlo x rfl
            have hmem := hroots P hP h0 z
              (fun l hl => lt_trans (hlox l hl) hzx) hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd hzx (lt_irrefl z)
            · exact hmem)
          hrest
        refine ⟨x :: ξ'', ?_, ?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨fun z hz' => by simpa using hlo'' x rfl z hz', hpair''⟩
        · intro l hl y hy
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hlox l hl
          · exact lt_trans (hlox l hl) (by simpa using hlo'' x rfl y hy)
        · intro P hP h0 z hzlo hzroot
          have hmem := hroots P hP h0 z hzlo hzroot
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact List.mem_cons_self
          · have hzx : x < z := hhead z hmem
            exact List.mem_cons_of_mem _
              (hroots'' P hP h0 z (by simpa using hzx) hzroot)
        · rw [dropPadding_cons, if_pos hz]
          exact ⟨hlox, hgap, hpt, hcols''⟩
      · -- drop the sample
        have hnorootx : ∀ P ∈ F, ¬ (spec g P).eval x = 0 := by
          intro P hP h0
          exact hz (hpt ▸ zero_mem_signVec_of_root hP h0)
        obtain ⟨w, hwlo, hwx⟩ : ∃ w : ℝ, (∀ l ∈ lo, l < w) ∧ w < x := by
          cases lo with
          | none =>
            obtain ⟨w, hw⟩ := exists_lt x
            exact ⟨w, by simp, hw⟩
          | some l =>
            obtain ⟨w, hw1, hw2⟩ := exists_between (by simpa using hlox l rfl)
            exact ⟨w, by simpa using hw1, hw2⟩
        have hceq : c = cpt := by
          rw [← hgap w hwlo hwx, ← hpt]
          refine signVec_eq_of_gap g F fun P hP h0 z hzI hzroot => ?_
          rw [min_eq_left hwx.le, max_eq_right hwx.le] at hzI
          have hzlo : ∀ l ∈ lo, l < z := fun l hl =>
            lt_of_lt_of_le (hwlo l hl) hzI.1
          have hmem := hroots P hP h0 z hzlo hzroot
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact hnorootx P hP hzroot
          · exact absurd (lt_of_le_of_lt hzI.2 (hhead z hmem)) (lt_irrefl z)
        match xs, rest, hrest with
        | [], [c'], hray =>
          obtain ⟨w', hw'⟩ := exists_gt x
          have hceq2 : cpt = c' := by
            rw [← hpt, ← hray w' (by simpa using hw')]
            refine signVec_eq_of_gap g F fun P hP h0 z hzI hzroot => ?_
            rw [min_eq_left hw'.le, max_eq_right hw'.le] at hzI
            have hzlo : ∀ l ∈ lo, l < z := fun l hl =>
              lt_of_lt_of_le (hlox l hl) hzI.1
            have hmem := hroots P hP h0 z hzlo hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact hnorootx P hP hzroot
            · exact absurd hmem List.not_mem_nil
          refine ⟨[], List.Pairwise.nil, by simp, ?_, ?_⟩
          · intro P hP h0 z hzlo hzroot
            have hmem := hroots P hP h0 z hzlo hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd hzroot (hnorootx P hP)
            · exact absurd hmem List.not_mem_nil
          · rw [dropPadding_cons, if_neg hz]
            change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F g y = c
            intro y hy
            rcases lt_trichotomy y x with hyx | rfl | hxy
            · exact hgap y hy hyx
            · rw [hpt, hceq]
            · rw [hray y (by simpa using hxy), ← hceq2, ← hceq]
        | x₂ :: xs₂, c' :: cpt₂ :: rest₃, ⟨hxx₂, hgap₂, hpt₂, hrest₂⟩ =>
          have hxx₂' : x < x₂ := by simpa using hxx₂ x rfl
          have hceq2 : cpt = c' := by
            obtain ⟨w', hw'1, hw'2⟩ := exists_between hxx₂'
            rw [← hpt, ← hgap₂ w' (by simpa using hw'1) hw'2]
            refine signVec_eq_of_gap g F fun P hP h0 z hzI hzroot => ?_
            rw [min_eq_left hw'1.le, max_eq_right hw'1.le] at hzI
            have hzlo : ∀ l ∈ lo, l < z := fun l hl =>
              lt_of_lt_of_le (hlox l hl) hzI.1
            have hmem := hroots P hP h0 z hzlo hzroot
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact hnorootx P hP hzroot
            · have hx₂z : x₂ ≤ z := by
                rw [List.mem_cons] at hmem
                rcases hmem with rfl | hmem
                · exact le_refl z
                · exact ((List.pairwise_cons.mp htail).1 z hmem).le
              exact absurd (lt_of_le_of_lt hzI.2 hw'2) (not_lt.mpr hx₂z)
          have hmerged : ColsFrom g F lo (x₂ :: xs₂) (c :: cpt₂ :: rest₃) := by
            refine ⟨fun l hl => lt_trans (hlox l hl) hxx₂', ?_, hpt₂, hrest₂⟩
            intro y hy hyx₂
            rcases lt_trichotomy y x with hyx | rfl | hxy
            · exact hgap y hy hyx
            · rw [hpt, hceq]
            · rw [hgap₂ y (by simpa using hxy) hyx₂, ← hceq2, ← hceq]
          obtain ⟨ξ', hpair', hlo', hroots', hcols'⟩ :=
            ih (x₂ :: xs₂) lo (c :: cpt₂ :: rest₃)
            (by simp at hlen ⊢; omega) htail
            (by
              intro l hl y hy
              refine lt_trans (hlox l hl) ?_
              rw [List.mem_cons] at hy
              rcases hy with rfl | hy
              · exact hxx₂'
              · exact hhead y (List.mem_cons_of_mem _ hy))
            (by
              intro P hP h0 z hzlo hzroot
              have hmem := hroots P hP h0 z hzlo hzroot
              rw [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact absurd hzroot (hnorootx P hP)
              · exact hmem)
            hmerged
          refine ⟨ξ', hpair', hlo', hroots', ?_⟩
          rw [dropPadding_cons, if_neg hz]
          exact hcols'

/-- **Padding removal preserves realization.** -/
theorem realizes_dropPadding {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} {D : List (List SignType)}
    (h : Realizes g F D) : Realizes g F (dropPadding D) := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  obtain ⟨ξ', hpair', -, hroots', hcols'⟩ := colsFrom_dropPadding g F ξ.length ξ none D
    le_rfl hpair (by simp)
    (fun P hP h0 z _ hzroot => hroots P hP h0 z hzroot) hcols
  exact ⟨ξ', hpair', fun P hP h0 y hy => hroots' P hP h0 y (by simp) hy, hcols'⟩

/-! ### The contract for the transfer: samples carry zeros -/

private theorem colsFrom_paddingFree_zero (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g F lo ξ cols → PaddingFree cols →
    ∀ x ∈ ξ, SignType.zero ∈ signVec F g x := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc hPF x hx
    exact absurd hx List.not_mem_nil
  | cons x xs ih =>
    intro lo cols hc hPF y hy
    match cols, hc with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      rw [paddingFree_cons] at hPF
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rw [hpt]
        exact hPF.1
      · exact ih (some x) rest hrest hPF.2 y hy

/-- **Every sample of a padding-free realized diagram is a root of some member** — the
transfer (TS-2b) reaches every sample. -/
theorem realizes_samples_root {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} {D : List (List SignType)}
    (hPF : PaddingFree D) (h : Realizes g F D) :
    ∃ ξ : List ℝ, ξ.Pairwise (· < ·) ∧
      (∀ P ∈ F, spec g P ≠ 0 → ∀ y : ℝ, (spec g P).IsRoot y → y ∈ ξ) ∧
      ColsFrom g F none ξ D ∧
      ∀ x ∈ ξ, ∃ P ∈ F, (spec g P).eval x = 0 := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  refine ⟨ξ, hpair, hroots, hcols, ?_⟩
  intro x hx
  have hzero := colsFrom_paddingFree_zero g F ξ none D hcols hPF x hx
  rw [signVec] at hzero
  obtain ⟨P, hP, hPsign⟩ := List.mem_map.mp hzero
  exact ⟨P, hP, sign_eq_zero_iff.mp hPsign⟩

end Sundog.TarskiQE
