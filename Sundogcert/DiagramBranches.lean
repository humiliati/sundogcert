/-
# TS-QE, TS-2's recursion (pitch 2): the vanishing-lead branch layer.

The master needs live leads; on arbitrary `g` they vanish. The Cohen–Hörmander fix,
landed here: branch over resolutions. `resolve g q` (TS-2a) already IS the pointwise
truncation — spec-preserving (`resolve_spec`) and zero-or-live (`resolve_faithful`),
with finitely many possible values (`truncChain`). This module makes the branching
`SADef` and supplies the transports:

- **`sadef_resolve_fiber` / `sadef_resolve_cell`** — the fiber
  `{g | resolve g q = t}` is `SADef` (strong induction on the support, splitting on
  the vanishing of the leading coefficient via `resolve_of_lead_vanish` and
  `resolve_eq_self_iff`); a family cell is a `Forall₂` of fibers, `SADef` by
  intersection.
- **`resolve_cell_props`** — on a cell, members and their truncations have EQUAL
  specializations, and every truncation is zero-or-live: exactly the master's `hlive`
  contract for the live part, with zeros split off.
- **`exists_resolve_cell`** — the cover: every `g` lies in the cell of its own
  resolutions, and those live in the finite `truncChain`s.
- **`realizes_congr`** — spec-equal families share diagrams (so a diagram for the
  truncated family IS a diagram for the original, on the cell).
- **`realizes_zero_cons`** — a spec-zero member inserts as an all-zero row (so zero
  truncations rejoin the family after the machinery runs on the live part; arbitrary
  positions via `realizes_selectFam`).

**Honest fence.** Remaining: pitch 3, the Dershowitz–Manna assembly — max-degree pick,
`famDegrees_induction`, and the per-cell composition of `realizes_readAnnot` +
these transports into `DiagramPartition` for every family.
-/
import Sundogcert.DiagramSelect

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Forall₂ utilities -/

private theorem forall₂_exists_left {α β : Type*} {r : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ r l₁ l₂) {b : β} (hb : b ∈ l₂) :
    ∃ a ∈ l₁, r a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb'
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-! ### Spec-equal families share diagrams -/

private theorem signVec_congr {g : Fin n → ℝ}
    {F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hFF : List.Forall₂ (fun q₁ q₂ => spec g q₁ = spec g q₂) F₁ F₂) (y : ℝ) :
    signVec F₁ g y = signVec F₂ g y := by
  induction hFF with
  | nil => rfl
  | cons hqq _ ih => rw [signVec_cons, signVec_cons, hqq, ih]

private theorem colsFrom_congr {g : Fin n → ℝ}
    {F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hsv : ∀ y : ℝ, signVec F₁ g y = signVec F₂ g y) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g F₁ lo ξ cols → ColsFrom g F₂ lo ξ cols := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc
    match cols, hc with
    | [c], hc =>
      change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F₂ g y = c
      intro y hy
      rw [← hsv y]
      exact hc y hy
  | cons x xs ih =>
    intro lo cols hc
    match cols, hc with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      refine ⟨hlox, ?_, ?_, ih (some x) rest hrest⟩
      · intro y hy hyx
        rw [← hsv y]
        exact hgap y hy hyx
      · rw [← hsv x]
        exact hpt

/-- **Spec-equal families share diagrams.** On a resolve-cell, a diagram for the
truncated family is a diagram for the original. -/
theorem realizes_congr {g : Fin n → ℝ}
    {F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hFF : List.Forall₂ (fun q₁ q₂ => spec g q₁ = spec g q₂) F₁ F₂)
    {D : List (List SignType)} (h : Realizes g F₁ D) : Realizes g F₂ D := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  refine ⟨ξ, hpair, ?_, colsFrom_congr (signVec_congr hFF) ξ none D hcols⟩
  intro Q hQ h0 y hy
  obtain ⟨Q₁, hQ₁, hq⟩ := forall₂_exists_left hFF hQ
  exact hroots Q₁ hQ₁ (by rw [hq]; exact h0) y (hq.symm ▸ hy)

/-! ### Zero members insert as all-zero rows -/

private theorem colsFrom_zero_cons {g : Fin n → ℝ}
    {Q : Polynomial (MvPolynomial (Fin n) ℝ)} (h0 : spec g Q = 0)
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g F lo ξ cols →
    ColsFrom g (Q :: F) lo ξ (cols.map fun c => (0 : SignType) :: c) := by
  have hsv : ∀ y : ℝ, signVec (Q :: F) g y = (0 : SignType) :: signVec F g y := by
    intro y
    rw [signVec_cons, h0]
    simp
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc
    match cols, hc with
    | [c], hc =>
      change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec (Q :: F) g y = (0 : SignType) :: c
      intro y hy
      rw [hsv y, hc y hy]
  | cons x xs ih =>
    intro lo cols hc
    match cols, hc with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      refine ⟨hlox, ?_, ?_, ih (some x) rest hrest⟩
      · intro y hy hyx
        rw [hsv y, hgap y hy hyx]
      · rw [hsv x, hpt]

/-- **Zero members insert as all-zero rows** (exempt from root coverage). -/
theorem realizes_zero_cons {g : Fin n → ℝ}
    {Q : Polynomial (MvPolynomial (Fin n) ℝ)} (h0 : spec g Q = 0)
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} {D : List (List SignType)}
    (h : Realizes g F D) :
    Realizes g (Q :: F) (D.map fun c => (0 : SignType) :: c) := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  refine ⟨ξ, hpair, ?_, colsFrom_zero_cons h0 ξ none D hcols⟩
  intro R hR hR0 y hy
  rcases List.mem_cons.mp hR with rfl | hR'
  · exact absurd h0 hR0
  · exact hroots R hR' hR0 y hy

/-! ### Resolve-fibers are SADef -/

private theorem sadef_resolve_fiber_zero (t : Polynomial (MvPolynomial (Fin n) ℝ)) :
    SADef n {g : Fin n → ℝ | resolve g 0 = t} := by
  have he : ∀ g : Fin n → ℝ,
      resolve g (0 : Polynomial (MvPolynomial (Fin n) ℝ)) = 0 :=
    fun g => (resolve_eq_self_iff g 0).mpr (Or.inl rfl)
  by_cases ht : (0 : Polynomial (MvPolynomial (Fin n) ℝ)) = t
  · subst ht
    have e : {g : Fin n → ℝ | resolve g 0 = 0} = Set.univ :=
      Set.ext fun g => by simp [he g]
    rw [e]
    exact SADef.univ
  · have e : {g : Fin n → ℝ | resolve g 0 = t} = ∅ :=
      Set.ext fun g => by simp [he g, ht]
    rw [e]
    exact SADef.empty

/-- The fiber of the resolution map is semialgebraic in the parameters. -/
theorem sadef_resolve_fiber (q t : Polynomial (MvPolynomial (Fin n) ℝ)) :
    SADef n {g : Fin n → ℝ | resolve g q = t} := by
  suffices H : ∀ (N : ℕ) (q : Polynomial (MvPolynomial (Fin n) ℝ)),
      q.support.card ≤ N → SADef n {g : Fin n → ℝ | resolve g q = t} from
    H q.support.card q le_rfl
  intro N
  induction N with
  | zero =>
    intro q hq
    have h0 : q = 0 :=
      Polynomial.support_eq_empty.mp (Finset.card_eq_zero.mp (by omega))
    subst h0
    exact sadef_resolve_fiber_zero t
  | succ N ih =>
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      exact sadef_resolve_fiber_zero t
    · have e : {g : Fin n → ℝ | resolve g q = t}
          = ({g | MvPolynomial.eval g q.leadingCoeff = 0}
              ∩ {g | resolve g q.eraseLead = t})
            ∪ ({g | MvPolynomial.eval g q.leadingCoeff = 0}ᶜ
              ∩ (if q = t then Set.univ else ∅)) := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        by_cases hl : MvPolynomial.eval g q.leadingCoeff = 0
        · rw [resolve_of_lead_vanish g hq0 hl]
          simp [hl]
        · rw [(resolve_eq_self_iff g q).mpr (Or.inr hl)]
          by_cases hqt : q = t
          · exact iff_of_true hqt
              (Or.inr ⟨hl, by rw [if_pos hqt]; exact Set.mem_univ g⟩)
          · refine iff_of_false hqt ?_
            rintro (⟨h1, -⟩ | ⟨-, h2⟩)
            · exact hl h1
            · rw [if_neg hqt] at h2
              simp at h2
      rw [e]
      refine ((SADef.zero _).inter (ih q.eraseLead ?_)).union
        (((SADef.zero _).compl).inter ?_)
      · have := Polynomial.eraseLead_support_card_lt hq0
        omega
      · by_cases hqt : q = t
        · rw [if_pos hqt]
          exact SADef.univ
        · rw [if_neg hqt]
          exact SADef.empty

/-- A family's resolve-cell is SADef. -/
theorem sadef_resolve_cell (F T : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    SADef n {g : Fin n → ℝ | List.Forall₂ (fun q t => resolve g q = t) F T} := by
  induction F generalizing T with
  | nil =>
    match T with
    | [] =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q t => resolve g q = t) [] []} = Set.univ :=
        Set.ext fun g => by simp
      rw [e]
      exact SADef.univ
    | t :: T =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q t => resolve g q = t) [] (t :: T)} = ∅ :=
        Set.ext fun g => by simp
      rw [e]
      exact SADef.empty
  | cons q F ih =>
    match T with
    | [] =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q t => resolve g q = t) (q :: F) []} = ∅ :=
        Set.ext fun g => by simp
      rw [e]
      exact SADef.empty
    | t :: T =>
      have e : {g : Fin n → ℝ |
          List.Forall₂ (fun q' t' => resolve g q' = t') (q :: F) (t :: T)}
          = {g | resolve g q = t}
            ∩ {g | List.Forall₂ (fun q' t' => resolve g q' = t') F T} :=
        Set.ext fun g => by simp [List.forall₂_cons]
      rw [e]
      exact (sadef_resolve_fiber q t).inter (ih T)

/-! ### The per-cell package and the cover -/

/-- On a resolve-cell: members and truncations have equal specializations, and every
truncation is zero-or-live — the master's contract. -/
theorem resolve_cell_props {g : Fin n → ℝ}
    {F T : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hcell : List.Forall₂ (fun q t => resolve g q = t) F T) :
    List.Forall₂ (fun q t => spec g q = spec g t) F T ∧
      ∀ t ∈ T, t = 0 ∨ MvPolynomial.eval g t.leadingCoeff ≠ 0 := by
  constructor
  · refine List.Forall₂.imp ?_ hcell
    intro q t hqt
    rw [← hqt, resolve_spec]
  · intro t ht
    obtain ⟨q, _, hqt⟩ := forall₂_exists_left hcell ht
    rw [← hqt]
    exact resolve_faithful g q

/-- **The cover**: every `g` lies in the cell of its own resolutions, which live in
the finite truncation chains. -/
theorem exists_resolve_cell (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∃ T : List (Polynomial (MvPolynomial (Fin n) ℝ)),
      List.Forall₂ (fun q t => resolve g q = t) F T ∧
      List.Forall₂ (fun q t => t ∈ truncChain q) F T := by
  induction F with
  | nil => exact ⟨[], List.Forall₂.nil, List.Forall₂.nil⟩
  | cons q F ih =>
    obtain ⟨T, h1, h2⟩ := ih
    exact ⟨resolve g q :: T, List.Forall₂.cons rfl h1,
      List.Forall₂.cons (resolve_mem_truncChain g q) h2⟩

end Sundog.TarskiQE
