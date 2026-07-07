/-
# TS-QE, TS-2d-1: sign diagrams — the summit's base camp.

The elimination's target and its data structures, plus the first rung of the induction:

- **`SADef`** — quantifier-free semialgebraic subsets of the parameter space (an inductive
  closure in the R1 `PolyDef` style: polynomial strict-positivity atoms, complement, union),
  with the closure algebra (`inter`, `zero`, `signEq`, finite list unions/intersections).
- **`signVec`/`ColsFrom`/`Realizes`** — the sign diagram of a specialized family along the
  line: sample points `ξ` (strictly increasing, containing every root of every nonzero
  member) and the alternating column list `[ray, pt, gap, pt, …, ray]` of sign vectors.
- **`exists_diagram`** — every parameter point realizes some diagram (sorted roots + IVT
  constancy on the gaps).
- **`realizes_exists_iff`** — a diagram answers the existential sign query: `∃ y` with sign
  vector `σ` iff `σ` is a column (gap and ray columns are witnessed because cells are
  nonempty).
- **`DiagramPartition` + `elim_of_diagramPartition`** — THE SUMMIT STATEMENT: finitely many
  `SADef` branches, each carrying one diagram valid across the branch. From it, the
  elimination is a corollary: the `∃`-set is the finite union of the branches whose diagram
  contains `σ`. The Cohen–Hörmander induction proving `DiagramPartition` for every family
  is 2d-2/2d-3 (measure: Dershowitz–Manna on `famDegrees`).
- **`diagramPartition_of_constants`** — the base case: a family of `y`-degree-0 polynomials
  has the one-column diagram per coefficient-sign branch (`allSignVecs` enumeration).

**Honest fence.** 2d-1 only: the reconstruction step (2d-2) and the descent assembly (2d-3)
are the remaining climb; `QE_COMBINATORICS_WALL` watches there.
-/
import Sundogcert.PolyDerivZones

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Quantifier-free semialgebraic parameter sets -/

/-- Quantifier-free semialgebraic subsets of the parameter space. -/
inductive SADef (n : ℕ) : Set (Fin n → ℝ) → Prop
  | pos (f : MvPolynomial (Fin n) ℝ) : SADef n {g | 0 < MvPolynomial.eval g f}
  | compl {s : Set (Fin n → ℝ)} : SADef n s → SADef n sᶜ
  | union {s t : Set (Fin n → ℝ)} : SADef n s → SADef n t → SADef n (s ∪ t)

namespace SADef

theorem inter {s t : Set (Fin n → ℝ)} (hs : SADef n s) (ht : SADef n t) :
    SADef n (s ∩ t) := by
  have h := (hs.compl.union ht.compl).compl
  rwa [Set.compl_union, compl_compl, compl_compl] at h

theorem empty : SADef n (∅ : Set (Fin n → ℝ)) := by
  have h := SADef.pos (n := n) 0
  have e : {g : Fin n → ℝ | 0 < MvPolynomial.eval g 0} = ∅ := by
    ext g
    simp
  rwa [e] at h

theorem univ : SADef n (Set.univ : Set (Fin n → ℝ)) := by
  have h := (empty (n := n)).compl
  rwa [Set.compl_empty] at h

theorem neg (f : MvPolynomial (Fin n) ℝ) :
    SADef n {g | MvPolynomial.eval g f < 0} := by
  have h := SADef.pos (-f)
  have e : {g : Fin n → ℝ | 0 < MvPolynomial.eval g (-f)}
      = {g | MvPolynomial.eval g f < 0} := by
    ext g
    simp
  rwa [e] at h

theorem zero (f : MvPolynomial (Fin n) ℝ) :
    SADef n {g | MvPolynomial.eval g f = 0} := by
  have h := ((SADef.pos f).union (neg f)).compl
  have e : ({g : Fin n → ℝ | 0 < MvPolynomial.eval g f}
      ∪ {g | MvPolynomial.eval g f < 0})ᶜ = {g | MvPolynomial.eval g f = 0} := by
    ext g
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
    · intro h
      rw [h]
      exact ⟨le_refl 0, le_refl 0⟩
  rwa [e] at h

/-- The sign-condition atom. -/
theorem signEq (f : MvPolynomial (Fin n) ℝ) (s : SignType) :
    SADef n {g | SignType.sign (MvPolynomial.eval g f) = s} := by
  cases s
  · have e : {g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g f) = SignType.zero}
        = {g | MvPolynomial.eval g f = 0} := by
      ext g
      simp [sign_eq_zero_iff]
    rw [e]
    exact zero f
  · have e : {g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g f) = SignType.neg}
        = {g | MvPolynomial.eval g f < 0} := by
      ext g
      simp [sign_eq_neg_one_iff]
    rw [e]
    exact neg f
  · have e : {g : Fin n → ℝ | SignType.sign (MvPolynomial.eval g f) = SignType.pos}
        = {g | 0 < MvPolynomial.eval g f} := by
      ext g
      simp [sign_eq_one_iff]
    rw [e]
    exact SADef.pos f

theorem list_biUnion {α : Type*} {l : List α} {f : α → Set (Fin n → ℝ)}
    (h : ∀ a ∈ l, SADef n (f a)) : SADef n (⋃ a ∈ l, f a) := by
  induction l with
  | nil =>
    have e : (⋃ a ∈ ([] : List α), f a) = (∅ : Set (Fin n → ℝ)) := by
      simp
    rw [e]
    exact empty
  | cons a l ih =>
    have e : (⋃ x ∈ (a :: l), f x) = f a ∪ ⋃ x ∈ l, f x := by
      ext g
      simp [List.mem_cons]
    rw [e]
    exact (h a List.mem_cons_self).union (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

end SADef

/-! ### Sign vectors and diagrams -/

/-- The sign vector of the specialized family at height `y`. -/
noncomputable def signVec (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (g : Fin n → ℝ) (y : ℝ) : List SignType :=
  F.map fun P => SignType.sign ((spec g P).eval y)

/-- The columns of a diagram along sample points, to the right of an optional barrier:
`[gap, pt, gap, pt, …, final ray]`. -/
def ColsFrom (g : Fin n → ℝ) (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    Option ℝ → List ℝ → List (List SignType) → Prop
  | lo, [], cols =>
      match cols with
      | [c] => ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F g y = c
      | _ => False
  | lo, x :: xs, cols =>
      match cols with
      | c :: cpt :: rest =>
          (∀ l ∈ lo, l < x) ∧
          (∀ y : ℝ, (∀ l ∈ lo, l < y) → y < x → signVec F g y = c) ∧
          signVec F g x = cpt ∧ ColsFrom g F (some x) xs rest
      | _ => False

/-- `D` is a sign diagram for the family at `g`: strictly increasing sample points
containing every root of every nonzero member, with the column pattern `D`. -/
def Realizes (g : Fin n → ℝ) (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (D : List (List SignType)) : Prop :=
  ∃ ξ : List ℝ, ξ.Pairwise (· < ·) ∧
    (∀ P ∈ F, spec g P ≠ 0 → ∀ y : ℝ, (spec g P).IsRoot y → y ∈ ξ) ∧
    ColsFrom g F none ξ D

/-! ### Gap constancy -/

theorem sign_eq_of_no_root_Icc (p : ℝ[X]) {y y' : ℝ} (hle : y ≤ y')
    (hfree : ∀ z ∈ Set.Icc y y', ¬ p.IsRoot z) :
    SignType.sign (p.eval y) = SignType.sign (p.eval y') := by
  have hy : p.eval y ≠ 0 := hfree y (Set.left_mem_Icc.mpr hle)
  have hy' : p.eval y' ≠ 0 := hfree y' (Set.right_mem_Icc.mpr hle)
  rcases lt_or_gt_of_ne hy with h1 | h1 <;> rcases lt_or_gt_of_ne hy' with h2 | h2
  · rw [sign_neg h1, sign_neg h2]
  · exfalso
    obtain ⟨z, hzI, hz⟩ := intermediate_value_Icc hle p.continuous.continuousOn
      (Set.mem_Icc.mpr ⟨h1.le, h2.le⟩)
    exact hfree z hzI hz
  · exfalso
    obtain ⟨z, hzI, hz⟩ := intermediate_value_Icc' hle p.continuous.continuousOn
      (Set.mem_Icc.mpr ⟨h2.le, h1.le⟩)
    exact hfree z hzI hz
  · rw [sign_pos h1, sign_pos h2]

/-- Sign vectors agree across a root-free stretch (zero members trivially so). -/
theorem signVec_eq_of_gap (g : Fin n → ℝ) (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    {y y' : ℝ}
    (h : ∀ P ∈ F, spec g P ≠ 0 →
      ∀ z ∈ Set.Icc (min y y') (max y y'), ¬ (spec g P).IsRoot z) :
    signVec F g y = signVec F g y' := by
  rw [signVec, signVec]
  refine List.map_congr_left fun P hP => ?_
  by_cases h0 : spec g P = 0
  · rw [h0]
    simp
  · rcases le_total y y' with hle | hle
    · refine sign_eq_of_no_root_Icc _ hle fun z hz => h P hP h0 z ?_
      rw [min_eq_left hle, max_eq_right hle]
      exact hz
    · refine (sign_eq_of_no_root_Icc _ hle fun z hz => h P hP h0 z ?_).symm
      rw [min_eq_right hle, max_eq_left hle]
      exact hz

/-! ### Every point has a diagram -/

private theorem finite_specRoots (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    {y : ℝ | ∃ P ∈ F, spec g P ≠ 0 ∧ (spec g P).IsRoot y}.Finite := by
  have he : {y : ℝ | ∃ P ∈ F, spec g P ≠ 0 ∧ (spec g P).IsRoot y}
      = ⋃ P ∈ F, {y : ℝ | spec g P ≠ 0 ∧ (spec g P).IsRoot y} := by
    ext y
    simp
    tauto
  rw [he]
  refine Set.Finite.biUnion F.finite_toSet fun P hP => ?_
  by_cases h0 : spec g P = 0
  · have he2 : {y : ℝ | spec g P ≠ 0 ∧ (spec g P).IsRoot y} = ∅ := by
      ext y
      simp [h0]
    rw [he2]
    exact Set.finite_empty
  · exact (Polynomial.finite_setOf_isRoot h0).subset fun y hy => hy.2

private theorem colsFrom_exists (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ), ξ.Pairwise (· < ·) →
    (∀ l ∈ lo, ∀ x ∈ ξ, l < x) →
    (∀ P ∈ F, spec g P ≠ 0 → ∀ z : ℝ, (∀ l ∈ lo, l < z) →
      (spec g P).IsRoot z → z ∈ ξ) →
    ∃ cols, ColsFrom g F lo ξ cols := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo hpair hlo hroots
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, ∀ l ∈ lo, l < y₀ := by
      cases lo with
      | none => exact ⟨0, by simp⟩
      | some l =>
        obtain ⟨y₀, hy₀⟩ := exists_gt l
        exact ⟨y₀, by simpa using hy₀⟩
    refine ⟨[signVec F g y₀], ?_⟩
    change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F g y = signVec F g y₀
    intro y hy
    refine signVec_eq_of_gap g F fun P hP h0 z hz hroot => ?_
    have hzlo : ∀ l ∈ lo, l < z := by
      intro l hl
      have h1 := hy l hl
      have h2 := hy₀ l hl
      rcases le_total y y₀ with hle | hle
      · rw [min_eq_left hle] at hz
        exact lt_of_lt_of_le h1 hz.1
      · rw [min_eq_right hle] at hz
        exact lt_of_lt_of_le h2 hz.1
    exact absurd (hroots P hP h0 z hzlo hroot) (List.not_mem_nil)
  | cons x xs ih =>
    intro lo hpair hlo hroots
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    -- a witness in the gap below x
    obtain ⟨w, hwlo, hwx⟩ : ∃ w : ℝ, (∀ l ∈ lo, l < w) ∧ w < x := by
      cases lo with
      | none =>
        obtain ⟨w, hw⟩ := exists_lt x
        exact ⟨w, by simp, hw⟩
      | some l =>
        obtain ⟨w, hw1, hw2⟩ := exists_between (by simpa using hlo l rfl x List.mem_cons_self)
        exact ⟨w, by simpa using hw1, hw2⟩
    obtain ⟨cols, hcols⟩ := ih (some x) htail
      (by
        intro l hl z hz
        rw [Option.mem_def, Option.some.injEq] at hl
        subst hl
        exact hhead z hz)
      (by
        intro P hP h0 z hzlo hroot
        have hzx : x < z := by simpa using hzlo x rfl
        have := hroots P hP h0 z
          (fun l hl => lt_trans (hlo l hl x List.mem_cons_self) hzx) hroot
        rw [List.mem_cons] at this
        rcases this with rfl | h
        · exact absurd hzx (lt_irrefl z)
        · exact h)
    refine ⟨signVec F g w :: signVec F g x :: cols,
      fun l hl => hlo l hl x List.mem_cons_self, ?_, rfl, hcols⟩
    intro y hy hyx
    refine signVec_eq_of_gap g F fun P hP h0 z hz hroot => ?_
    have hzlo : ∀ l ∈ lo, l < z := by
      intro l hl
      rcases le_total y w with hle | hle
      · rw [min_eq_left hle] at hz
        exact lt_of_lt_of_le (hy l hl) hz.1
      · rw [min_eq_right hle] at hz
        exact lt_of_lt_of_le (hwlo l hl) hz.1
    have hzx : z < x := by
      rcases le_total y w with hle | hle
      · rw [max_eq_right hle] at hz
        exact lt_of_le_of_lt hz.2 hwx
      · rw [max_eq_left hle] at hz
        exact lt_of_le_of_lt hz.2 hyx
    have hmem := hroots P hP h0 z hzlo hroot
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact absurd hzx (lt_irrefl z)
    · exact absurd (hhead z hmem) (not_lt.mpr hzx.le)

/-- **Every parameter point realizes a diagram.** -/
theorem exists_diagram (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (g : Fin n → ℝ) : ∃ D, Realizes g F D := by
  classical
  have hfin := finite_specRoots g F
  set ξ := hfin.toFinset.sort (· ≤ ·) with hξdef
  have hpair : ξ.Pairwise (· < ·) := hfin.toFinset.sortedLT_sort.pairwise
  have hroots : ∀ P ∈ F, spec g P ≠ 0 → ∀ y : ℝ, (spec g P).IsRoot y → y ∈ ξ := by
    intro P hP h0 y hy
    rw [hξdef, Finset.mem_sort, Set.Finite.mem_toFinset]
    exact ⟨P, hP, h0, hy⟩
  obtain ⟨cols, hcols⟩ := colsFrom_exists g F ξ none hpair (by simp)
    (fun P hP h0 z _ hroot => hroots P hP h0 z hroot)
  exact ⟨cols, ξ, hpair, hroots, hcols⟩

/-! ### A diagram answers the existential sign query -/

private theorem colsFrom_covers (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g F lo ξ cols → ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F g y ∈ cols := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc y hy
    match cols, hc with
    | [c], hc =>
      rw [hc y hy]
      exact List.mem_singleton.mpr rfl
  | cons x xs ih =>
    intro lo cols hc y hy
    match cols, hc with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      rcases lt_trichotomy y x with hyx | rfl | hxy
      · rw [hgap y hy hyx]
        exact List.mem_cons_self
      · rw [hpt]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · have h := ih (some x) rest hrest y (by simpa using hxy)
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

private theorem colsFrom_witness (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g F lo ξ cols →
    ∀ c ∈ cols, ∃ y : ℝ, (∀ l ∈ lo, l < y) ∧ signVec F g y = c := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc c hcmem
    match cols, hc with
    | [c'], hc =>
      rw [List.mem_singleton] at hcmem
      subst hcmem
      obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, ∀ l ∈ lo, l < y₀ := by
        cases lo with
        | none => exact ⟨0, by simp⟩
        | some l =>
          obtain ⟨y₀, hy₀⟩ := exists_gt l
          exact ⟨y₀, by simpa using hy₀⟩
      exact ⟨y₀, hy₀, hc y₀ hy₀⟩
  | cons x xs ih =>
    intro lo cols hc c hcmem
    match cols, hc with
    | c' :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      rw [List.mem_cons] at hcmem
      rcases hcmem with rfl | hcmem
      · obtain ⟨w, hwlo, hwx⟩ : ∃ w : ℝ, (∀ l ∈ lo, l < w) ∧ w < x := by
          cases lo with
          | none =>
            obtain ⟨w, hw⟩ := exists_lt x
            exact ⟨w, by simp, hw⟩
          | some l =>
            obtain ⟨w, hw1, hw2⟩ := exists_between (by simpa using hlox l rfl)
            exact ⟨w, by simpa using hw1, hw2⟩
        exact ⟨w, hwlo, hgap w hwlo hwx⟩
      rw [List.mem_cons] at hcmem
      rcases hcmem with rfl | hcmem
      · exact ⟨x, hlox, hpt⟩
      · obtain ⟨y, hylo, hy⟩ := ih (some x) rest hrest c hcmem
        refine ⟨y, fun l hl => ?_, hy⟩
        have hxy : x < y := by simpa using hylo x rfl
        exact lt_trans (hlox l hl) hxy

/-- **A diagram answers the existential sign query.** -/
theorem realizes_exists_iff {g : Fin n → ℝ}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} {D : List (List SignType)}
    (hD : Realizes g F D) (σ : List SignType) :
    (∃ y : ℝ, signVec F g y = σ) ↔ σ ∈ D := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := hD
  constructor
  · rintro ⟨y, rfl⟩
    exact colsFrom_covers g F ξ none D hcols y (by simp)
  · intro hσ
    obtain ⟨y, -, hy⟩ := colsFrom_witness g F ξ none D hcols σ hσ
    exact ⟨y, hy⟩

/-! ### The summit statement and the elimination reduction -/

/-- **THE PARAMETRIC SIGN-DIAGRAM STATEMENT** (to be proven for every family by the
Cohen–Hörmander induction, 2d-2/2d-3): finitely many semialgebraic branches, each carrying
one diagram valid across the whole branch. -/
def DiagramPartition (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) : Prop :=
  ∃ branches : List (Set (Fin n → ℝ) × List (List SignType)),
    (∀ b ∈ branches, SADef n b.1 ∧ ∀ g ∈ b.1, Realizes g F b.2) ∧
    (∀ g : Fin n → ℝ, ∃ b ∈ branches, g ∈ b.1)

/-- **The elimination, given the summit**: the existential sign set is the finite union of
the branches whose diagram contains the queried column. -/
theorem elim_of_diagramPartition {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (h : DiagramPartition F) (σ : List SignType) :
    SADef n {g | ∃ y : ℝ, signVec F g y = σ} := by
  classical
  obtain ⟨branches, hbr, hcover⟩ := h
  have he : {g | ∃ y : ℝ, signVec F g y = σ}
      = ⋃ b ∈ branches.filter (fun b => σ ∈ b.2), b.1 := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, hbmem, hbg⟩ := hcover g
      refine ⟨b, ⟨hbmem, ?_⟩, hbg⟩
      exact (realizes_exists_iff ((hbr b hbmem).2 g hbg) σ).mp ⟨y, hy⟩
    · rintro ⟨b, ⟨hbmem, hbσ⟩, hbg⟩
      exact (realizes_exists_iff ((hbr b hbmem).2 g hbg) σ).mpr hbσ
  rw [he]
  exact SADef.list_biUnion fun b hb =>
    (hbr b (List.mem_of_mem_filter hb)).1

/-! ### The base case: constant families -/

/-- All sign vectors of a given length. -/
def allSignVecs : ℕ → List (List SignType)
  | 0 => [[]]
  | k + 1 => (allSignVecs k).flatMap fun v =>
      [SignType.neg :: v, SignType.zero :: v, SignType.pos :: v]

theorem mem_allSignVecs : ∀ {k : ℕ} {τ : List SignType}, τ.length = k → τ ∈ allSignVecs k
  | 0, [], _ => List.mem_singleton.mpr rfl
  | k + 1, t :: ts, h => by
    have hts : ts ∈ allSignVecs k := mem_allSignVecs (by simpa using h)
    refine List.mem_flatMap.mpr ⟨ts, hts, ?_⟩
    cases t <;> simp

private theorem SADef_mapSign (l : List (MvPolynomial (Fin n) ℝ)) (τ : List SignType) :
    SADef n {g | l.map (fun c => SignType.sign (MvPolynomial.eval g c)) = τ} := by
  induction l generalizing τ with
  | nil =>
    cases τ with
    | nil =>
      have e : {g : Fin n → ℝ | ([] : List (MvPolynomial (Fin n) ℝ)).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = []} = Set.univ := by
        ext g
        simp
      rw [e]
      exact SADef.univ
    | cons t ts =>
      have e : {g : Fin n → ℝ | ([] : List (MvPolynomial (Fin n) ℝ)).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = t :: ts} = ∅ := by
        ext g
        simp
      rw [e]
      exact SADef.empty
  | cons c cs ih =>
    cases τ with
    | nil =>
      have e : {g : Fin n → ℝ | (c :: cs).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = []} = ∅ := by
        ext g
        simp
      rw [e]
      exact SADef.empty
    | cons t ts =>
      have e : {g : Fin n → ℝ | (c :: cs).map
          (fun c => SignType.sign (MvPolynomial.eval g c)) = t :: ts}
          = {g | SignType.sign (MvPolynomial.eval g c) = t}
            ∩ {g | cs.map (fun c => SignType.sign (MvPolynomial.eval g c)) = ts} := by
        ext g
        simp
      rw [e]
      exact (SADef.signEq c t).inter (ih ts)

/-- **The base case: a constant family has a diagram partition.** -/
theorem diagramPartition_of_constants (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (hF : ∀ P ∈ F, P.natDegree = 0) : DiagramPartition F := by
  classical
  refine ⟨(allSignVecs F.length).map fun τ =>
    ({g | F.map (fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))) = τ}, [τ]),
    ?_, ?_⟩
  · rintro b hb
    obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hb
    constructor
    · have e : {g : Fin n → ℝ | F.map
          (fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))) = τ}
          = {g | (F.map (fun P => P.coeff 0)).map
              (fun c => SignType.sign (MvPolynomial.eval g c)) = τ} := by
        ext g
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, List.map_map]
        rfl
      rw [e]
      exact SADef_mapSign _ τ
    · intro g hg
      refine ⟨[], List.Pairwise.nil, ?_, ?_⟩
      · intro P hP h0 y hy
        exfalso
        apply h0
        have hC := Polynomial.eq_C_of_natDegree_eq_zero (hF P hP)
        rw [hC] at hy ⊢
        rw [spec, Polynomial.map_C] at hy ⊢
        have hc0 : MvPolynomial.eval g (P.coeff 0) = 0 := by
          have h' := hy
          simp only [Polynomial.IsRoot, Polynomial.eval_C] at h'
          exact h'
        rw [hc0, Polynomial.C_0]
      · change ∀ y : ℝ, (∀ l ∈ (none : Option ℝ), l < y) → signVec F g y = τ
        intro y _
        rw [← hg, signVec]
        refine List.map_congr_left fun P hP => ?_
        have hC := Polynomial.eq_C_of_natDegree_eq_zero (hF P hP)
        conv_lhs => rw [hC, spec, Polynomial.map_C, Polynomial.eval_C]
  · intro g
    exact ⟨({g' | F.map (fun P => SignType.sign (MvPolynomial.eval g' (P.coeff 0)))
        = F.map fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))},
        [F.map fun P => SignType.sign (MvPolynomial.eval g (P.coeff 0))]),
      List.mem_map.mpr ⟨_, mem_allSignVecs (by simp), rfl⟩, rfl⟩

end Sundog.TarskiQE
