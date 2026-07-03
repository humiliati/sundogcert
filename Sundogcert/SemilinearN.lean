/-
# O-min lane R4-B1: the n-dimensional semilinear presentation class — syntax + boolean closure.

The R3 dims-2 class (`Semilinear`) generalized to `n` variables: an atom is a coefficient row
`a : Fin n → ℝ` with a constant, of kind `gt` (`(∑ i, a i · x i) + c > 0`) or `eq` (`… = 0`);
cells are finite conjunctions, presentations finite unions. This stage ports R3's constructive
boolean closure (`slUnionN` / `slInterN` / `slComplN`, with correctness) — the port is mechanical
because the R3 proofs only ever used each atom's affine **value** as one opaque real; the single
new algebraic fact is `neg_val` (negating the row and constant negates the value), proved
name-risk-free from `Finset.sum_add_distrib` + `sum_eq_zero`.

Later stages on this syntax: B2 substitution (fiberwise coefficient sums → the
`definable_subst` axiom shape), B3 the n-dimensional Fourier–Motzkin (eliminate the last
variable), B4 the atoms + `tame_dim_one` bridge + the assembled `OMinStructure` instance.

**Honest fence.** Syntax and booleans only; no projection, no tameness, no instance — those are
B2–B4. Pre-registered stage of the R4-B scope in `SUNDOG_V_OMIN.md`.
-/
import Sundogcert.Semilinear

namespace Sundog.SemilinearN

/-! ### Syntax and semantics -/

/-- A linear atom in `n` variables: coefficient row + constant; `gt` means
`(∑ i, a i · x i) + c > 0`, `eq` means `… = 0`. -/
inductive AtomN (n : ℕ) where
  | gt (a : Fin n → ℝ) (c : ℝ)
  | eq (a : Fin n → ℝ) (c : ℝ)

variable {n : ℕ}

@[simp] def AtomN.holds : AtomN n → (Fin n → ℝ) → Prop
  | .gt a c, x => 0 < (∑ i, a i * x i) + c
  | .eq a c, x => (∑ i, a i * x i) + c = 0

/-- A cell: a finite conjunction of atoms. -/
abbrev CellN (n : ℕ) := List (AtomN n)

/-- A semilinear presentation: a finite union of cells. -/
abbrev SLN (n : ℕ) := List (CellN n)

def cellHoldsN (C : CellN n) (x : Fin n → ℝ) : Prop := ∀ A ∈ C, A.holds x

def slHoldsN (S : SLN n) (x : Fin n → ℝ) : Prop := ∃ C ∈ S, cellHoldsN C x

/-- The set presented. -/
def SLN.toSet (S : SLN n) : Set (Fin n → ℝ) := {x | slHoldsN S x}

/-- Negating the row and the constant negates the atom's value — the one new algebraic fact of
the port, proved without name risk from `sum_add_distrib`. -/
private theorem neg_val (a : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    (∑ i, (fun i => -a i) i * x i) + -c = -((∑ i, a i * x i) + c) := by
  have h : (∑ i, (fun i => -a i) i * x i) + (∑ i, a i * x i) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => by ring
  linarith

/-! ### Evaluation lemmas (verbatim R3 ports) -/

theorem cellHoldsN_singleton (A : AtomN n) (x : Fin n → ℝ) :
    cellHoldsN [A] x ↔ A.holds x := by
  unfold cellHoldsN
  constructor
  · intro h
    exact h A List.mem_cons_self
  · intro h B hB
    rw [List.mem_singleton] at hB
    subst hB
    exact h

theorem slHoldsN_cons (C : CellN n) (S : SLN n) (x : Fin n → ℝ) :
    slHoldsN (C :: S) x ↔ cellHoldsN C x ∨ slHoldsN S x := by
  unfold slHoldsN
  constructor
  · rintro ⟨D, hD, h⟩
    rcases List.mem_cons.mp hD with rfl | hD
    exacts [Or.inl h, Or.inr ⟨D, hD, h⟩]
  · rintro (h | ⟨D, hD, h⟩)
    exacts [⟨C, List.mem_cons_self, h⟩, ⟨D, List.mem_cons_of_mem _ hD, h⟩]

theorem cellHoldsN_append (C D : CellN n) (x : Fin n → ℝ) :
    cellHoldsN (C ++ D) x ↔ cellHoldsN C x ∧ cellHoldsN D x := by
  unfold cellHoldsN
  constructor
  · intro h
    exact ⟨fun A hA => h A (List.mem_append_left _ hA),
      fun A hA => h A (List.mem_append_right _ hA)⟩
  · rintro ⟨h1, h2⟩ A hA
    rcases List.mem_append.mp hA with h | h
    exacts [h1 A h, h2 A h]

/-! ### Boolean closure (constructive, verbatim R3 ports mod `neg_val`) -/

/-- Union: concatenate the cell lists. -/
def slUnionN (S T : SLN n) : SLN n := S ++ T

theorem slUnionN_holds (S T : SLN n) (x : Fin n → ℝ) :
    slHoldsN (slUnionN S T) x ↔ slHoldsN S x ∨ slHoldsN T x := by
  unfold slUnionN slHoldsN
  constructor
  · rintro ⟨C, hC, h⟩
    rcases List.mem_append.mp hC with h' | h'
    exacts [Or.inl ⟨C, h', h⟩, Or.inr ⟨C, h', h⟩]
  · rintro (⟨C, hC, h⟩ | ⟨C, hC, h⟩)
    exacts [⟨C, List.mem_append_left _ hC, h⟩, ⟨C, List.mem_append_right _ hC, h⟩]

/-- Intersection: pairwise concatenation of cells (distributivity). -/
def slInterN (S T : SLN n) : SLN n := S.flatMap fun C => T.map fun D => C ++ D

theorem slInterN_holds (S T : SLN n) (x : Fin n → ℝ) :
    slHoldsN (slInterN S T) x ↔ slHoldsN S x ∧ slHoldsN T x := by
  unfold slInterN slHoldsN
  constructor
  · rintro ⟨E, hE, h⟩
    obtain ⟨C, hC, hE'⟩ := List.mem_flatMap.mp hE
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hE'
    obtain ⟨h1, h2⟩ := (cellHoldsN_append C D x).mp h
    exact ⟨⟨C, hC, h1⟩, ⟨D, hD, h2⟩⟩
  · rintro ⟨⟨C, hC, h1⟩, ⟨D, hD, h2⟩⟩
    exact ⟨C ++ D, List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨D, hD, rfl⟩⟩,
      (cellHoldsN_append C D x).mpr ⟨h1, h2⟩⟩

/-- Atom complement: `¬(v > 0)` is `(−v > 0) ∨ (v = 0)`; `¬(v = 0)` is `(v > 0) ∨ (−v > 0)` —
with `−v` realized by negating the row and the constant. -/
def atomComplN : AtomN n → SLN n
  | .gt a c => [[.gt (fun i => -a i) (-c)], [.eq a c]]
  | .eq a c => [[.gt a c], [.gt (fun i => -a i) (-c)]]

theorem atomComplN_holds (A : AtomN n) (x : Fin n → ℝ) :
    slHoldsN (atomComplN A) x ↔ ¬ A.holds x := by
  cases A with
  | gt a c =>
    rw [show atomComplN (.gt a c) = [[.gt (fun i => -a i) (-c)], [.eq a c]] from rfl,
      slHoldsN_cons, slHoldsN_cons, cellHoldsN_singleton, cellHoldsN_singleton]
    simp only [AtomN.holds, slHoldsN, List.not_mem_nil, false_and, exists_false, or_false,
      not_lt]
    rw [neg_val]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  | eq a c =>
    rw [show atomComplN (.eq a c) = [[.gt a c], [.gt (fun i => -a i) (-c)]] from rfl,
      slHoldsN_cons, slHoldsN_cons, cellHoldsN_singleton, cellHoldsN_singleton]
    simp only [AtomN.holds, slHoldsN, List.not_mem_nil, false_and, exists_false, or_false]
    rw [neg_val]
    constructor
    · rintro (h | h) <;> intro hcon <;> linarith
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)

/-- Cell complement: de Morgan — the complement of a conjunction is the union of the atom
complements. -/
def cellComplN (C : CellN n) : SLN n := C.flatMap atomComplN

theorem cellComplN_holds (C : CellN n) (x : Fin n → ℝ) :
    slHoldsN (cellComplN C) x ↔ ¬ cellHoldsN C x := by
  unfold cellComplN cellHoldsN
  constructor
  · rintro ⟨D, hD, h⟩ hall
    obtain ⟨A, hA, hD'⟩ := List.mem_flatMap.mp hD
    have := (atomComplN_holds A x).mp ⟨D, hD', h⟩
    exact this (hall A hA)
  · intro h
    rcases not_forall.mp h with ⟨A, hA⟩
    rcases Classical.not_imp.mp hA with ⟨hAC, hnA⟩
    obtain ⟨D, hD, hh⟩ := (atomComplN_holds A x).mpr hnA
    exact ⟨D, List.mem_flatMap.mpr ⟨A, hAC, hD⟩, hh⟩

/-- The universal presentation: one empty cell. -/
def slUnivN : SLN n := [[]]

theorem slUnivN_holds (x : Fin n → ℝ) : slHoldsN (slUnivN : SLN n) x :=
  ⟨[], List.mem_cons_self, fun _ h => absurd h List.not_mem_nil⟩

/-- Complement: fold de Morgan over the union of cells. -/
def slComplN (S : SLN n) : SLN n :=
  S.foldr (fun C acc => slInterN (cellComplN C) acc) slUnivN

theorem slComplN_holds (S : SLN n) (x : Fin n → ℝ) :
    slHoldsN (slComplN S) x ↔ ¬ slHoldsN S x := by
  induction S with
  | nil =>
    simp only [slComplN, List.foldr_nil, slHoldsN, List.not_mem_nil, false_and, exists_false,
      not_false_iff, iff_true]
    exact slUnivN_holds x
  | cons C S ih =>
    have hstep : slHoldsN (slComplN (C :: S)) x ↔
        slHoldsN (cellComplN C) x ∧ slHoldsN (slComplN S) x := by
      unfold slComplN
      rw [List.foldr_cons]
      exact slInterN_holds _ _ x
    rw [hstep, cellComplN_holds, ih, slHoldsN_cons]
    tauto

/-! ### B2 — substitution: reindexing along `σ : Fin m → Fin n` (fiberwise coefficient sums)

The `definable_subst` axiom shape for the coming instance: substituting variables along any
`σ` (not necessarily injective — diagonals included) transforms an atom by **summing its
coefficients over the fibers of `σ`**: the new row is `b j := ∑ i ∈ σ⁻¹(j), a i`, and the value
is preserved because `∑ j, b j · f j` regroups to `∑ i, a i · f (σ i)` (`sum_fiberwise`).
Everything here is computable — `DecidableEq (Fin n)` is genuine, no classical sign tests. -/

variable {m : ℕ}

/-- Substituted atom: each new coefficient collects a fiber of `σ`. -/
def substAtomN (σ : Fin m → Fin n) : AtomN m → AtomN n
  | .gt a c => .gt (fun j => ∑ i ∈ Finset.univ.filter (fun i => σ i = j), a i) c
  | .eq a c => .eq (fun j => ∑ i ∈ Finset.univ.filter (fun i => σ i = j), a i) c

/-- The fiberwise regrouping: the substituted row's value at `f` is the original row's value at
`f ∘ σ`. -/
private theorem reindex_sum (σ : Fin m → Fin n) (a : Fin m → ℝ) (f : Fin n → ℝ) :
    (∑ j, (∑ i ∈ Finset.univ.filter (fun i => σ i = j), a i) * f j)
      = ∑ i, a i * f (σ i) := by
  have h1 : ∀ j, (∑ i ∈ Finset.univ.filter (fun i => σ i = j), a i) * f j
      = ∑ i ∈ Finset.univ.filter (fun i => σ i = j), a i * f (σ i) := by
    intro j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (σ i)) _

theorem substAtomN_holds (σ : Fin m → Fin n) (A : AtomN m) (f : Fin n → ℝ) :
    (substAtomN σ A).holds f ↔ A.holds (f ∘ σ) := by
  cases A with
  | gt a c =>
    simp only [substAtomN, AtomN.holds, Function.comp_apply]
    rw [reindex_sum]
  | eq a c =>
    simp only [substAtomN, AtomN.holds, Function.comp_apply]
    rw [reindex_sum]

def substCellN (σ : Fin m → Fin n) (C : CellN m) : CellN n := C.map (substAtomN σ)

theorem substCellN_holds (σ : Fin m → Fin n) (C : CellN m) (f : Fin n → ℝ) :
    cellHoldsN (substCellN σ C) f ↔ cellHoldsN C (f ∘ σ) := by
  unfold substCellN cellHoldsN
  constructor
  · intro h A hA
    exact (substAtomN_holds σ A f).mp (h _ (List.mem_map_of_mem hA))
  · intro h A₁ hA₁
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hA₁
    exact (substAtomN_holds σ A f).mpr (h A hA)

def substSLN (σ : Fin m → Fin n) (S : SLN m) : SLN n := S.map (substCellN σ)

theorem substSLN_holds (σ : Fin m → Fin n) (S : SLN m) (f : Fin n → ℝ) :
    slHoldsN (substSLN σ S) f ↔ slHoldsN S (f ∘ σ) := by
  unfold substSLN slHoldsN
  constructor
  · rintro ⟨C₁, hC₁, h⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC₁
    exact ⟨C, hC, (substCellN_holds σ C f).mp h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨substCellN σ C, List.mem_map_of_mem hC, (substCellN_holds σ C f).mpr h⟩

/-- **B2 headline, in the binding `OMinStructure` axiom shape**: the substituted presentation
presents exactly `{f | f ∘ σ ∈ toSet S}` — cylinders, permutations, and diagonals in one
constructive transform. -/
theorem substSLN_toSet (σ : Fin m → Fin n) (S : SLN m) :
    (substSLN σ S).toSet = {f : Fin n → ℝ | f ∘ σ ∈ S.toSet} := by
  ext f
  exact substSLN_holds σ S f

end Sundog.SemilinearN
