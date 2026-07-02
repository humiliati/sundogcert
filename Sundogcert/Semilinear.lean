/-
# O-min ladder R3-semilinear (part 1): the semilinear presentation class, dims 1–2.

Syntax and semantics for semilinear sets — the standard presentation: finite unions of cells,
a cell being a finite conjunction of strict linear inequalities (`gt`: `a·x + b·y + c > 0`) and
linear equalities (`eq`: `… = 0`). With `{>, =}` atoms the class is closed under all boolean
operations (complement of `>` is `< ∪ =`; complement of `=` is `> ∪ <`; de Morgan folds the rest)
— proved here **constructively**: `slInter₂`, `slCompl₂`, with correctness lemmas.

The 1-D fragment lands in rung 1's tameness: every 1-D semilinear set is `Tame`
(`slHolds₁_tame`) — a `gt` atom is an open convex set (open + `OrdConnected`), an `eq` atom is a
point / `∅` / `univ`, and the boolean structure closes by rung 1's algebra.

Part 2 (`FourierMotzkin`) adds the projection `SL₂ → SL₁` — together they make the semilinear
class a genuine structure in dimensions 1–2: booleans + projection + dimension-one tameness.

**Honest fence.** Dimensions 1–2 only (the n-dimensional version is the same argument with more
index bookkeeping — named, not claimed). The bridge "2-input ReLU-net superlevel sets are
semilinear" needs a 2-D piece decomposition the lane has not built — named follow-on, not claimed.
-/
import Sundogcert.OMinimalNormalForm

namespace Sundog.Semilinear

open Sundog.OMinimalOne Sundog.OMinimalNormalForm

/-! ### Syntax and semantics -/

/-- A linear atom in two variables: `gt a b c` means `a·x + b·y + c > 0`; `eq` means `… = 0`. -/
inductive Atom₂ where
  | gt (a b c : ℝ)
  | eq (a b c : ℝ)

@[simp] def Atom₂.holds : Atom₂ → ℝ → ℝ → Prop
  | .gt a b c, x, y => 0 < a * x + b * y + c
  | .eq a b c, x, y => a * x + b * y + c = 0

/-- A cell: a finite conjunction of atoms. -/
abbrev Cell₂ := List Atom₂

/-- A semilinear presentation: a finite union of cells. -/
abbrev SL₂ := List Cell₂

def cellHolds₂ (C : Cell₂) (x y : ℝ) : Prop := ∀ A ∈ C, A.holds x y

def slHolds₂ (S : SL₂) (x y : ℝ) : Prop := ∃ C ∈ S, cellHolds₂ C x y

/-- A linear atom in one variable: `gt p q` means `p·x + q > 0`; `eq` means `… = 0`. -/
inductive Atom₁ where
  | gt (p q : ℝ)
  | eq (p q : ℝ)

@[simp] def Atom₁.holds : Atom₁ → ℝ → Prop
  | .gt p q, x => 0 < p * x + q
  | .eq p q, x => p * x + q = 0

abbrev Cell₁ := List Atom₁
abbrev SL₁ := List Cell₁

def cellHolds₁ (C : Cell₁) (x : ℝ) : Prop := ∀ A ∈ C, A.holds x

def slHolds₁ (S : SL₁) (x : ℝ) : Prop := ∃ C ∈ S, cellHolds₁ C x

/-- Singleton-cell evaluation: `cellHolds₂ [A]` is just the atom. -/
theorem cellHolds₂_singleton (A : Atom₂) (x y : ℝ) :
    cellHolds₂ [A] x y ↔ A.holds x y := by
  unfold cellHolds₂
  constructor
  · intro h
    exact h A List.mem_cons_self
  · intro h B hB
    rw [List.mem_singleton] at hB
    subst hB
    exact h

/-- Cons-cell evaluation for 1-D unions. -/
theorem slHolds₁_cons (C : Cell₁) (S : SL₁) (x : ℝ) :
    slHolds₁ (C :: S) x ↔ cellHolds₁ C x ∨ slHolds₁ S x := by
  unfold slHolds₁
  constructor
  · rintro ⟨D, hD, h⟩
    rcases List.mem_cons.mp hD with rfl | hD
    exacts [Or.inl h, Or.inr ⟨D, hD, h⟩]
  · rintro (h | ⟨D, hD, h⟩)
    exacts [⟨C, List.mem_cons_self, h⟩, ⟨D, List.mem_cons_of_mem _ hD, h⟩]

/-- Cons-cell evaluation for 2-D unions. -/
theorem slHolds₂_cons (C : Cell₂) (S : SL₂) (x y : ℝ) :
    slHolds₂ (C :: S) x y ↔ cellHolds₂ C x y ∨ slHolds₂ S x y := by
  unfold slHolds₂
  constructor
  · rintro ⟨D, hD, h⟩
    rcases List.mem_cons.mp hD with rfl | hD
    exacts [Or.inl h, Or.inr ⟨D, hD, h⟩]
  · rintro (h | ⟨D, hD, h⟩)
    exacts [⟨C, List.mem_cons_self, h⟩, ⟨D, List.mem_cons_of_mem _ hD, h⟩]

/-! ### Boolean closure in dimension 2 (constructive) -/

/-- Union: concatenate the cell lists. -/
def slUnion₂ (S T : SL₂) : SL₂ := S ++ T

theorem slUnion₂_holds (S T : SL₂) (x y : ℝ) :
    slHolds₂ (slUnion₂ S T) x y ↔ slHolds₂ S x y ∨ slHolds₂ T x y := by
  unfold slUnion₂ slHolds₂
  constructor
  · rintro ⟨C, hC, h⟩
    rcases List.mem_append.mp hC with h' | h'
    exacts [Or.inl ⟨C, h', h⟩, Or.inr ⟨C, h', h⟩]
  · rintro (⟨C, hC, h⟩ | ⟨C, hC, h⟩)
    exacts [⟨C, List.mem_append_left _ hC, h⟩, ⟨C, List.mem_append_right _ hC, h⟩]

theorem cellHolds₂_append (C D : Cell₂) (x y : ℝ) :
    cellHolds₂ (C ++ D) x y ↔ cellHolds₂ C x y ∧ cellHolds₂ D x y := by
  unfold cellHolds₂
  constructor
  · intro h
    exact ⟨fun A hA => h A (List.mem_append_left _ hA),
      fun A hA => h A (List.mem_append_right _ hA)⟩
  · rintro ⟨h1, h2⟩ A hA
    rcases List.mem_append.mp hA with h | h
    exacts [h1 A h, h2 A h]

/-- Intersection: pairwise concatenation of cells (distributivity). -/
def slInter₂ (S T : SL₂) : SL₂ := S.flatMap fun C => T.map fun D => C ++ D

theorem slInter₂_holds (S T : SL₂) (x y : ℝ) :
    slHolds₂ (slInter₂ S T) x y ↔ slHolds₂ S x y ∧ slHolds₂ T x y := by
  unfold slInter₂ slHolds₂
  constructor
  · rintro ⟨E, hE, h⟩
    obtain ⟨C, hC, hE'⟩ := List.mem_flatMap.mp hE
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hE'
    obtain ⟨h1, h2⟩ := (cellHolds₂_append C D x y).mp h
    exact ⟨⟨C, hC, h1⟩, ⟨D, hD, h2⟩⟩
  · rintro ⟨⟨C, hC, h1⟩, ⟨D, hD, h2⟩⟩
    exact ⟨C ++ D, List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨D, hD, rfl⟩⟩,
      (cellHolds₂_append C D x y).mpr ⟨h1, h2⟩⟩

/-- Atom complement: `¬(t > 0)` is `(−t > 0) ∨ (t = 0)`; `¬(t = 0)` is `(t > 0) ∨ (−t > 0)`. -/
def atomCompl₂ : Atom₂ → SL₂
  | .gt a b c => [[.gt (-a) (-b) (-c)], [.eq a b c]]
  | .eq a b c => [[.gt a b c], [.gt (-a) (-b) (-c)]]

theorem atomCompl₂_holds (A : Atom₂) (x y : ℝ) :
    slHolds₂ (atomCompl₂ A) x y ↔ ¬ A.holds x y := by
  cases A with
  | gt a b c =>
    rw [show atomCompl₂ (.gt a b c) = [[.gt (-a) (-b) (-c)], [.eq a b c]] from rfl,
      slHolds₂_cons, slHolds₂_cons, cellHolds₂_singleton, cellHolds₂_singleton]
    simp only [Atom₂.holds, slHolds₂, List.not_mem_nil, false_and, exists_false, or_false,
      not_lt]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  | eq a b c =>
    rw [show atomCompl₂ (.eq a b c) = [[.gt a b c], [.gt (-a) (-b) (-c)]] from rfl,
      slHolds₂_cons, slHolds₂_cons, cellHolds₂_singleton, cellHolds₂_singleton]
    simp only [Atom₂.holds, slHolds₂, List.not_mem_nil, false_and, exists_false, or_false]
    constructor
    · rintro (h | h) <;> intro hcon <;> linarith
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)

/-- Cell complement: de Morgan — the complement of a conjunction is the union of the atom
complements. -/
def cellCompl₂ (C : Cell₂) : SL₂ := C.flatMap atomCompl₂

theorem cellCompl₂_holds (C : Cell₂) (x y : ℝ) :
    slHolds₂ (cellCompl₂ C) x y ↔ ¬ cellHolds₂ C x y := by
  unfold cellCompl₂ cellHolds₂
  constructor
  · rintro ⟨D, hD, h⟩ hall
    obtain ⟨A, hA, hD'⟩ := List.mem_flatMap.mp hD
    have := (atomCompl₂_holds A x y).mp ⟨D, hD', h⟩
    exact this (hall A hA)
  · intro h
    rcases not_forall.mp h with ⟨A, hA⟩
    rcases Classical.not_imp.mp hA with ⟨hAC, hnA⟩
    obtain ⟨D, hD, hh⟩ := (atomCompl₂_holds A x y).mpr hnA
    exact ⟨D, List.mem_flatMap.mpr ⟨A, hAC, hD⟩, hh⟩

/-- The universal presentation: one empty cell. -/
def slUniv₂ : SL₂ := [[]]

theorem slUniv₂_holds (x y : ℝ) : slHolds₂ slUniv₂ x y :=
  ⟨[], List.mem_cons_self, fun _ h => absurd h List.not_mem_nil⟩

/-- Complement: fold de Morgan over the union of cells. -/
def slCompl₂ (S : SL₂) : SL₂ := S.foldr (fun C acc => slInter₂ (cellCompl₂ C) acc) slUniv₂

theorem slCompl₂_holds (S : SL₂) (x y : ℝ) :
    slHolds₂ (slCompl₂ S) x y ↔ ¬ slHolds₂ S x y := by
  induction S with
  | nil =>
    simp only [slCompl₂, List.foldr_nil, slHolds₂, List.not_mem_nil, false_and, exists_false,
      not_false_iff, iff_true]
    exact slUniv₂_holds x y
  | cons C S ih =>
    have hstep : slHolds₂ (slCompl₂ (C :: S)) x y ↔
        slHolds₂ (cellCompl₂ C) x y ∧ slHolds₂ (slCompl₂ S) x y := by
      unfold slCompl₂
      rw [List.foldr_cons]
      exact slInter₂_holds _ _ x y
    rw [hstep, cellCompl₂_holds, ih, slHolds₂_cons]
    tauto

/-! ### The 1-D fragment is tame (the rung-1 bridge) -/

/-- A strict linear atom cuts out an open convex set — tame by rung 2's interval lemma. -/
theorem atom₁_gt_tame (p q : ℝ) : Tame {x | 0 < p * x + q} := by
  apply tame_of_isOpen_ordConnected
  · exact isOpen_lt continuous_const ((continuous_const.mul continuous_id).add continuous_const)
  · constructor
    intro u hu v hv z hz
    simp only [Set.mem_setOf_eq] at *
    rcases le_or_gt 0 p with hp | hp
    · have := mul_le_mul_of_nonneg_left hz.1 hp
      linarith
    · have := mul_le_mul_of_nonpos_left hz.2 hp.le
      linarith

/-- A linear equality cuts out a point, `∅`, or `univ` — tame in every case. -/
theorem atom₁_eq_tame (p q : ℝ) : Tame {x | p * x + q = 0} := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · have h : {x : ℝ | p * x + q = 0} = Set.univ := by
        ext x; simp [hp, hq]
      rw [h]; exact tame_univ
    · have h : {x : ℝ | p * x + q = 0} = ∅ := by
        ext x; simp [hp, hq]
      rw [h]; exact tame_empty
  · have h : {x : ℝ | p * x + q = 0} = {-q / p} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      rw [eq_div_iff hp]
      constructor
      · intro h'
        linear_combination h'
      · intro h'
        linear_combination h'
    rw [h]
    exact (Set.finite_singleton _).subset isClosed_singleton.frontier_subset

theorem atom₁_tame (A : Atom₁) : Tame {x | A.holds x} := by
  cases A with
  | gt p q => exact atom₁_gt_tame p q
  | eq p q => exact atom₁_eq_tame p q

theorem cellHolds₁_tame (C : Cell₁) : Tame {x | cellHolds₁ C x} := by
  induction C with
  | nil =>
    have h : {x : ℝ | cellHolds₁ [] x} = Set.univ := by
      ext x; simp [cellHolds₁]
    rw [h]; exact tame_univ
  | cons A C ih =>
    have h : {x : ℝ | cellHolds₁ (A :: C) x} = {x | A.holds x} ∩ {x | cellHolds₁ C x} := by
      ext x
      simp only [cellHolds₁, List.forall_mem_cons, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [h]
    exact tame_inter (atom₁_tame A) ih

/-- **Every 1-D semilinear set is tame** — the rung-1 landing pad for the projection. -/
theorem slHolds₁_tame (S : SL₁) : Tame {x | slHolds₁ S x} := by
  induction S with
  | nil =>
    have h : {x : ℝ | slHolds₁ [] x} = ∅ := by
      ext x; simp [slHolds₁]
    rw [h]; exact tame_empty
  | cons C S ih =>
    have h : {x : ℝ | slHolds₁ (C :: S) x} = {x | cellHolds₁ C x} ∪ {x | slHolds₁ S x} := by
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, slHolds₁_cons]
    rw [h]
    exact tame_union (cellHolds₁_tame C) ih

end Sundog.Semilinear
