/-
# O-min lane R4-D4a: the normality layer (the classical Finiteness-Lemma route).

D4 replan receipt: the pre-registered "pile wall" DISSOLVES — the classical proof of the
Finiteness Lemma (vdD Ch. 3; REU exposition recovered 2026-07-05) kills the pile with the
least-non-normal-height tube, and every ingredient is order-only and already banked in this
ladder. Route: D4a normality layer → D4b β-machinery → D4c the tube kill (bad set finite) →
D4d count constancy + UNIFORM FINITENESS.

**This module (D4a):** the box-normality predicates, their definability (the deepest formula
of the ladder so far — the selection-continuity clause lives at ambient size 12, assembled
by `Fml.reindex` templates over a mechanical snoc battery), and the structural payoffs the
β-machinery needs:

- `normal_slice_isOpen` — within one column, normal heights are OPEN: an empty box certifies
  its whole height-window; a graph box certifies every other height by an empty box carved
  out of the selection-continuity clause (an invader would have to BE the selection).
- `tame_normalTop` / `tame_normalBot` — the ±∞ ray-normality sets are tame — and
  `tame_notNormal_slice`, `notNormal_slice_isClosed` — so the least non-normal height exists
  where needed (closed + nonempty + bounded below).

**Honest fence.** D4a only: no β functions (D4b), no tube kill (D4c), no UF (D4d).
-/
import Sundogcert.OMinimalCurves

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalAbstract.Fml

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### Coordinate equality -/

/-- Coordinate equality as a formula: `¬(i<j) ∧ ¬(j<i)`. -/
def eqAt {S : OMinStructure} {n : ℕ} (i j : Fin n) : Fml S n :=
  (Fml.not (ltAt i j)).and (Fml.not (ltAt j i))

@[simp] theorem eval_eqAt {n : ℕ} (i j : Fin n) (f : Fin n → ℝ) :
    (eqAt (S := S) i j).eval f ↔ f i = f j := by
  simp only [eqAt, Fml.eval, eval_ltAt]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
  · rintro h
    rw [h]
    exact ⟨lt_irrefl _, lt_irrefl _⟩

/-! ### The box predicates (shapes tuned to the formulas below) -/

/-- The box `(u,w) × (p,q)` misses `A` entirely. -/
def IsEmptyBox (A : Set (Fin 2 → ℝ)) (u w p q : ℝ) : Prop :=
  ∀ x y : ℝ, ((u < x ∧ x < w) ∧ (p < y ∧ y < q)) → pairFn x y ∉ A

/-- Every column of the box meets `A` in exactly one point. -/
def IsThinBox (A : Set (Fin 2 → ℝ)) (u w p q : ℝ) : Prop :=
  ∀ x : ℝ, (u < x ∧ x < w) → ∃ y : ℝ, (p < y ∧ y < q) ∧ (pairFn x y ∈ A ∧
    ∀ y' : ℝ, ((p < y' ∧ y' < q) ∧ pairFn x y' ∈ A) → y' = y)

/-- The box selection is order-continuous: at every column point and every bracket around
its selected height, some subwindow of columns selects inside the bracket. -/
def IsSelContBox (A : Set (Fin 2 → ℝ)) (u w p q : ℝ) : Prop :=
  ∀ x : ℝ, (u < x ∧ x < w) → ∀ y : ℝ, ((p < y ∧ y < q) ∧ pairFn x y ∈ A) →
    ∀ c d : ℝ, (c < y ∧ y < d) → ∃ u' w' : ℝ, ((u' < x ∧ x < w') ∧
      ∀ x' : ℝ, ((u' < x' ∧ x' < w') ∧ (u < x' ∧ x' < w)) →
        ∀ y' : ℝ, ((p < y' ∧ y' < q) ∧ pairFn x' y' ∈ A) → (c < y' ∧ y' < d))

/-- `(a,b)` is a normal point of `A`: some box around it either misses `A` or catches `A`
as a thin continuous graph through `(a,b)`. -/
def Normal (A : Set (Fin 2 → ℝ)) (a b : ℝ) : Prop :=
  ∃ u w p q : ℝ, ((u < a ∧ a < w) ∧ (p < b ∧ b < q)) ∧
    (IsEmptyBox A u w p q ∨
      (pairFn a b ∈ A ∧ (IsThinBox A u w p q ∧ IsSelContBox A u w p q)))

/-- `(a, +∞)` is normal: some window × upper ray misses `A`. -/
def NormalTop (A : Set (Fin 2 → ℝ)) (a : ℝ) : Prop :=
  ∃ u w q : ℝ, (u < a ∧ a < w) ∧
    ∀ x : ℝ, (u < x ∧ x < w) → ∀ y : ℝ, q < y → pairFn x y ∉ A

/-- `(a, −∞)` is normal: some window × lower ray misses `A`. -/
def NormalBot (A : Set (Fin 2 → ℝ)) (a : ℝ) : Prop :=
  ∃ u w p : ℝ, (u < a ∧ a < w) ∧
    ∀ x : ℝ, (u < x ∧ x < w) → ∀ y : ℝ, y < p → pairFn x y ∉ A

/-! ### The snoc battery (ambient sizes 2–12) -/

private theorem sn2_0 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem snL2 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 1 = z := by simp [Fin.snoc]

private theorem sn3_0 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn3_1 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem snL3 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 2 = z := by simp [Fin.snoc]

private theorem sn4_0 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn4_1 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn4_2 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem snL4 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 3 = z := by simp [Fin.snoc]

private theorem sn5_0 (h : Fin 4 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 5 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn5_1 (h : Fin 4 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 5 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn5_2 (h : Fin 4 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 5 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn5_3 (h : Fin 4 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 5 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem snL5 (h : Fin 4 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 5 → ℝ) 4 = z := by simp [Fin.snoc]

private theorem sn6_0 (h : Fin 5 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 6 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn6_1 (h : Fin 5 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 6 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn6_2 (h : Fin 5 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 6 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn6_3 (h : Fin 5 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 6 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn6_4 (h : Fin 5 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 6 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem snL6 (h : Fin 5 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 6 → ℝ) 5 = z := by simp [Fin.snoc]

private theorem sn7_0 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn7_1 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn7_2 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn7_3 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn7_4 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem sn7_5 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 5 = h 5 := by simp [Fin.snoc]

private theorem snL7 (h : Fin 6 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 7 → ℝ) 6 = z := by simp [Fin.snoc]

private theorem sn8_0 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn8_1 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn8_2 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn8_3 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn8_4 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem sn8_5 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 5 = h 5 := by simp [Fin.snoc]

private theorem sn8_6 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 6 = h 6 := by simp [Fin.snoc]

private theorem snL8 (h : Fin 7 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 8 → ℝ) 7 = z := by simp [Fin.snoc]

private theorem sn9_0 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn9_1 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn9_2 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn9_3 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn9_4 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem sn9_5 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 5 = h 5 := by simp [Fin.snoc]

private theorem sn9_6 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 6 = h 6 := by simp [Fin.snoc]

private theorem sn9_7 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 7 = h 7 := by simp [Fin.snoc]

private theorem snL9 (h : Fin 8 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 9 → ℝ) 8 = z := by simp [Fin.snoc]

private theorem sn10_0 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn10_1 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn10_2 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn10_3 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn10_4 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem sn10_5 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 5 = h 5 := by simp [Fin.snoc]

private theorem sn10_6 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 6 = h 6 := by simp [Fin.snoc]

private theorem sn10_7 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 7 = h 7 := by simp [Fin.snoc]

private theorem sn10_8 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 8 = h 8 := by simp [Fin.snoc]

private theorem snL10 (h : Fin 9 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 10 → ℝ) 9 = z := by simp [Fin.snoc]

private theorem sn11_0 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn11_1 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn11_2 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn11_3 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn11_4 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem sn11_5 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 5 = h 5 := by simp [Fin.snoc]

private theorem sn11_6 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 6 = h 6 := by simp [Fin.snoc]

private theorem sn11_7 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 7 = h 7 := by simp [Fin.snoc]

private theorem sn11_8 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 8 = h 8 := by simp [Fin.snoc]

private theorem sn11_9 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 9 = h 9 := by simp [Fin.snoc]

private theorem snL11 (h : Fin 10 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 11 → ℝ) 10 = z := by simp [Fin.snoc]

private theorem sn12_0 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem sn12_1 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem sn12_2 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem sn12_3 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 3 = h 3 := by simp [Fin.snoc]

private theorem sn12_4 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 4 = h 4 := by simp [Fin.snoc]

private theorem sn12_5 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 5 = h 5 := by simp [Fin.snoc]

private theorem sn12_6 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 6 = h 6 := by simp [Fin.snoc]

private theorem sn12_7 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 7 = h 7 := by simp [Fin.snoc]

private theorem sn12_8 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 8 = h 8 := by simp [Fin.snoc]

private theorem sn12_9 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 9 = h 9 := by simp [Fin.snoc]

private theorem sn12_10 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 10 = h 10 := by simp [Fin.snoc]

private theorem snL12 (h : Fin 11 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 12 → ℝ) 11 = z := by simp [Fin.snoc]

attribute [local simp] sn2_0 snL2 sn3_0 sn3_1 snL3 sn4_0 sn4_1 sn4_2 snL4 sn5_0 sn5_1 sn5_2
  sn5_3 snL5 sn6_0 sn6_1 sn6_2 sn6_3 sn6_4 snL6 sn7_0 sn7_1 sn7_2 sn7_3 sn7_4 sn7_5 snL7 sn8_0
  sn8_1 sn8_2 sn8_3 sn8_4 sn8_5 sn8_6 snL8 sn9_0 sn9_1 sn9_2 sn9_3 sn9_4 sn9_5 sn9_6 sn9_7 snL9
  sn10_0 sn10_1 sn10_2 sn10_3 sn10_4 sn10_5 sn10_6 sn10_7 sn10_8 snL10 sn11_0 sn11_1 sn11_2
  sn11_3 sn11_4 sn11_5 sn11_6 sn11_7 sn11_8 sn11_9 snL11 sn12_0 sn12_1 sn12_2 sn12_3 sn12_4
  sn12_5 sn12_6 sn12_7 sn12_8 sn12_9 sn12_10 snL12

/-! ### Composition collapses -/

private theorem compPair {n : ℕ} (h : Fin n → ℝ) (i j : Fin n) :
    h ∘ ![i, j] = pairFn (h i) (h j) := by
  funext k
  fin_cases k <;> simp [pairFn, Function.comp]

private def quadFn (a b c d : ℝ) : Fin 4 → ℝ := ![a, b, c, d]

@[simp] private theorem quadFn_zero (a b c d : ℝ) : quadFn a b c d 0 = a := rfl
@[simp] private theorem quadFn_one (a b c d : ℝ) : quadFn a b c d 1 = b := rfl
@[simp] private theorem quadFn_two (a b c d : ℝ) : quadFn a b c d 2 = c := rfl
@[simp] private theorem quadFn_three (a b c d : ℝ) : quadFn a b c d 3 = d := rfl

private theorem compQuad {n : ℕ} (h : Fin n → ℝ) (i j k l : Fin n) :
    h ∘ ![i, j, k, l] = quadFn (h i) (h j) (h k) (h l) := by
  funext m
  fin_cases m <;> simp [quadFn, Function.comp]

/-! ### The box formulas (free slots `u w p q = 0 1 2 3`) -/

private def emptyBoxFml (hA : S.Definable A) : Fml S 4 :=
  .all (.all ((((ltAt 0 4).and (ltAt 4 1)).and ((ltAt 2 5).and (ltAt 5 3))).imp
    (.not (Fml.atom ![4, 5] hA))))

private theorem eval_emptyBoxFml (hA : S.Definable A) (g : Fin 4 → ℝ) :
    (emptyBoxFml hA).eval g ↔ IsEmptyBox A (g 0) (g 1) (g 2) (g 3) := by
  simp [emptyBoxFml, IsEmptyBox, Fml.eval, compPair]

private def thinFml (hA : S.Definable A) : Fml S 4 :=
  .all (((ltAt 0 4).and (ltAt 4 1)).imp (.ex (((ltAt 2 5).and (ltAt 5 3)).and
    ((Fml.atom ![4, 5] hA).and
      (.all ((((ltAt 2 6).and (ltAt 6 3)).and (Fml.atom ![4, 6] hA)).imp (eqAt 6 5)))))))

private theorem eval_thinFml (hA : S.Definable A) (g : Fin 4 → ℝ) :
    (thinFml hA).eval g ↔ IsThinBox A (g 0) (g 1) (g 2) (g 3) := by
  simp [thinFml, IsThinBox, Fml.eval, compPair]

private def selContFml (hA : S.Definable A) : Fml S 4 :=
  .all (((ltAt 0 4).and (ltAt 4 1)).imp
    (.all ((((ltAt 2 5).and (ltAt 5 3)).and (Fml.atom ![4, 5] hA)).imp
      (.all (.all (((ltAt 6 5).and (ltAt 5 7)).imp
        (.ex (.ex (((ltAt 8 4).and (ltAt 4 9)).and
          (.all ((((ltAt 8 10).and (ltAt 10 9)).and ((ltAt 0 10).and (ltAt 10 1))).imp
            (.all ((((ltAt 2 11).and (ltAt 11 3)).and (Fml.atom ![10, 11] hA)).imp
              ((ltAt 6 11).and (ltAt 11 7)))))))))))))))

private theorem eval_selContFml (hA : S.Definable A) (g : Fin 4 → ℝ) :
    (selContFml hA).eval g ↔ IsSelContBox A (g 0) (g 1) (g 2) (g 3) := by
  simp [selContFml, IsSelContBox, Fml.eval, compPair]

/-! ### The normality formulas and definability -/

private def normalFml (hA : S.Definable A) : Fml S 2 :=
  .ex (.ex (.ex (.ex (
    ((((ltAt 2 0).and (ltAt 0 3)).and ((ltAt 4 1).and (ltAt 1 5))).and
      ((Fml.reindex ![2, 3, 4, 5] (emptyBoxFml hA)).or
        ((Fml.atom ![0, 1] hA).and
          ((Fml.reindex ![2, 3, 4, 5] (thinFml hA)).and
            (Fml.reindex ![2, 3, 4, 5] (selContFml hA))))))))))

private theorem eval_normalFml (hA : S.Definable A) (f : Fin 2 → ℝ) :
    (normalFml hA).eval f ↔ Normal A (f 0) (f 1) := by
  simp [normalFml, Normal, Fml.eval, Fml.eval_reindex, compQuad, compPair,
    eval_emptyBoxFml, eval_thinFml, eval_selContFml]

/-- **The normal-point set is definable.** -/
theorem definable_normal (hA : S.Definable A) :
    S.Definable {h : Fin 2 → ℝ | Normal A (h 0) (h 1)} := by
  have h := Fml.definable (normalFml hA)
  have e : {f : Fin 2 → ℝ | (normalFml hA).eval f}
      = {h : Fin 2 → ℝ | Normal A (h 0) (h 1)} := by
    ext f
    exact eval_normalFml hA f
  rwa [e] at h

theorem definable_notNormal (hA : S.Definable A) :
    S.Definable {h : Fin 2 → ℝ | ¬ Normal A (h 0) (h 1)} := by
  have h := Fml.definable (Fml.not (normalFml hA))
  have e : {f : Fin 2 → ℝ | (Fml.not (normalFml hA)).eval f}
      = {h : Fin 2 → ℝ | ¬ Normal A (h 0) (h 1)} := by
    ext f
    simp only [Set.mem_setOf_eq, Fml.eval, eval_normalFml]
  rwa [e] at h

/-- Not-normal heights of one column form a tame set. -/
theorem tame_notNormal_slice (hA : S.Definable A) (a : ℝ) :
    Tame {b : ℝ | ¬ Normal A a b} := by
  have h := tame_slice (definable_notNormal hA) a
  have e : {y : ℝ | pairFn a y ∈ {h : Fin 2 → ℝ | ¬ Normal A (h 0) (h 1)}}
      = {b : ℝ | ¬ Normal A a b} := by
    ext b
    simp
  rwa [e] at h

private def topRayFml (hA : S.Definable A) : Fml S 1 :=
  .ex (.ex (.ex (((ltAt 1 0).and (ltAt 0 2)).and
    (.all (((ltAt 1 4).and (ltAt 4 2)).imp
      (.all ((ltAt 3 5).imp (.not (Fml.atom ![4, 5] hA)))))))))

private def botRayFml (hA : S.Definable A) : Fml S 1 :=
  .ex (.ex (.ex (((ltAt 1 0).and (ltAt 0 2)).and
    (.all (((ltAt 1 4).and (ltAt 4 2)).imp
      (.all ((ltAt 5 3).imp (.not (Fml.atom ![4, 5] hA)))))))))

private theorem eval_topRayFml (hA : S.Definable A) (g : Fin 1 → ℝ) :
    (topRayFml hA).eval g ↔ NormalTop A (g 0) := by
  simp [topRayFml, NormalTop, Fml.eval, compPair]

private theorem eval_botRayFml (hA : S.Definable A) (g : Fin 1 → ℝ) :
    (botRayFml hA).eval g ↔ NormalBot A (g 0) := by
  simp [botRayFml, NormalBot, Fml.eval, compPair]

/-- **The `(·, +∞)`-normal set is tame.** -/
theorem tame_normalTop (hA : S.Definable A) : Tame {a : ℝ | NormalTop A a} := by
  have h := Fml.tame_one (S := S) (topRayFml hA)
  have e : {a : ℝ | NormalTop A a}
      = {x : ℝ | (topRayFml hA).eval (fun _ => x)} := by
    ext a
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, eval_topRayFml]
  rw [e]
  exact h

/-- **The `(·, −∞)`-normal set is tame.** -/
theorem tame_normalBot (hA : S.Definable A) : Tame {a : ℝ | NormalBot A a} := by
  have h := Fml.tame_one (S := S) (botRayFml hA)
  have e : {a : ℝ | NormalBot A a}
      = {x : ℝ | (botRayFml hA).eval (fun _ => x)} := by
    ext a
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, eval_botRayFml]
  rw [e]
  exact h

/-! ### Column openness: within one column, normal heights are open -/

/-- **Normal heights are open in the column.** An empty box certifies its whole
height-window; a graph box certifies every other height via an empty box carved out of the
selection-continuity clause. -/
theorem normal_slice_isOpen (a : ℝ) : IsOpen {b : ℝ | Normal A a b} := by
  rw [isOpen_iff_mem_nhds]
  rintro b ⟨u, w, p, q, ⟨⟨hua, haw⟩, hpb, hbq⟩, hbox⟩
  refine Filter.mem_of_superset (Ioo_mem_nhds hpb hbq) ?_
  intro b'' hb''
  rcases hbox with hemp | ⟨hmem, hthin, hcont⟩
  · exact ⟨u, w, p, q, ⟨⟨hua, haw⟩, hb''.1, hb''.2⟩, Or.inl hemp⟩
  · rcases lt_trichotomy b'' b with hlt | rfl | hgt
    · obtain ⟨m, hm1, hm2⟩ := exists_between hlt
      obtain ⟨u', w', ⟨hu'a, haw'⟩, hwin⟩ :=
        hcont a ⟨hua, haw⟩ b ⟨⟨hpb, hbq⟩, hmem⟩ m q ⟨hm2, hbq⟩
      refine ⟨max u u', min w w', p, m,
        ⟨⟨max_lt hua hu'a, lt_min haw haw'⟩, hb''.1, hm1⟩, Or.inl ?_⟩
      rintro x' y' ⟨⟨hx1, hx2⟩, hy1, hy2⟩ hyA
      have hx'uw : u < x' ∧ x' < w :=
        ⟨lt_of_le_of_lt (le_max_left _ _) hx1, lt_of_lt_of_le hx2 (min_le_left _ _)⟩
      have hx'u'w' : u' < x' ∧ x' < w' :=
        ⟨lt_of_le_of_lt (le_max_right _ _) hx1, lt_of_lt_of_le hx2 (min_le_right _ _)⟩
      have hy'q : y' < q := lt_trans hy2 (lt_trans hm2 hbq)
      have hthis := hwin x' ⟨hx'u'w', hx'uw⟩ y' ⟨⟨hy1, hy'q⟩, hyA⟩
      exact absurd hthis.1 (not_lt.mpr hy2.le)
    · exact ⟨u, w, p, q, ⟨⟨hua, haw⟩, hpb, hbq⟩, Or.inr ⟨hmem, hthin, hcont⟩⟩
    · obtain ⟨m', hm1', hm2'⟩ := exists_between hgt
      obtain ⟨u', w', ⟨hu'a, haw'⟩, hwin⟩ :=
        hcont a ⟨hua, haw⟩ b ⟨⟨hpb, hbq⟩, hmem⟩ p m' ⟨hpb, hm1'⟩
      refine ⟨max u u', min w w', m', q,
        ⟨⟨max_lt hua hu'a, lt_min haw haw'⟩, hm2', hb''.2⟩, Or.inl ?_⟩
      rintro x' y' ⟨⟨hx1, hx2⟩, hy1, hy2⟩ hyA
      have hx'uw : u < x' ∧ x' < w :=
        ⟨lt_of_le_of_lt (le_max_left _ _) hx1, lt_of_lt_of_le hx2 (min_le_left _ _)⟩
      have hx'u'w' : u' < x' ∧ x' < w' :=
        ⟨lt_of_le_of_lt (le_max_right _ _) hx1, lt_of_lt_of_le hx2 (min_le_right _ _)⟩
      have hpy' : p < y' := lt_trans (lt_trans hpb hm1') hy1
      have hthis := hwin x' ⟨hx'u'w', hx'uw⟩ y' ⟨⟨hpy', hy2⟩, hyA⟩
      exact absurd hthis.2 (not_lt.mpr hy1.le)

/-- Not-normal heights of one column form a closed set. -/
theorem notNormal_slice_isClosed (a : ℝ) : IsClosed {b : ℝ | ¬ Normal A a b} := by
  have e : {b : ℝ | ¬ Normal A a b} = {b : ℝ | Normal A a b}ᶜ := rfl
  rw [e]
  exact (normal_slice_isOpen a).isClosed_compl

end Sundog.OMinimalAbstract
