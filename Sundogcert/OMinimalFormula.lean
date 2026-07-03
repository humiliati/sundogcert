/-
# O-min lane R4-C0: the formula layer — definability by reflection.

The scouted cost-center of the Monotonicity Theorem is definability *plumbing*: each set like
`{x | ∃ v > x, ∀ y ∈ (x,v), φ y > φ x}` costs 50–100 lines of raw substitution/projection
bookkeeping. This module fixes that once: a reflected first-order syntax `Fml S n` — atoms are
definable sets pulled back along coordinate maps, connectives are `¬`/`∧`/`∃`-last (with
`∨`/`→`/`∀` derived) — and **one induction** (`Fml.definable`) showing every formula's solution
set is definable. After this, every van den Dries "this set is clearly definable" is a term.

Convenience layer: coordinate comparison (`ltAt`), coordinate-equals-constant (`eqConstAt`),
membership in a dimension-one definable (`memAt`), the graph atom (`graphAt`: `φ(x_i) = x_j`),
and the derived two-coordinate value comparison (`ltGraph`: `φ(x_i) < φ(x_j)`, two `∃`s over
graph atoms). `Fml.tame_one` lands dimension-one formulas in `Tame` directly.

Receipt (the payoff, and C1's first working set): `tame_right_inc` — for any definable `φ`, the
set of points where `φ` is eventually increasing to the right,
`{x | ∃ v, x < v ∧ ∀ y, x < y → y < v → φ x < φ y}`, is tame — a six-line formula term.
The pre-registered falsifier `FORMULA_LAYER_LEAKS` (index/universe bookkeeping makes the
inductive unusable) did **not** fire.

**Honest fence.** A plumbing layer, not a theorem: the mathematical content of R4-C
(trichotomies, gluing, the mixed-sign kills) is C1a–C1d on top of this.
-/
import Sundogcert.OMinimalStructure

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

/-! ### The syntax and its semantics -/

/-- First-order formulas over an o-minimal structure: atoms are definable sets pulled back
along coordinate maps; `¬`/`∧`/`∃`-last generate the rest. `Fml S n` has `n` free variables. -/
inductive Fml (S : OMinStructure) : ℕ → Type where
  | atom {m n : ℕ} (σ : Fin m → Fin n) {A : Set (Fin m → ℝ)} (h : S.Definable A) : Fml S n
  | not {n : ℕ} : Fml S n → Fml S n
  | and {n : ℕ} : Fml S n → Fml S n → Fml S n
  | ex {n : ℕ} : Fml S (n + 1) → Fml S n

namespace Fml

variable {S : OMinStructure} {n : ℕ}

@[simp] def eval : ∀ {n : ℕ}, Fml S n → (Fin n → ℝ) → Prop
  | _, .atom σ (A := A) _, f => f ∘ σ ∈ A
  | _, .not φ, f => ¬ φ.eval f
  | _, .and φ ψ, f => φ.eval f ∧ ψ.eval f
  | _, .ex φ, f => ∃ y : ℝ, φ.eval (Fin.snoc f y)

/-- **The layer's one theorem**: every formula's solution set is definable — each constructor
is one structure axiom. -/
theorem definable (φ : Fml S n) : S.Definable {f | φ.eval f} := by
  induction φ with
  | atom σ h =>
    have h' := S.definable_subst σ h
    simpa only [eval] using h'
  | not φ ih =>
    have h' := S.definable_compl ih
    rw [Set.compl_setOf] at h'
    simpa only [eval] using h'
  | and φ ψ ih₁ ih₂ =>
    have h' := S.definable_inter ih₁ ih₂
    rw [← Set.setOf_and] at h'
    simpa only [eval] using h'
  | ex φ ih =>
    have h' := S.definable_proj ih
    simpa only [eval, Set.mem_setOf_eq] using h'

/-- Dimension-one formulas land in `Tame` directly. -/
theorem tame_one (ψ : Fml S 1) : Tame {x : ℝ | ψ.eval (fun _ => x)} :=
  S.tame_dim_one ψ.definable

/-! ### Derived connectives -/

def or (φ ψ : Fml S n) : Fml S n := .not (.and (.not φ) (.not ψ))

@[simp] theorem eval_or (φ ψ : Fml S n) (f : Fin n → ℝ) :
    (φ.or ψ).eval f ↔ φ.eval f ∨ ψ.eval f := by
  simp only [or, eval, not_and, not_not]
  tauto

def imp (φ ψ : Fml S n) : Fml S n := .not (.and φ (.not ψ))

@[simp] theorem eval_imp (φ ψ : Fml S n) (f : Fin n → ℝ) :
    (φ.imp ψ).eval f ↔ (φ.eval f → ψ.eval f) := by
  simp only [imp, eval, not_and, not_not]

def all (φ : Fml S (n + 1)) : Fml S n := .not (.ex (.not φ))

@[simp] theorem eval_all (φ : Fml S (n + 1)) (f : Fin n → ℝ) :
    φ.all.eval f ↔ ∀ y : ℝ, φ.eval (Fin.snoc f y) := by
  simp only [all, eval, not_exists, not_not]

/-! ### Convenience atoms -/

/-- Coordinate comparison: `x_i < x_j`. -/
def ltAt (i j : Fin n) : Fml S n := .atom ![i, j] S.definable_lt

@[simp] theorem eval_ltAt (i j : Fin n) (f : Fin n → ℝ) :
    (ltAt (S := S) i j).eval f ↔ f i < f j := by
  simp [ltAt, Function.comp]

/-- Coordinate equals a constant: `x_i = r`. -/
def eqConstAt (i : Fin n) (r : ℝ) : Fml S n := .atom ![i] (S.definable_singleton r)

@[simp] theorem eval_eqConstAt (i : Fin n) (r : ℝ) (f : Fin n → ℝ) :
    (eqConstAt (S := S) i r).eval f ↔ f i = r := by
  simp [eqConstAt, Function.comp]

/-- Membership of a coordinate in a dimension-one definable set: `x_i ∈ T`. -/
def memAt (i : Fin n) {T : Set ℝ} (h : S.Definable (toOne T)) : Fml S n := .atom ![i] h

@[simp] theorem eval_memAt (i : Fin n) {T : Set ℝ} (h : S.Definable (toOne T))
    (f : Fin n → ℝ) : (memAt i h).eval f ↔ f i ∈ T := by
  simp [memAt, toOne, Function.comp]

/-- The graph atom: `φ(x_i) = x_j`. -/
def graphAt {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n) : Fml S n :=
  .atom ![i, j] hφ

@[simp] theorem eval_graphAt {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n)
    (f : Fin n → ℝ) : (graphAt hφ i j).eval f ↔ φ (f i) = f j := by
  simp [graphAt, Function.comp]

/-- Two-coordinate value comparison: `φ(x_i) < φ(x_j)`, via two `∃`s over graph atoms. -/
def ltGraph {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n) : Fml S n :=
  .ex (.ex (.and (.and
    (graphAt hφ (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.last n)))
    (graphAt hφ (Fin.castSucc (Fin.castSucc j)) (Fin.last (n + 1))))
    (ltAt (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)))))

@[simp] theorem eval_ltGraph {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n)
    (f : Fin n → ℝ) : (ltGraph hφ i j).eval f ↔ φ (f i) < φ (f j) := by
  simp only [ltGraph, eval, eval_graphAt, eval_ltAt, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨p, q, ⟨h1, h2⟩, h3⟩
    rw [← h1, ← h2] at h3
    exact h3
  · intro h
    exact ⟨φ (f i), φ (f j), ⟨rfl, rfl⟩, h⟩

/-! ### The receipt: C1's first working set, in six lines of formula -/

/-- **The payoff demo (and C1's first D-set): the eventually-right-increasing set of a definable
function is tame.** `{x | ∃ v, x < v ∧ ∀ y, x < y → y < v → φ x < φ y}` — as a formula:
coordinates `x = 0`, `∃ v = 1`, `∀ y = 2`. In the raw calculus this is ~100 lines; here it is
the formula term below. -/
private theorem snocA (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocB (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 1 = y := by
  simp [Fin.snoc]

private theorem snocC (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocD (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocE (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 2 = y := by
  simp [Fin.snoc]

theorem tame_right_inc {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) :
    Tame {x : ℝ | ∃ v : ℝ, x < v ∧ ∀ y : ℝ, x < y → y < v → φ x < φ y} := by
  have h := Fml.tame_one (S := S)
    (Fml.ex (.and (ltAt 0 1)
      (Fml.all ((Fml.and (ltAt 0 2) (ltAt 2 1)).imp (ltGraph hφ 0 2)))))
  have e : {x : ℝ | ∃ v : ℝ, x < v ∧ ∀ y : ℝ, x < y → y < v → φ x < φ y}
      = {x : ℝ | Fml.eval (S := S) (n := 1)
          (Fml.ex (.and (ltAt 0 1)
            (Fml.all ((Fml.and (ltAt 0 2) (ltAt 2 1)).imp (ltGraph hφ 0 2)))))
          (fun _ => x)} := by
    ext x
    simp only [Set.mem_setOf_eq, eval, eval_ltAt, eval_all, eval_imp, eval_ltGraph,
      snocA, snocB, snocC, snocD, snocE, and_imp]
  rw [e]
  exact h

end Fml

end Sundog.OMinimalAbstract
