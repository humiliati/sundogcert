/-
# O-min lane R4-D0: parametric slices, and the fiber-frontier set.

The slicing layer for cell decomposition:

- **`tame_slice`** — the fiber of a two-variable definable at any real parameter is tame
  (the formula `∃z, z = x ∧ (z,y) ∈ A`, discharging C0's slicing IOU);
- **`mem_closure_iff_order`** — closure in pure order terms (`mem_closure_iff_nhds_basis` over
  the `Ioo` basis), so the frontier of a fiber is first-order;
- **`definable_fiberFrontier`** — the set `Y = {(x,y) | y ∈ frontier(A_x)}` is definable: one
  parameterized quantifier block (`closBlock`, template-style) instantiated at the `A`-atom and
  its negation, glued by `frontier_eq_closure_inter_closure`;
- **`fiberFrontier_fiber_finite`** — `Y`'s fibers are *automatically finite*: the fiber of `Y`
  at `x` **is** the frontier of the fiber of `A` at `x`, and `Tame` is frontier-finiteness.
  `Y` is the uniform-finiteness engine's input: UF for `Y` bounds fiber boundaries for every
  definable `A`.

**Honest fence.** D0 only: no counting formulas (D1), no dichotomy or point functions (D2), no
curves (D3), no wall (D4).
-/
import Sundogcert.OMinimalContinuity

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalAbstract.Fml

/-! ### Pairs as two-variable points -/

/-- The pair `(x, y)` as a two-variable point. -/
def pairFn (x y : ℝ) : Fin 2 → ℝ := ![x, y]

@[simp] theorem pairFn_zero (x y : ℝ) : pairFn x y 0 = x := rfl

@[simp] theorem pairFn_one (x y : ℝ) : pairFn x y 1 = y := rfl

/-! ### Local snoc battery (literal indices) -/

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

private theorem snocF (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocG (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 2 = g 2 := by
  simp [Fin.snoc]

private theorem snocH (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 3 = y := by
  simp [Fin.snoc]

private theorem snocK (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocL (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 2 = g 2 := by
  simp [Fin.snoc]

private theorem snocM (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 3 = g 3 := by
  simp [Fin.snoc]

private theorem snocN (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 4 = y := by
  simp [Fin.snoc]

/-! ### The slice -/

/-- The composed reindex of the slice formula collapses to the pair. -/
private theorem comp10 (y z : ℝ) :
    ((Fin.snoc (fun _ => y) z : Fin 2 → ℝ) ∘ ![1, 0]) = pairFn z y := by
  funext k
  fin_cases k <;> simp [pairFn, Fin.snoc, Function.comp]

/-- **Parametric slices are tame** — the fiber of a two-variable definable at any real
parameter (C0's slicing IOU, discharged). -/
theorem tame_slice {S : OMinStructure} {A : Set (Fin 2 → ℝ)} (hA : S.Definable A) (x : ℝ) :
    Tame {y : ℝ | pairFn x y ∈ A} := by
  have h := Fml.tame_one (S := S) (Fml.ex (.and (eqConstAt 1 x) (.atom ![1, 0] hA)))
  have e : {y : ℝ | pairFn x y ∈ A} = {y : ℝ | Fml.eval (S := S) (n := 1)
      (Fml.ex (.and (eqConstAt 1 x) (.atom ![1, 0] hA))) (fun _ => y)} := by
    ext y
    simp only [Set.mem_setOf_eq, Fml.eval, eval_eqConstAt, snocB]
    constructor
    · intro hmem
      refine ⟨x, rfl, ?_⟩
      rw [comp10]
      exact hmem
    · rintro ⟨z, rfl, hmem⟩
      rw [comp10] at hmem
      exact hmem
  rw [e]
  exact h

/-! ### Closure and frontier in order terms -/

/-- Closure in pure order terms: every order-window around the point meets the set. -/
theorem mem_closure_iff_order (T : Set ℝ) (y : ℝ) :
    y ∈ closure T ↔ ∀ u v : ℝ, u < y → y < v → ∃ t, u < t ∧ t < v ∧ t ∈ T := by
  rw [mem_closure_iff_nhds_basis (nhds_basis_Ioo y)]
  constructor
  · intro h u v hu hv
    obtain ⟨t, hT, ht⟩ := h (u, v) ⟨hu, hv⟩
    rw [Set.mem_Ioo] at ht
    exact ⟨t, ht.1, ht.2, hT⟩
  · rintro h ⟨u, v⟩ ⟨hu, hv⟩
    obtain ⟨t, h1, h2, hT⟩ := h u v hu hv
    exact ⟨t, hT, Set.mem_Ioo.mpr ⟨h1, h2⟩⟩

/-! ### The fiber-frontier set -/

/-- `Y = {(x,y) | y ∈ frontier(A_x)}` — the fiber-boundary set. -/
def fiberFrontier (A : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {h | h 1 ∈ frontier {y : ℝ | pairFn (h 0) y ∈ A}}

/-- The parameterized closure block: `∀u ∀v (u < y ∧ y < v → ∃t (u < t ∧ t < v ∧ base))`,
with ambient coordinates `x = 0, y = 1, u = 2, v = 3, t = 4`. -/
private def closBlock {S : OMinStructure} (base : Fml S 5) : Fml S 2 :=
  .all (.all (((ltAt 2 1).and (ltAt 1 3)).imp
    (.ex ((ltAt 2 4).and ((ltAt 4 3).and base)))))

private theorem eval_closBlock {S : OMinStructure} (base : Fml S 5)
    {P : (Fin 2 → ℝ) → ℝ → Prop}
    (hbase : ∀ (f : Fin 2 → ℝ) (u v t : ℝ),
      base.eval (Fin.snoc (Fin.snoc (Fin.snoc f u : Fin 3 → ℝ) v : Fin 4 → ℝ) t) ↔ P f t)
    (f : Fin 2 → ℝ) :
    (closBlock base).eval f ↔
      ∀ u v : ℝ, u < f 1 → f 1 < v → ∃ t, u < t ∧ t < v ∧ P f t := by
  simp only [closBlock, Fml.eval, eval_all, eval_imp, eval_ltAt, hbase,
    snocD, snocE, snocF, snocG, snocH, snocL, snocM, snocN, and_imp]

/-- The atom's triple-snoc reindex collapses to the pair `(x, t)`. -/
private theorem comp04 (f : Fin 2 → ℝ) (u v t : ℝ) :
    ((Fin.snoc (Fin.snoc (Fin.snoc f u : Fin 3 → ℝ) v : Fin 4 → ℝ) t : Fin 5 → ℝ)
      ∘ ![0, 4]) = pairFn (f 0) t := by
  funext k
  fin_cases k <;> simp [pairFn, Fin.snoc, Function.comp]

/-- **The fiber-frontier set is definable**: two closure blocks (at the `A`-atom and its
negation), glued by `frontier = closure ∩ closure-of-complement`. -/
theorem definable_fiberFrontier {S : OMinStructure} {A : Set (Fin 2 → ℝ)}
    (hA : S.Definable A) : S.Definable (fiberFrontier A) := by
  have h := Fml.definable (S := S)
    ((closBlock (.atom ![0, 4] hA)).and (closBlock (.not (.atom ![0, 4] hA))))
  have hbase1 : ∀ (f : Fin 2 → ℝ) (u v t : ℝ),
      (Fml.atom (S := S) ![0, 4] hA).eval
        (Fin.snoc (Fin.snoc (Fin.snoc f u : Fin 3 → ℝ) v : Fin 4 → ℝ) t) ↔
      pairFn (f 0) t ∈ A := by
    intro f u v t
    simp only [Fml.eval]
    rw [comp04]
  have hbase2 : ∀ (f : Fin 2 → ℝ) (u v t : ℝ),
      (Fml.not (Fml.atom (S := S) ![0, 4] hA)).eval
        (Fin.snoc (Fin.snoc (Fin.snoc f u : Fin 3 → ℝ) v : Fin 4 → ℝ) t) ↔
      pairFn (f 0) t ∉ A := by
    intro f u v t
    simp only [Fml.eval]
    rw [comp04]
  have e : {f : Fin 2 → ℝ | Fml.eval
      ((closBlock (.atom ![0, 4] hA)).and (closBlock (.not (.atom ![0, 4] hA)))) f}
      = fiberFrontier A := by
    ext f
    rw [Set.mem_setOf_eq, show Fml.eval
        ((closBlock (.atom (S := S) ![0, 4] hA)).and
          (closBlock (.not (.atom ![0, 4] hA)))) f
        = ((closBlock (.atom (S := S) ![0, 4] hA)).eval f ∧
          (closBlock (.not (.atom (S := S) ![0, 4] hA))).eval f) from rfl,
      eval_closBlock _ hbase1 f, eval_closBlock _ hbase2 f]
    rw [fiberFrontier, Set.mem_setOf_eq, frontier_eq_closure_inter_closure,
      Set.mem_inter_iff, mem_closure_iff_order, mem_closure_iff_order]
    rfl
  rwa [e] at h

/-- **The engine input: fiber-frontier fibers are automatically finite** — the fiber of `Y` at
`x` *is* the frontier of the fiber of `A` at `x`, and tameness is frontier-finiteness. -/
theorem fiberFrontier_fiber_finite {S : OMinStructure} {A : Set (Fin 2 → ℝ)}
    (hA : S.Definable A) (x : ℝ) :
    {y : ℝ | pairFn x y ∈ fiberFrontier A}.Finite := by
  have e : {y : ℝ | pairFn x y ∈ fiberFrontier A}
      = frontier {y : ℝ | pairFn x y ∈ A} := by
    ext y
    simp only [fiberFrontier, Set.mem_setOf_eq, pairFn_zero, pairFn_one]
  rw [e]
  exact tame_slice hA x

end Sundog.OMinimalAbstract
