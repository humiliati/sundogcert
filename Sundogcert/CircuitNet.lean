/-
# Exact compilation of tropical (piecewise-linear) circuits into ReLU networks

Another worked example of the discipline in `Sundogcert.Certificate`: **machine-check
the constructive deductive core, name the imported wall.** The certificate is
finite-field algebra; the sorting certificate is combinatorics; this is the
**circuit-complexity / approximation-theory** sibling.

It formalizes the *exact* (ε = 0) special case of the circuit→network compilation
theorem (Kratsios–Brugiapaglia–Kim–Cousins–Sáez de Ocáriz Borde,
*Algorithmic Foundations of Deep Learning*, arXiv:2606.26705, Thm 3.2) for the
**piecewise-linear / tropical** gate fragment — the gate set on which that paper's
headline all-pairs-shortest-paths corollary (Cor 5.1, a min-plus circuit) runs.

## What is PROVED here (the deductive core)

A **tropical circuit** `Trop n` over `n` real inputs uses the exactly-ReLU-representable
fragment of the gate language `𝔾_t-alg`: constants, real addition (the tropical
"product" that combines a signal with an edge weight), scaling by a real constant, and
`max` (the tropical "sum"). A **ReLU network** `Net n` is an arithmetic circuit whose
only nonlinearity is `relu x = max x 0`.

* **`compile_eval` (THE CORE).** A structural compiler `compile : Trop n → Net n` is
  **exact**: `(compile e).eval x = e.eval x` for *every* tropical circuit `e` and every
  input `x` — proved by induction over the circuit. The only nonlinear case is the
  algebraic identity `max p q = q + relu (p − q)`, kernel-checked over `ℝ`.
* **`compile_depth_le` (the resource bound).** The compiled network's depth is **linear**
  in the circuit's depth: `(compile e).depth ≤ 4 * e.depth`. Depth is exactly the
  resource the paper's Cor 5.1 bounds (`O(k log k)` for `k`-vertex shortest paths).
* **Derived min-plus gates, each proved exact.** `min`, `neg`, `abs`, a single
  Bellman–Ford **edge relaxation** `relaxEdge d_i d_j w = min (d_i) (d_j + w)`, and the
  `bellmanStep` that folds a list of incoming edges — all *defined* from the four
  primitive gates and proved to evaluate correctly (`min_eval`, `abs_eval`,
  `relaxEdge_eval`, `bellmanStep_eval`). These are the atomic operations of the
  min-plus / shortest-path circuit, so the APSP example compiles to a ReLU net by the
  same exact theorem (`bellmanStep_compiles_exactly`).

o-minimality / definability does **zero** work here: every step is finite real algebra,
re-checked by the kernel. That is the point — this core earns its place without leaning
on the imported definability machinery.

## The IMPORTED WALL (named, NOT proved here)

* **The analytic gates.** Real *multiplication of two variables*, reciprocal `x ↦ 1/x`,
  and radicals `x ↦ x^{1/ℓ}` are **not** piecewise-linear and are **not** exactly
  ReLU-representable; the paper compiles them only **approximately** (`ε > 0`), and *that*
  is where o-minimality and Newton-iteration error analysis live. They are deliberately
  outside this exact core — the honest boundary of the piecewise-linear fragment.
* **Linear gate COUNT needs a DAG.** The exact identity `max p q = q + relu (p − q)`
  shares the operand `q`. A *tree*-shaped circuit duplicates it, so nested `max`/`min`
  (a deep min-plus circuit) blows up gate count; only a **DAG** (wire fan-out) keeps the
  count linear. This module proves the linear **depth** bound (tree-stable); the
  *gate-count* linearity is a DAG/sharing statement — named here, not proved (a clean
  next increment, a compiler-correctness proof with wire-index refinement).
* **Trainability.** This is an *existence* result: it bounds the size of a network that
  *can* compute the circuit. That SGD *finds* those weights is imported, never proved —
  the same wall the whole development carries.

## References
* Kratsios, Brugiapaglia, Kim, Cousins, Sáez de Ocáriz Borde,
  *Algorithmic Foundations of Deep Learning* (arXiv:2606.26705), Thm 3.1–3.2, Cor 5.1.
* `max p q = q + relu (p − q)`: the standard ReLU representation of `max`/`abs`
  (e.g. Goodfellow–Bengio–Courville, *Deep Learning*, §6.3).
* Cormen–Leiserson–Rivest–Stein, *Introduction to Algorithms*, §24 (Bellman–Ford / the
  min-plus relaxation step).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Sundog.CircuitNet

variable {n : ℕ}

/-- A **tropical (piecewise-linear) circuit** over `n` real inputs: the
exactly-ReLU-representable fragment of `𝔾_t-alg` — constants, real addition (tropical
"product"), scaling by a real constant, and `max` (tropical "sum"). `min`, `neg`, `abs`
and the min-plus relaxation step are *derived* (smart constructors below). -/
inductive Trop (n : ℕ) where
  | var   : Fin n → Trop n
  | const : ℝ → Trop n
  | add   : Trop n → Trop n → Trop n
  | scale : ℝ → Trop n → Trop n
  | max   : Trop n → Trop n → Trop n

/-- A **ReLU network** as an arithmetic circuit whose only nonlinearity is
`relu x = max x 0`: constants, addition, scaling by a constant, and `relu`. -/
inductive Net (n : ℕ) where
  | var   : Fin n → Net n
  | const : ℝ → Net n
  | add   : Net n → Net n → Net n
  | scale : ℝ → Net n → Net n
  | relu  : Net n → Net n

/-- Denotation of a tropical circuit at an input `x : Fin n → ℝ`. -/
def Trop.eval : Trop n → (Fin n → ℝ) → ℝ
  | .var i,     x => x i
  | .const c,   _ => c
  | .add a b,   x => a.eval x + b.eval x
  | .scale c a, x => c * a.eval x
  | .max a b,   x => Max.max (a.eval x) (b.eval x)

/-- Denotation of a ReLU network at an input `x : Fin n → ℝ`. -/
def Net.eval : Net n → (Fin n → ℝ) → ℝ
  | .var i,     x => x i
  | .const c,   _ => c
  | .add a b,   x => a.eval x + b.eval x
  | .scale c a, x => c * a.eval x
  | .relu a,    x => Max.max (a.eval x) 0

-- Per-constructor `rfl` evaluation lemmas (so `simp` reliably unfolds `eval`).
@[simp] theorem Trop.eval_var (i : Fin n) (x : Fin n → ℝ) :
    (Trop.var i).eval x = x i := rfl
@[simp] theorem Trop.eval_const (c : ℝ) (x : Fin n → ℝ) :
    (Trop.const c : Trop n).eval x = c := rfl
@[simp] theorem Trop.eval_add (a b : Trop n) (x : Fin n → ℝ) :
    (Trop.add a b).eval x = a.eval x + b.eval x := rfl
@[simp] theorem Trop.eval_scale (c : ℝ) (a : Trop n) (x : Fin n → ℝ) :
    (Trop.scale c a).eval x = c * a.eval x := rfl
@[simp] theorem Trop.eval_max (a b : Trop n) (x : Fin n → ℝ) :
    (Trop.max a b).eval x = Max.max (a.eval x) (b.eval x) := rfl

@[simp] theorem Net.eval_var (i : Fin n) (x : Fin n → ℝ) :
    (Net.var i).eval x = x i := rfl
@[simp] theorem Net.eval_const (c : ℝ) (x : Fin n → ℝ) :
    (Net.const c : Net n).eval x = c := rfl
@[simp] theorem Net.eval_add (a b : Net n) (x : Fin n → ℝ) :
    (Net.add a b).eval x = a.eval x + b.eval x := rfl
@[simp] theorem Net.eval_scale (c : ℝ) (a : Net n) (x : Fin n → ℝ) :
    (Net.scale c a).eval x = c * a.eval x := rfl
@[simp] theorem Net.eval_relu (a : Net n) (x : Fin n → ℝ) :
    (Net.relu a).eval x = Max.max (a.eval x) 0 := rfl

/-- The structural compiler. Affine gates pass through unchanged; the single nonlinear
gate uses the exact ReLU identity `max p q = q + relu (p − q)`, with `p − q` written as
`p + (-1)·q`. -/
def compile : Trop n → Net n
  | .var i     => .var i
  | .const c   => .const c
  | .add a b   => .add (compile a) (compile b)
  | .scale c a => .scale c (compile a)
  | .max a b   => .add (compile b) (.relu (.add (compile a) (.scale (-1) (compile b))))

/-- **Exact compilation (THE DEDUCTIVE CORE).** Every tropical circuit compiles to a
ReLU network computing the *same* real function, exactly (no error term), at every
input. Proof: structural induction; the only nonlinear case is `max p q = q + relu(p−q)`,
discharged by `le_total`. -/
theorem compile_eval (e : Trop n) (x : Fin n → ℝ) :
    (compile e).eval x = e.eval x := by
  induction e with
  | var i => rfl
  | const c => rfl
  | add a b iha ihb => simp [compile, iha, ihb]
  | scale c a ih => simp [compile, ih]
  | max a b iha ihb =>
      simp only [compile, Net.eval_add, Net.eval_relu, Net.eval_scale, Trop.eval_max,
        iha, ihb]
      rcases le_total (a.eval x) (b.eval x) with h | h
      · -- a ≤ b: RHS max = b; and p − q = a − b ≤ 0 so relu = 0
        rw [max_eq_right h]
        have hle : a.eval x + (-1) * b.eval x ≤ 0 := by linarith
        rw [max_eq_right hle]; ring
      · -- b ≤ a: RHS max = a; and p − q = a − b ≥ 0 so relu = a − b
        rw [max_eq_left h]
        have hge : (0 : ℝ) ≤ a.eval x + (-1) * b.eval x := by linarith
        rw [max_eq_left hge]; ring

/-! ## Resource bound: linear depth -/

/-- Depth of a tropical circuit (longest gate path; inputs/constants have depth 0). -/
def Trop.depth : Trop n → ℕ
  | .var _     => 0
  | .const _   => 0
  | .add a b   => 1 + Nat.max a.depth b.depth
  | .scale _ a => 1 + a.depth
  | .max a b   => 1 + Nat.max a.depth b.depth

/-- Depth of a ReLU network. -/
def Net.depth : Net n → ℕ
  | .var _     => 0
  | .const _   => 0
  | .add a b   => 1 + Nat.max a.depth b.depth
  | .scale _ a => 1 + a.depth
  | .relu a    => 1 + a.depth

/-- **The compiled network's depth is linear in the circuit's depth.** Each tropical
gate adds at most a constant to the depth (the `max` gate, the worst case, expands to a
fixed `add/relu/add/scale` stack), so depth is preserved up to the factor `4`. This is
the resource the paper's Cor 5.1 controls (`O(k log k)` depth for `k`-vertex APSP). -/
theorem compile_depth_le (e : Trop n) : (compile e).depth ≤ 4 * e.depth := by
  induction e with
  | var i => simp [compile, Net.depth, Trop.depth]
  | const c => simp [compile, Net.depth, Trop.depth]
  | add a b iha ihb =>
      simp only [compile, Net.depth, Trop.depth, Nat.max_def]
      split_ifs <;> omega
  | scale c a ih =>
      simp only [compile, Net.depth, Trop.depth]
      omega
  | max a b iha ihb =>
      simp only [compile, Net.depth, Trop.depth, Nat.max_def]
      split_ifs <;> omega

/-! ## Derived min-plus gates (the APSP / Cor 5.1 building blocks), each proved exact -/

/-- Negation as a derived gate: `neg a = (-1) · a`. -/
def Trop.neg (a : Trop n) : Trop n := .scale (-1) a

@[simp] theorem neg_eval (a : Trop n) (x : Fin n → ℝ) :
    (a.neg).eval x = - a.eval x := by
  simp [Trop.neg]

/-- Minimum as a derived gate: `min a b = -max (-a) (-b)`. -/
def Trop.min (a b : Trop n) : Trop n := (Trop.max a.neg b.neg).neg

@[simp] theorem min_eval (a b : Trop n) (x : Fin n → ℝ) :
    (a.min b).eval x = Min.min (a.eval x) (b.eval x) := by
  simp only [Trop.min, neg_eval, Trop.eval_max]
  rcases le_total (a.eval x) (b.eval x) with h | h
  · rw [min_eq_left h, max_eq_left (neg_le_neg h), neg_neg]
  · rw [min_eq_right h, max_eq_right (neg_le_neg h), neg_neg]

/-- Absolute value as a derived gate: `abs a = max a (-a)`. -/
def Trop.abs (a : Trop n) : Trop n := Trop.max a a.neg

@[simp] theorem abs_eval (a : Trop n) (x : Fin n → ℝ) :
    (a.abs).eval x = |a.eval x| := by
  simp only [Trop.abs, Trop.eval_max, neg_eval]
  rcases le_total (0 : ℝ) (a.eval x) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]

/-- A single **Bellman–Ford edge relaxation** (the atomic min-plus operation): relax the
current distance `dCur` against an incoming edge `dPrev + w`. -/
def Trop.relaxEdge (dCur dPrev : Trop n) (w : ℝ) : Trop n :=
  dCur.min (dPrev.add (.const w))

@[simp] theorem relaxEdge_eval (dCur dPrev : Trop n) (w : ℝ) (x : Fin n → ℝ) :
    (dCur.relaxEdge dPrev w).eval x = Min.min (dCur.eval x) (dPrev.eval x + w) := by
  simp [Trop.relaxEdge]

/-- A full **Bellman–Ford relaxation step** at one vertex: fold a list of incoming edges
`(dPrev, w)` into a starting distance, taking the running min-plus. This is the inner
loop of the all-pairs-shortest-paths circuit; by `compile_eval` it compiles exactly to a
ReLU network. -/
def Trop.bellmanStep (d0 : Trop n) (edges : List (Trop n × ℝ)) : Trop n :=
  edges.foldl (fun acc e => acc.relaxEdge e.1 e.2) d0

@[simp] theorem bellmanStep_eval (d0 : Trop n) (edges : List (Trop n × ℝ))
    (x : Fin n → ℝ) :
    (d0.bellmanStep edges).eval x =
      edges.foldl (fun acc e => Min.min acc (e.1.eval x + e.2)) (d0.eval x) := by
  unfold Trop.bellmanStep
  induction edges generalizing d0 with
  | nil => rfl
  | cons hd tl ih => simp [List.foldl, ih]

/-- **The APSP corollary, concretely.** Any Bellman–Ford relaxation step — the building
block of the all-pairs-shortest-paths min-plus circuit — compiles to a ReLU network that
computes the *exact same* min-plus value. This is the paper's Cor 5.1 example realized by
the exact compilation theorem (the size/error there is the *approximation* of the analytic
post-processing, not of the tropical core, which is exact). -/
theorem bellmanStep_compiles_exactly (d0 : Trop n) (edges : List (Trop n × ℝ))
    (x : Fin n → ℝ) :
    (compile (d0.bellmanStep edges)).eval x =
      edges.foldl (fun acc e => Min.min acc (e.1.eval x + e.2)) (d0.eval x) := by
  rw [compile_eval, bellmanStep_eval]

end Sundog.CircuitNet

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.CircuitNet.compile_eval
#print axioms Sundog.CircuitNet.compile_depth_le
#print axioms Sundog.CircuitNet.bellmanStep_compiles_exactly
