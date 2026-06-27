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
  count linear. This module now proves the local sharing receipt (`appendMax_eval`):
  once `p` and `q` are existing wires, the ReLU max gadget appends exactly four gates and
  reuses `q` by index. The full recursive source-DAG → target-DAG compiler remains the
  next wall.
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

/-! ## Sharing-aware DAG gate count -/

/-- A wire program gate whose operands may reference either the `n` external inputs or
one of the `m` already-built gates. The `Fin (n + m)` index is the acyclicity discipline:
new gates cannot point to future gates. -/
inductive RGate (n : ℕ) : ℕ → Type where
  | const {m : ℕ} : ℝ → RGate n m
  | add   {m : ℕ} : Fin (n + m) → Fin (n + m) → RGate n m
  | scale {m : ℕ} : ℝ → Fin (n + m) → RGate n m
  | relu  {m : ℕ} : Fin (n + m) → RGate n m

/-- A straight-line ReLU DAG with `m` internal gates. Fan-out is free: later gates may
reuse any earlier wire by index. -/
inductive RProg (n : ℕ) : ℕ → Type where
  | nil : RProg n 0
  | snoc {m : ℕ} : RProg n m → RGate n m → RProg n (m + 1)

/-- The gate count of a typed straight-line DAG is carried by its index. -/
def RProg.gateCount {n m : ℕ} (_ : RProg n m) : ℕ := m

@[simp] theorem RProg.gateCount_snoc {n m : ℕ} (p : RProg n m) (g : RGate n m) :
    (p.snoc g).gateCount = p.gateCount + 1 := rfl

/-- Reinterpret an existing wire inside a larger program extension. -/
def widenWire {n m extra : ℕ} (w : Fin (n + m)) : Fin (n + (m + extra)) :=
  ⟨w.val, by omega⟩

/-- The wire produced by appending the next gate to a program with `m` internal gates. -/
def lastWire (n m : ℕ) : Fin (n + (m + 1)) :=
  ⟨n + m, by omega⟩

/-- Extend an environment by one newly computed gate value. -/
def extendEnv {k : ℕ} (env : Fin k → ℝ) (v : ℝ) : Fin (k + 1) → ℝ :=
  fun i => if h : i.val < k then env ⟨i.val, h⟩ else v

@[simp] theorem extendEnv_widen {n m : ℕ} (env : Fin (n + m) → ℝ) (v : ℝ)
    (w : Fin (n + m)) :
    extendEnv env v (widenWire (extra := 1) w) = env w := by
  unfold extendEnv widenWire
  simp [w.isLt]

@[simp] theorem extendEnv_last {k : ℕ} (env : Fin k → ℝ) (v : ℝ) :
    extendEnv env v ⟨k, by omega⟩ = v := by
  simp [extendEnv]

/-- Evaluate one DAG gate against the current wire environment. -/
def RGate.eval {n m : ℕ} (g : RGate n m) (env : Fin (n + m) → ℝ) : ℝ :=
  match g with
  | .const c => c
  | .add a b => env a + env b
  | .scale c a => c * env a
  | .relu a => Max.max (env a) 0

/-- Evaluate a straight-line ReLU DAG, returning the value of every available wire. -/
def RProg.eval {n m : ℕ} (p : RProg n m) (x : Fin n → ℝ) : Fin (n + m) → ℝ :=
  match p with
  | .nil => fun i =>
      have h : i.val < n := i.isLt
      x ⟨i.val, h⟩
  | .snoc p g =>
      let env := p.eval x
      extendEnv env (g.eval env)

@[simp] theorem RProg.eval_snoc_old {n m : ℕ} (p : RProg n m) (g : RGate n m)
    (x : Fin n → ℝ) (w : Fin (n + m)) :
    (RProg.snoc p g).eval x (widenWire (extra := 1) w) = p.eval x w := by
  exact extendEnv_widen (p.eval x) (g.eval (p.eval x)) w

@[simp] theorem RProg.eval_snoc_last {n m : ℕ} (p : RProg n m) (g : RGate n m)
    (x : Fin n → ℝ) :
    (RProg.snoc p g).eval x (lastWire n m) = g.eval (p.eval x) := by
  simp [RProg.eval, lastWire]

/-- Append the shared-wire ReLU gadget
`max a b = b + relu(a - b)` to an existing DAG. The input wire `b` is used twice by
fan-out; it is not duplicated as a subtree. -/
def RProg.appendMax {n m : ℕ} (p : RProg n m) (a b : Fin (n + m)) : RProg n (m + 4) :=
  let a1 : Fin (n + (m + 1)) := widenWire (extra := 1) a
  let b1 : Fin (n + (m + 1)) := widenWire (extra := 1) b
  let b2 : Fin (n + (m + 2)) := widenWire (extra := 1) b1
  let b3 : Fin (n + (m + 3)) := widenWire (extra := 1) b2
  let p1 : RProg n (m + 1) := p.snoc (.scale (-1) b)
  let p2 : RProg n (m + 2) :=
    p1.snoc (.add a1 (lastWire n m))
  let p3 : RProg n (m + 3) := p2.snoc (.relu (lastWire n (m + 1)))
  p3.snoc (.add b3 (lastWire n (m + 2)))

/-- The output wire of `appendMax`. -/
def RProg.appendMaxOut (n m : ℕ) : Fin (n + (m + 4)) :=
  lastWire n (m + 3)

/-- The local sharing-aware gate-count receipt: a tropical `max` needs exactly four new
ReLU DAG gates (`scale`, `add`, `relu`, `add`) when existing operands are wires. -/
theorem appendMax_gate_count {n m : ℕ} (p : RProg n m) (a b : Fin (n + m)) :
    (p.appendMax a b).gateCount = p.gateCount + 4 := rfl

/-- Correctness of the shared-wire `max` gadget. This is the local lemma that the
tree-shaped compiler was missing for gate-count accounting: the operand `b` is reused
as a wire, and the four appended gates compute `max a b`. -/
theorem appendMax_eval {n m : ℕ} (p : RProg n m) (a b : Fin (n + m)) (x : Fin n → ℝ) :
    (p.appendMax a b).eval x (RProg.appendMaxOut n m) =
      Max.max (p.eval x a) (p.eval x b) := by
  simp only [RProg.appendMax, RProg.appendMaxOut]
  simp only [RProg.eval_snoc_last, RProg.eval_snoc_old, RGate.eval]
  rcases le_total (p.eval x a) (p.eval x b) with h | h
  · rw [max_eq_right h]
    have hle : p.eval x a + (-1) * p.eval x b ≤ 0 := by linarith
    rw [max_eq_right hle]
    ring_nf
  · rw [max_eq_left h]
    have hge : (0 : ℝ) ≤ p.eval x a + (-1) * p.eval x b := by linarith
    rw [max_eq_left hge]
    ring_nf

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

/-! ## Recursive tree → DAG compiler (the linear gate-count thread)

The local `appendMax` gadget folds over an entire tropical *tree* to give a *sharing*
compiler `compileToDag : Trop n → RProg n _`: each subtree is compiled once and reused by
its output wire, so an `N`-node tree yields a `≤ 4N`-gate ReLU DAG — the linear gate count
the tree-to-tree `compile` could not have (Phase 1: the construction + the gate-count
bound; the eval-correctness of the output wire is the next increment). -/

/-- Node count of a tropical tree — the source circuit's size. -/
def Trop.nodeCount : Trop n → ℕ
  | .var _     => 1
  | .const _   => 1
  | .add a b   => a.nodeCount + b.nodeCount + 1
  | .scale _ a => a.nodeCount + 1
  | .max a b   => a.nodeCount + b.nodeCount + 1

/-- Reinterpret a wire in a program that has grown from `a` to `b ≥ a` gates. Absolute
indices stay valid, so this is just the `.val`-preserving cast. -/
def widenLe {n a b : ℕ} (h : a ≤ b) (w : Fin (n + a)) : Fin (n + b) :=
  ⟨w.val, by omega⟩

/-- The result of compiling a tropical tree onto an existing DAG `p` with `m` gates:
the new gate count `m'`, a proof the program only grew (`m ≤ m'`), the extended program,
and the output wire computing the tree. -/
structure CompileRes (n m : ℕ) where
  m'   : ℕ
  hle  : m ≤ m'
  prog : RProg n m'
  out  : Fin (n + m')

/-- **The recursive sharing compiler.** Fold the `appendMax` gadget (and single-gate
appends) over a tropical tree, threading the running DAG. Each subtree is compiled once
and handed back as a wire, so there is no subtree duplication. -/
def compileToDag {n : ℕ} : {m : ℕ} → RProg n m → Trop n → CompileRes n m
  | m, p, .var i     => ⟨m, le_refl m, p, ⟨i.val, by have := i.isLt; omega⟩⟩
  | m, p, .const c   => ⟨m + 1, Nat.le_succ m, p.snoc (.const c), lastWire n m⟩
  | _, p, .scale c a =>
      let ra := compileToDag p a
      ⟨ra.m' + 1, ra.hle.trans (Nat.le_succ ra.m'),
        ra.prog.snoc (.scale c ra.out), lastWire n ra.m'⟩
  | _, p, .add a b =>
      let ra := compileToDag p a
      let rb := compileToDag ra.prog b
      ⟨rb.m' + 1, (ra.hle.trans rb.hle).trans (Nat.le_succ rb.m'),
        rb.prog.snoc (.add (widenLe rb.hle ra.out) rb.out), lastWire n rb.m'⟩
  | _, p, .max a b =>
      let ra := compileToDag p a
      let rb := compileToDag ra.prog b
      ⟨rb.m' + 4, (ra.hle.trans rb.hle).trans (Nat.le_add_right rb.m' 4),
        rb.prog.appendMax (widenLe rb.hle ra.out) rb.out, RProg.appendMaxOut n rb.m'⟩

/-- **The recursive compiler is gate-count linear (Phase 1).** Compiling an `N`-node
tropical tree onto a DAG with `m` gates yields a DAG with at most `m + 4N` gates —
exactly the linear gate count the tree-to-tree `compile` could not achieve, because the
shared-wire `max` gadget appends a constant (4) per source node with no duplication. -/
theorem compileToDag_gate_count {n : ℕ} :
    ∀ {m : ℕ} (p : RProg n m) (e : Trop n),
      (compileToDag p e).m' ≤ m + 4 * e.nodeCount := by
  intro m p e
  induction e generalizing m p with
  | var i => simp [compileToDag, Trop.nodeCount]
  | const c => simp [compileToDag, Trop.nodeCount]
  | scale c a ih =>
      have h := ih p
      simp only [compileToDag, Trop.nodeCount]
      omega
  | add a b iha ihb =>
      have h1 := iha p
      have h2 := ihb (compileToDag p a).prog
      simp only [compileToDag, Trop.nodeCount]
      omega
  | max a b iha ihb =>
      have h1 := iha p
      have h2 := ihb (compileToDag p a).prog
      simp only [compileToDag, Trop.nodeCount]
      omega

end Sundog.CircuitNet

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.CircuitNet.compile_eval
#print axioms Sundog.CircuitNet.compile_depth_le
#print axioms Sundog.CircuitNet.appendMax_eval
#print axioms Sundog.CircuitNet.compileToDag_gate_count
#print axioms Sundog.CircuitNet.bellmanStep_compiles_exactly
