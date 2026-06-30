/-
# Polylog *gates* for the sawtooth: the explicit shared DAG (Slate-4 U-3, the literal gate count)

`SawtoothShared` proved the value core `R m x = x − Σ_{k=1}^m T^[k](x)/4^k` — the approximant is a
flat sum of `m` chain-shared iterated tents. This module turns that into the literal **`O(m)`-gate**
ReLU DAG, closing `SHARED_SIZE_NOT_CAPTURED`.

The blocker was that `compileToDag` maps `var i` to the *input* wire `i`, so it cannot read a
previously-built wire — walking the sawtooth tree recompiles the duplicated tent (exponential). The
fix is a one-line generalization, `compileWith σ p e`, mapping `var i` to an arbitrary wire `σ i`.
Its three theorems mirror `compileToDag`'s exactly. Then:

* `tentLayer p w := compileWith (fun _ => w) p tent` appends a tent reading wire `w` — a *constant*
  number of gates (`tent` is a fixed small tree), output evaluating to `T(value at w)`.
* `sawBuild m` folds `tentLayer` `m` times, threading the iterated-tent wire and an accumulator
  wire `accW = R k`. Each layer reuses the previous tent wire, so the chain is `O(m)`, not `2^m`.

The result `sawDag_*`: an `RProg 1 M` with `M ≤ C·m` whose accumulator wire evaluates to `R m`,
hence approximates `x²` to `1/(4·4^m)` (`SawtoothApprox.sq_sub_R_le`) — `ε` at `O(log 1/ε)` GATES.
-/
import Sundogcert.SawtoothShared

namespace Sundog.SawtoothDag

open Sundog.CircuitNet Sundog.DepthSeparation Sundog.SawtoothApprox Sundog.SawtoothShared

/-! ### The generalized sharing compiler: `var i ↦ wire σ i` -/

/-- `compileToDag` but with `var i` mapped to an arbitrary existing wire `σ i` (not the input
wire). This is the single change that lets a compiled tree *read* a previously-built wire — the
basis of chaining without duplication. -/
def compileWith {n : ℕ} :
    {m : ℕ} → (Fin n → Fin (n + m)) → RProg n m → Trop n → CompileRes n m
  | m, σ, p, .var i => ⟨m, le_refl m, p, σ i⟩
  | m, _, p, .const c => ⟨m + 1, Nat.le_succ m, p.snoc (.const c), lastWire n m⟩
  | _, σ, p, .scale c a =>
      let ra := compileWith σ p a
      ⟨ra.m' + 1, ra.hle.trans (Nat.le_succ ra.m'),
        ra.prog.snoc (.scale c ra.out), lastWire n ra.m'⟩
  | _, σ, p, .add a b =>
      let ra := compileWith σ p a
      let rb := compileWith (fun i => widenLe ra.hle (σ i)) ra.prog b
      ⟨rb.m' + 1, (ra.hle.trans rb.hle).trans (Nat.le_succ rb.m'),
        rb.prog.snoc (.add (widenLe rb.hle ra.out) rb.out), lastWire n rb.m'⟩
  | _, σ, p, .max a b =>
      let ra := compileWith σ p a
      let rb := compileWith (fun i => widenLe ra.hle (σ i)) ra.prog b
      ⟨rb.m' + 4, (ra.hle.trans rb.hle).trans (Nat.le_add_right rb.m' 4),
        rb.prog.appendMax (widenLe rb.hle ra.out) rb.out, RProg.appendMaxOut n rb.m'⟩

/-- Gate count: `≤ m + 4·nodeCount`, identical to `compileToDag`. -/
theorem compileWith_gate_count {n : ℕ} :
    ∀ {m : ℕ} (σ : Fin n → Fin (n + m)) (p : RProg n m) (e : Trop n),
      (compileWith σ p e).m' ≤ m + 4 * e.nodeCount := by
  intro m σ p e
  induction e generalizing m p σ with
  | var i => simp [compileWith, Trop.nodeCount]
  | const c => simp [compileWith, Trop.nodeCount]
  | scale c a ih => have h := ih σ p; simp only [compileWith, Trop.nodeCount]; omega
  | add a b iha ihb =>
      have h1 := iha σ p
      have h2 := ihb (fun i => widenLe (compileWith σ p a).hle (σ i)) (compileWith σ p a).prog
      simp only [compileWith, Trop.nodeCount]; omega
  | max a b iha ihb =>
      have h1 := iha σ p
      have h2 := ihb (fun i => widenLe (compileWith σ p a).hle (σ i)) (compileWith σ p a).prog
      simp only [compileWith, Trop.nodeCount]; omega

/-- Preservation: existing wires keep their value, identical to `compileToDag_preserves`. -/
theorem compileWith_preserves {n : ℕ} (x : Fin n → ℝ) (e : Trop n) :
    ∀ {m : ℕ} (σ : Fin n → Fin (n + m)) (p : RProg n m) (w : Fin (n + m))
      (w' : Fin (n + (compileWith σ p e).m')),
      w'.val = w.val → (compileWith σ p e).prog.eval x w' = p.eval x w := by
  induction e with
  | var i =>
      intro m σ p w w' hval
      simp only [compileWith] at w' ⊢
      exact congrArg _ (Fin.ext hval)
  | const c =>
      intro m σ p w w' hval
      simp only [compileWith] at w' ⊢
      have hi : w'.val < n + m := by have := w.isLt; omega
      rw [RProg.eval_snoc_lt p _ x w' hi]
      exact congrArg _ (Fin.ext hval)
  | scale c a ih =>
      intro m σ p w w' hval
      simp only [compileWith] at w' ⊢
      have hmono := (compileWith σ p a).hle
      have hi : w'.val < n + (compileWith σ p a).m' := by have := w.isLt; omega
      rw [RProg.eval_snoc_lt _ _ x w' hi]
      exact ih σ p w ⟨w'.val, hi⟩ hval
  | add a b iha ihb =>
      intro m σ p w w' hval
      simp only [compileWith] at w' ⊢
      have hma := (compileWith σ p a).hle
      have hmb := (compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
        (compileWith σ p a).prog b).hle
      have hi : w'.val < n + (compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
          (compileWith σ p a).prog b).m' := by have := w.isLt; omega
      rw [RProg.eval_snoc_lt _ _ x w' hi]
      have hib := ihb (fun i => widenLe (compileWith σ p a).hle (σ i)) (compileWith σ p a).prog
        ⟨w.val, by have := w.isLt; omega⟩ ⟨w'.val, hi⟩ hval
      rw [hib]
      exact iha σ p w ⟨w.val, by have := w.isLt; omega⟩ rfl
  | max a b iha ihb =>
      intro m σ p w w' hval
      simp only [compileWith] at w' ⊢
      have hma := (compileWith σ p a).hle
      have hmb := (compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
        (compileWith σ p a).prog b).hle
      have hi : w'.val < n + (compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
          (compileWith σ p a).prog b).m' := by have := w.isLt; omega
      simp only [RProg.appendMax]
      have h4 : w'.val < n + ((compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
        (compileWith σ p a).prog b).m' + 3) := by omega
      have h3 : w'.val < n + ((compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
        (compileWith σ p a).prog b).m' + 2) := by omega
      have h2 : w'.val < n + ((compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
        (compileWith σ p a).prog b).m' + 1) := by omega
      rw [RProg.eval_snoc_lt _ _ x w' h4, RProg.eval_snoc_lt _ _ x ⟨w'.val, h4⟩ h3,
        RProg.eval_snoc_lt _ _ x ⟨w'.val, h3⟩ h2, RProg.eval_snoc_lt _ _ x ⟨w'.val, h2⟩ hi]
      have hib := ihb (fun i => widenLe (compileWith σ p a).hle (σ i)) (compileWith σ p a).prog
        ⟨w.val, by have := w.isLt; omega⟩ ⟨w'.val, hi⟩ hval
      rw [hib]
      exact iha σ p w ⟨w.val, by have := w.isLt; omega⟩ rfl

/-- Output correctness: the output wire evaluates to `e` with `var i` bound to `p.eval x (σ i)`. -/
theorem compileWith_eval {n : ℕ} (x : Fin n → ℝ) (e : Trop n) :
    ∀ {m : ℕ} (σ : Fin n → Fin (n + m)) (p : RProg n m),
      (compileWith σ p e).prog.eval x (compileWith σ p e).out
        = e.eval (fun i => p.eval x (σ i)) := by
  induction e with
  | var i =>
      intro m σ p
      simp only [compileWith, Trop.eval_var]
  | const c =>
      intro m σ p
      simp only [compileWith, Trop.eval_const, RProg.eval_snoc_last, RGate.eval]
  | scale c a ih =>
      intro m σ p
      simp only [compileWith, Trop.eval_scale, RProg.eval_snoc_last, RGate.eval]
      rw [ih σ p]
  | add a b iha ihb =>
      intro m σ p
      simp only [compileWith, Trop.eval_add, RProg.eval_snoc_last, RGate.eval]
      have henv : (fun i => (compileWith σ p a).prog.eval x
            (widenLe (compileWith σ p a).hle (σ i)))
          = (fun i => p.eval x (σ i)) := by
        funext i
        exact compileWith_preserves x a σ p (σ i) (widenLe (compileWith σ p a).hle (σ i)) rfl
      rw [ihb (fun i => widenLe (compileWith σ p a).hle (σ i)) (compileWith σ p a).prog,
        compileWith_preserves x b (fun i => widenLe (compileWith σ p a).hle (σ i))
          (compileWith σ p a).prog (compileWith σ p a).out
          (widenLe (compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
            (compileWith σ p a).prog b).hle (compileWith σ p a).out) rfl,
        iha σ p, henv]
  | max a b iha ihb =>
      intro m σ p
      simp only [compileWith, Trop.eval_max]
      have henv : (fun i => (compileWith σ p a).prog.eval x
            (widenLe (compileWith σ p a).hle (σ i)))
          = (fun i => p.eval x (σ i)) := by
        funext i
        exact compileWith_preserves x a σ p (σ i) (widenLe (compileWith σ p a).hle (σ i)) rfl
      rw [appendMax_eval,
        compileWith_preserves x b (fun i => widenLe (compileWith σ p a).hle (σ i))
          (compileWith σ p a).prog (compileWith σ p a).out
          (widenLe (compileWith (fun i => widenLe (compileWith σ p a).hle (σ i))
            (compileWith σ p a).prog b).hle (compileWith σ p a).out) rfl,
        iha σ p, ihb (fun i => widenLe (compileWith σ p a).hle (σ i)) (compileWith σ p a).prog,
        henv]

/-! ### The tent layer: one tent gadget reading a chosen wire (constant gates) -/

/-- Append a tent reading wire `w`: the fixed tent tree compiled with its variable bound to `w`. -/
noncomputable def tentLayer {m : ℕ} (p : RProg 1 m) (w : Fin (1 + m)) : CompileRes 1 m :=
  compileWith (fun _ => w) p tent

theorem tentLayer_eval {m : ℕ} (p : RProg 1 m) (w : Fin (1 + m)) (x : Fin 1 → ℝ) :
    (tentLayer p w).prog.eval x (tentLayer p w).out = T (p.eval x w) := by
  rw [tentLayer, compileWith_eval, tent_eval]

theorem tentLayer_gate {m : ℕ} (p : RProg 1 m) (w : Fin (1 + m)) :
    (tentLayer p w).m' ≤ m + 52 := by
  have h := compileWith_gate_count (fun _ => w) p tent
  have ht : tent.nodeCount = 13 := rfl
  rw [ht] at h
  simp only [tentLayer]
  omega

theorem tentLayer_preserves {m : ℕ} (p : RProg 1 m) (w : Fin (1 + m)) (x : Fin 1 → ℝ)
    (v : Fin (1 + m)) (w' : Fin (1 + (tentLayer p w).m')) (hval : w'.val = v.val) :
    (tentLayer p w).prog.eval x w' = p.eval x v :=
  compileWith_preserves x tent (fun _ => w) p v w' hval

/-- The incremental closed form: `R (k+1) = R k − T^[k+1]/4^{k+1}` (one new chain term). -/
theorem R_succ_sub (k : ℕ) (x : ℝ) : R (k + 1) x = R k x - T^[k + 1] x / 4 ^ (k + 1) := by
  rw [R_eq_iteratedTents, R_eq_iteratedTents, Finset.sum_range_succ]
  ring

/-! ### The chain + accumulator: fold the tent layer `m` times -/

/-- A built sawtooth DAG state: program with `M` gates, the current iterated-tent wire, and the
running accumulator wire. -/
structure SawSt where
  M : ℕ
  prog : RProg 1 M
  tentW : Fin (1 + M)
  accW : Fin (1 + M)

/-- Build the sawtooth DAG: `sawBuild 0` is the bare input; `sawBuild (k+1)` appends one tent layer
(reading the previous tent wire) and two accumulator gates `acc ← acc − T^[k+1]/4^{k+1}`. Each
layer reuses the previous wire, so the gate count is `O(k)`. -/
noncomputable def sawBuild : ℕ → SawSt
  | 0 => ⟨0, RProg.nil, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
  | (k + 1) =>
      let s := sawBuild k
      let tl := tentLayer s.prog s.tentW
      ⟨tl.m' + 2,
       (tl.prog.snoc (.scale (-(1 / 4 ^ (k + 1))) tl.out)).snoc
         (.add (widenLe (by have := tl.hle; omega) s.accW) (lastWire 1 tl.m')),
       widenLe (by omega) tl.out,
       lastWire 1 (tl.m' + 1)⟩

/-- **The chain invariants.** `sawBuild k`'s tent wire evaluates to the `k`-fold tent `T^[k] x`, and
its accumulator wire evaluates to `R k x` — proved by induction, each step threading the previous
wires through the appended gates via preservation. -/
theorem sawBuild_eval (x : ℝ) (k : ℕ) :
    (sawBuild k).prog.eval (fun _ => x) (sawBuild k).tentW = (T^[k]) x
      ∧ (sawBuild k).prog.eval (fun _ => x) (sawBuild k).accW = R k x := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [sawBuild, RProg.eval]; rfl
    · simp only [sawBuild, RProg.eval, R]
  | succ k ih =>
    obtain ⟨iht, iha⟩ := ih
    simp only [sawBuild]
    set tl := tentLayer (sawBuild k).prog (sawBuild k).tentW with htl
    have htlout : tl.prog.eval (fun _ => x) tl.out = (T^[k + 1]) x := by
      rw [htl, tentLayer_eval, iht, Function.iterate_succ_apply']
    have hpres : ∀ (w0 : Fin (1 + tl.m')), w0.val = (sawBuild k).accW.val →
        tl.prog.eval (fun _ => x) w0 = R k x := fun w0 hw0 =>
      (tentLayer_preserves (sawBuild k).prog (sawBuild k).tentW (fun _ => x)
        (sawBuild k).accW w0 hw0).trans iha
    refine ⟨?_, ?_⟩
    · -- tent wire: T^[k+1] x
      rw [RProg.eval_snoc_lt _ _ _ _ (Nat.lt_succ_of_lt tl.out.isLt),
        RProg.eval_snoc_lt _ _ _ _ tl.out.isLt]
      exact htlout
    · -- accumulator wire: R (k+1) x
      have op2val : (tl.prog.snoc (.scale (-(1 / 4 ^ (k + 1))) tl.out)).eval (fun _ => x)
          (lastWire 1 tl.m') = -(1 / 4 ^ (k + 1)) * (T^[k + 1]) x := by
        rw [RProg.eval_snoc_last, RGate.eval, htlout]
      have op1val : (tl.prog.snoc (.scale (-(1 / 4 ^ (k + 1))) tl.out)).eval (fun _ => x)
          (widenLe (Nat.le_succ_of_le tl.hle) (sawBuild k).accW) = R k x := by
        rw [RProg.eval_snoc_lt _ _ _ _
          (Nat.lt_of_lt_of_le (sawBuild k).accW.isLt (Nat.add_le_add_left tl.hle 1))]
        exact hpres _ rfl
      rw [RProg.eval_snoc_last, RGate.eval, op1val, op2val, R_succ_sub]
      ring

/-! ### Gate count and the polylog-gate headline -/

/-- **Linear gate count.** `sawBuild m` has `≤ 54·m` gates — each tent layer adds a constant `≤ 52`
(the tent tree compiled once) plus the two accumulator gates. This is the sharing payoff: the tree
form of `Rcirc m` was *exponential*, the shared DAG is `O(m)`. -/
theorem sawBuild_gate (m : ℕ) : (sawBuild m).M ≤ 54 * m := by
  induction m with
  | zero => simp [sawBuild]
  | succ k ih =>
    have h := tentLayer_gate (sawBuild k).prog (sawBuild k).tentW
    simp only [sawBuild]
    omega

/-- **The shared sawtooth DAG approximates `x²`.** Its accumulator wire is within `1/(4·4^m)` of
`x²` on `[0,1]` (the value core `sawBuild_eval` = `R m`, then `SawtoothApprox.sq_sub_R_le`). -/
theorem sawDag_approx (m : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ 2 - (sawBuild m).prog.eval (fun _ => x) (sawBuild m).accW| ≤ 1 / (4 * 4 ^ m) := by
  rw [(sawBuild_eval x m).2]
  exact sq_sub_R_le m x hx

/-- **Polylog GATES (the `SHARED_SIZE_NOT_CAPTURED` follow-on, closed).** For every `ε > 0` there is
an explicit ReLU DAG of `≤ 54·m` **gates** whose output is within `ε` of `x²` on `[0,1]`, where
`1/(4·4^m) ≤ ε` — i.e. error `ε` at `O(log 1/ε)` gates (not the exponential tree size the
tree-keyed cost bound saw). The sharing the `compileToDag` tree walk could not exploit, built by
hand via `compileWith` + the iterated-tent chain. -/
theorem sawDag_polylog (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        |x ^ 2 - (sawBuild m).prog.eval (fun _ => x) (sawBuild m).accW| ≤ ε) ∧
      (sawBuild m).M ≤ 54 * m ∧
      (1 : ℝ) / (4 * 4 ^ m) ≤ ε := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (4 * ε)) (by norm_num : (1 : ℝ) < 4)
  have hδ : (1 : ℝ) / (4 * 4 ^ m) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have h4ε : (0 : ℝ) < 4 * ε := by positivity
    rw [div_lt_iff₀ h4ε] at hm
    nlinarith [hm]
  exact ⟨m, fun x hx => le_trans (sawDag_approx m x hx) hδ, sawBuild_gate m, hδ⟩

end Sundog.SawtoothDag
