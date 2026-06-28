/-
# The cancellation-free (monotone) tropical fragment — locating the monotone-vs-general wall

This is the Lean realization of slate hook **C-B1**. `CircuitNet` compiles tropical
circuits into ReLU nets *exactly*, and a ReLU net is a tropical **rational** map — it has
subtraction, hence cancellation. The classical **unconditional** monotone `(min,+)` /
`(max,+)` circuit lower bounds (Jerrum–Snir 1982 and successors) live over tropical
**polynomials** — monotone, no cancellation. So a monotone lower bound transfers to ReLU
only on a *cancellation-free* fragment. This module **defines that fragment and proves it
is proper**, pinning down exactly where the transfer is valid and where the wall stands.

## What is PROVED here (Phase 1)

The cancellation-free fragment is the **monotone (max-plus polynomial) sub-grammar** of
`CircuitNet.Trop`: `var`, `const`, `add`, `max`, and `scale c` **only for `c ≥ 0`** — the
predicate `IsMono`. (The right "cancellation-free" notion lives on the *source* tropical
circuit: even a monotone `max` compiles to a ReLU net that *internally* uses `scale (-1)`
inside `max p q = q + relu(p−q)`, so "the net has no subtraction" is the wrong notion; the
load-bearing property is that the computed *function* is monotone.)

* **`monotone_of_isMono` (THE CORE).** A cancellation-free circuit computes a **monotone**
  function (pointwise order on inputs): `IsMono e → Monotone (e.eval)`. By induction —
  `var`/`const` are monotone, and `add`, `max`, and nonneg `scale` preserve monotonicity.
* **`monotone_compile_of_isMono`.** Its compiled ReLU net computes the same (monotone)
  function — the cancellation-free *ReLU* fragment, via `compile_eval`.
* **The barrier, witnessed by `abs` (`abs_not_isMono`).** `|·|` is computed in the
  *general* fragment (`abs_in_general`, via `Trop.abs`) but is **not monotone**
  (`abs_not_monotone`), so **no cancellation-free circuit computes it**. The fragment is
  *proper*: cancellation buys exactly the non-monotone functions. This is why a monotone
  lower bound cannot, in general, be a ReLU lower bound.

## The IMPORTED WALL (named, NOT proved here)

* **The monotone lower bounds themselves** (Jerrum–Snir: explicit `(min,+)` functions
  needing super-polynomial monotone circuits) are imported — they are the *content* a
  transfer would carry; mathlib has no such bound.
* **Phase 2 (the reverse compilation), open:** whether an *arbitrary* small ReLU net that
  *happens* to compute a monotone function reduces to a small `IsMono` circuit. In general
  it does **not** — that gap *is* the monotone-vs-general circuit separation and the
  Razborov–Rudich natural-proofs barrier. So the transfer is sound on the fragment defined
  here (circuits built monotone), and the gap to "all nets computing monotone functions"
  is the wall this module locates rather than removes.

## References
* Jerrum, Snir, *Some exact complexity results for straight-line computations over
  semirings*, JACM 1982 (monotone `(min,+)` lower bounds).
* Razborov, Rudich, *Natural proofs*, 1997 (why monotone bounds do not extend).
-/
import Sundogcert.CircuitNet
import Mathlib.Order.Monotone.Basic

namespace Sundog.CancellationFree

open Sundog.CircuitNet

variable {n : ℕ}

/-- The **cancellation-free (monotone) fragment** of `Trop`: no negative scaling. Every
`scale` coefficient is required nonnegative; `var`, `const`, `add`, `max` are unrestricted.
These are the max-plus *polynomial* circuits — the monotone, no-subtraction sub-grammar. -/
def IsMono : Trop n → Prop
  | .var _     => True
  | .const _   => True
  | .add a b   => IsMono a ∧ IsMono b
  | .scale c a => 0 ≤ c ∧ IsMono a
  | .max a b   => IsMono a ∧ IsMono b

/-- **Cancellation-free circuits compute monotone functions (THE CORE).** Under the
pointwise order on inputs, a circuit in the `IsMono` fragment is monotone. Proof by
induction: `var`/`const` are monotone, and `add`, `max`, and nonnegative `scale` each
preserve monotonicity. -/
theorem monotone_of_isMono : ∀ {e : Trop n}, IsMono e → Monotone (fun x => e.eval x) := by
  intro e
  induction e with
  | var i => intro _ u v huv; exact huv i
  | const c => intro _; exact monotone_const
  | add a b iha ihb => intro h u v huv; exact add_le_add (iha h.1 huv) (ihb h.2 huv)
  | scale c a ih => intro h u v huv; exact mul_le_mul_of_nonneg_left (ih h.2 huv) h.1
  | max a b iha ihb => intro h u v huv; exact max_le_max (iha h.1 huv) (ihb h.2 huv)

/-- The compiled ReLU network of a cancellation-free circuit computes the same monotone
function — so the cancellation-free *ReLU* fragment is monotone too. -/
theorem monotone_compile_of_isMono {e : Trop n} (h : IsMono e) :
    Monotone (fun x => (compile e).eval x) := by
  have hfun : (fun x => (compile e).eval x) = (fun x => e.eval x) :=
    funext (fun x => compile_eval e x)
  rw [hfun]
  exact monotone_of_isMono h

/-! ## The cancellation barrier: `abs` separates the fragments -/

/-- Absolute value is **not** monotone: `-1 ≤ 0` but `|-1| = 1 > 0 = |0|`. -/
theorem abs_not_monotone : ¬ Monotone (fun x : Fin 1 → ℝ => |x 0|) := by
  intro h
  have hle : (fun _ : Fin 1 => (-1 : ℝ)) ≤ (fun _ : Fin 1 => (0 : ℝ)) := by
    intro i; norm_num
  have hcon := h hle
  norm_num at hcon

/-- Absolute value **is** in the general (tropical-rational) fragment: the `Trop.abs`
gadget `max a (-a)` computes `|·|`. -/
theorem abs_in_general :
    (fun x : Fin 1 → ℝ => (Trop.abs (Trop.var 0)).eval x) = (fun x => |x 0|) := by
  funext x
  simp only [abs_eval, Trop.eval_var]

/-- **The cancellation barrier (the proper-fragment separation).** No cancellation-free
circuit computes `|·|`: if `e` is in the `IsMono` fragment, its function is monotone, but
`|·|` is not. So the cancellation-free fragment is *strictly* inside the general one —
cancellation is exactly what buys the non-monotone functions, and that is why a monotone
circuit lower bound is not automatically a ReLU lower bound. -/
theorem abs_not_isMono (e : Trop 1) (h : IsMono e) :
    (fun x => e.eval x) ≠ (fun x : Fin 1 → ℝ => |x 0|) := by
  intro heq
  apply abs_not_monotone
  rw [← heq]
  exact monotone_of_isMono h

/-! ## Phase 2 — the reverse compilation and the imported-bound transfer -/

/-- The number of `max` (nonlinear) gates — the resource a monotone `(min,+)`/`(max,+)`
circuit lower bound charges for (`+`, scaling and constants are "free" in that model). -/
def maxCount : Trop n → ℕ
  | .var _     => 0
  | .const _   => 0
  | .add a b   => maxCount a + maxCount b
  | .scale _ a => maxCount a
  | .max a b   => maxCount a + maxCount b + 1

/-- **The source max-gate count lower-bounds the compiled DAG's gate count.** Each `max`
node compiles (via `appendMax`) to four ReLU gates, and no node ever removes gates, so the
compiled DAG has at least `maxCount e` gates. The mirror (a *lower* bound) of
`compileToDag_gate_count`. -/
theorem compileToDag_maxCount_ge :
    ∀ {m : ℕ} (p : CircuitNet.RProg n m) (e : Trop n),
      m + maxCount e ≤ (compileToDag p e).m' := by
  intro m p e
  induction e generalizing m p with
  | var i => simp [compileToDag, maxCount]
  | const c => simp [compileToDag, maxCount]
  | scale c a ih =>
      have h := ih p
      simp only [compileToDag, maxCount]
      omega
  | add a b iha ihb =>
      have h1 := iha p
      have h2 := ihb (compileToDag p a).prog
      simp only [compileToDag, maxCount]
      omega
  | max a b iha ihb =>
      have h1 := iha p
      have h2 := ihb (compileToDag p a).prog
      simp only [compileToDag, maxCount]
      omega

/-- The compiled ReLU DAG of `e` (built from the empty program) has at least `maxCount e`
gates. `(compileToDag RProg.nil e).m'` *is* that DAG's gate count
(`= (compileToDag RProg.nil e).prog.gateCount`). -/
theorem maxCount_le_compiled (e : Trop n) :
    maxCount e ≤ (compileToDag CircuitNet.RProg.nil e).m' := by
  simpa using compileToDag_maxCount_ge CircuitNet.RProg.nil e

/-- **The imported-bound transfer (THE PHASE-2 CORE).** Take a monotone max-gate lower
bound for a function `f` as an explicit hypothesis `hLB` — this is the **imported**
Jerrum–Snir-type content (mathlib has no such bound) — namely that *every* cancellation-
free (`IsMono`) circuit computing `f` uses at least `B` max-gates. Then *every*
cancellation-free ReLU net for `f` (the compilation of such a circuit) uses at least `B`
gates. The proof is just the size bridge `maxCount ≤ compiled gate count`; the genuinely
hard part (`hLB`) is named, not proved. -/
theorem monotone_transfer (f : (Fin n → ℝ) → ℝ) (B : ℕ)
    (hLB : ∀ e : Trop n, IsMono e → (fun x => e.eval x) = f → B ≤ maxCount e) :
    ∀ e : Trop n, IsMono e → (fun x => e.eval x) = f →
      B ≤ (compileToDag CircuitNet.RProg.nil e).m' :=
  fun e hmono heq => le_trans (hLB e hmono heq) (maxCount_le_compiled e)

/-- **The reverse compilation: every ReLU net is a tropical circuit.** `relu a` is the
tropical `max a 0`; the affine gates map directly. Completes the `Net ≅ Trop`
(tropical-*rational*) equivalence — the converse of `CircuitNet.compile`. -/
def decompile : Net n → Trop n
  | .var i     => .var i
  | .const c   => .const c
  | .add a b   => .add (decompile a) (decompile b)
  | .scale c a => .scale c (decompile a)
  | .relu a    => .max (decompile a) (.const 0)

/-- The reverse compilation is **exact**: `decompile g` computes the same function as `g`.
(`relu a = max a 0` is the only nontrivial case.) -/
theorem decompile_eval (g : Net n) (x : Fin n → ℝ) :
    (decompile g).eval x = g.eval x := by
  induction g with
  | var i => rfl
  | const c => rfl
  | add a b iha ihb => simp [decompile, Net.eval_add, iha, ihb]
  | scale c a ih => simp [decompile, Net.eval_scale, ih]
  | relu a ih => simp [decompile, Net.eval_relu, ih]

/-!
### The wall (named, not removed)

`decompile` sends a *general* ReLU net to a *general* `Trop` circuit — which need **not**
be `IsMono` (a net using cancellation decompiles to a circuit using `scale (-1)`). So
`monotone_transfer` bounds the **cancellation-free fragment** (the compile-image of
`IsMono` circuits), and the gap to *all* ReLU nets computing a monotone function is exactly
the monotone-vs-general circuit separation / the Razborov–Rudich natural-proofs barrier —
imported, not crossed here. The two provable halves (`monotone_transfer`, `decompile_eval`)
sandwich that wall precisely.
-/

end Sundog.CancellationFree

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.CancellationFree.monotone_of_isMono
#print axioms Sundog.CancellationFree.abs_not_isMono
#print axioms Sundog.CancellationFree.monotone_transfer
#print axioms Sundog.CancellationFree.decompile_eval
