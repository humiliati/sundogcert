/-
# Folding needs cancellation: the depth-separation witness is not cancellation-free (N-1)

The Lean realization of slate-2 hook **N-1** (sharp form). It fuses two landed cores:

* **C-B1** (`CancellationFree.monotone_of_isMono`): a cancellation-free (`IsMono`) circuit
  computes a **monotone** function.
* **C-D1** (`DepthSeparation.tent_iterate_dyadic`): the depth-`O(d)` tent circuit `T^[d]`
  **folds** — its dyadic samples alternate `0,1,0,1,…`, giving `2^d` linear pieces.

A monotone function **cannot fold**: it cannot rise to `1` at one input and fall back to `0`
at a larger input. Therefore **no cancellation-free circuit computes the `d`-fold tent for
`d ≥ 1`** — the exponential expressivity that depth buys (C-D1's `2^d` pieces) is
*cancellation-essential*. This is the "depth = computation **only with cancellation**" core:
the same witness that achieves `2^d` regions is unrealizable in the cancellation-free fragment.

## What is PROVED here

* **`isMono_no_fold`** — a cancellation-free circuit's function cannot take value `1` at `b`
  and `0` at `c ≥ b` (the down-stroke of a fold); immediate from `monotone_of_isMono`.
* **`isMono_not_iterTentFun`** — for `d ≥ 1`, no `IsMono` circuit computes the function
  `T^[d]`. Witness: `T^[d](1/2^d) = 1` (odd sample) and `T^[d](2/2^d) = 0` (even sample),
  with `1/2^d ≤ 2/2^d`.
* **`isMono_not_iterTent`** — the same, stated against the circuit `iterTent d` directly.

## The named PHASE-2 target (not proved here)

The matching **positive** half — that *every* `IsMono` depth-`d` width-`w` circuit has only
`O(d·w)` linear regions (monotone composition makes pieces *add*, not multiply) — needs a
piece-count function and a composition-additivity lemma over `RegionCount`. Named, not built.
-/
import Sundogcert.CancellationFree
import Sundogcert.DepthSeparation
import Sundogcert.RegionCount
import Mathlib.Order.UpperLower.Basic

namespace Sundog.FoldCancellation

open Sundog.CircuitNet Sundog.CancellationFree Sundog.DepthSeparation Sundog.RegionCount

variable {e : Trop 1}

/-- **Monotone circuits cannot fold.** If a cancellation-free circuit's function is `1` at
`b` and `0` at some `c ≥ b`, monotonicity is contradicted (`1 ≤ 0`). -/
theorem isMono_no_fold (hmono : IsMono e) {b c : ℝ} (hbc : b ≤ c)
    (hb : e.eval (fun _ => b) = 1) (hc : e.eval (fun _ => c) = 0) : False := by
  have hle : (fun _ : Fin 1 => b) ≤ (fun _ : Fin 1 => c) := by intro _; exact hbc
  have hmono' : e.eval (fun _ => b) ≤ e.eval (fun _ => c) := monotone_of_isMono hmono hle
  rw [hb, hc] at hmono'
  linarith

/-- **The depth-separation witness is cancellation-essential (N-1).** For `d ≥ 1` no
cancellation-free circuit computes the `d`-fold tent function `T^[d]`. The tent folds —
`T^[d](1/2^d) = 1` (odd) but `T^[d](2/2^d) = 0` (even), with `1/2^d ≤ 2/2^d` — and
`isMono_no_fold` forbids exactly that. So the `2^d` linear pieces of C-D1 require cancellation. -/
theorem isMono_not_iterTentFun (d : ℕ) (hd : 1 ≤ d) (hmono : IsMono e)
    (heq : ∀ x : Fin 1 → ℝ, e.eval x = T^[d] (x 0)) : False := by
  have h1 : (1 : ℕ) ≤ 2 ^ d := Nat.one_le_pow _ _ (by norm_num)
  have h2 : (2 : ℕ) ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hb : e.eval (fun _ => ((1 : ℕ) : ℝ) / 2 ^ d) = 1 := by
    have ht := tent_iterate_dyadic d 1 h1
    rw [if_pos (by decide : Odd 1)] at ht
    rw [heq]; exact ht
  have hc : e.eval (fun _ => ((2 : ℕ) : ℝ) / 2 ^ d) = 0 := by
    have ht := tent_iterate_dyadic d 2 h2
    rw [if_neg (by decide : ¬ Odd 2)] at ht
    rw [heq]; exact ht
  have hbc : ((1 : ℕ) : ℝ) / 2 ^ d ≤ ((2 : ℕ) : ℝ) / 2 ^ d := by
    gcongr; norm_num
  exact isMono_no_fold hmono hbc hb hc

/-- The same, stated against the depth-`O(d)` tent **circuit** `iterTent d`: for `d ≥ 1`, no
cancellation-free circuit computes what `iterTent d` computes. -/
theorem isMono_not_iterTent (d : ℕ) (hd : 1 ≤ d) (hmono : IsMono e)
    (heq : ∀ x : Fin 1 → ℝ, e.eval x = (iterTent d).eval x) : False := by
  refine isMono_not_iterTentFun d hd hmono ?_
  intro x; rw [heq x, iterTent_eval]

/-! ## The positive half (qualitative core): monotone circuits never fold, at any level

The negative half above forbids the *specific* fold of `T^[d]`. The positive half says a
cancellation-free circuit cannot oscillate *at all*: its 1-D realization is monotone, so
every super-level set `{x | c ≤ f x}` is an **upper set** — once `f` reaches level `c` it
stays `≥ c`, i.e. exactly one rising crossing per level, no fold-back anywhere. This is
`isMono_no_fold` lifted from one witnessed fold to every level, and it is the structural
reason monotone region counts stay small (pieces *add* under composition, they cannot
*multiply*). The matching *quantitative* `O(d·w)` region-count bound needs a region-count
definition over `RegionCount` and is the named remaining target. -/

/-- The 1-D realization of a cancellation-free circuit is **monotone**. -/
theorem isMono_realize1_monotone (hmono : IsMono e) : Monotone (realize1 e) := by
  intro s t hst
  exact monotone_of_isMono hmono (fun _ => hst)

/-- **No fold at any level (the positive-half core).** For a cancellation-free circuit,
every super-level set is an **upper set**: monotonicity means once `f` reaches `c` it never
returns below it — no oscillation, exactly the opposite of folding. -/
theorem isMono_superlevel_isUpperSet (hmono : IsMono e) (c : ℝ) :
    IsUpperSet {x : ℝ | c ≤ realize1 e x} := by
  intro a b hab ha
  exact le_trans ha (isMono_realize1_monotone hmono hab)

/-- **Contrast: the tent folds.** The depth-2 tent's super-level set `{x | 1/2 ≤ T^[2] x}`
is **not** an upper set — `1/4` is in it (`T^[2](1/4) = 1`) and `1/4 ≤ 1/2`, yet `1/2` is
not (`T^[2](1/2) = 0`). So no cancellation-free circuit has this level structure; folding is
exactly the upper-set failure that `isMono_superlevel_isUpperSet` rules out. -/
theorem tent_superlevel_not_isUpperSet :
    ¬ IsUpperSet {x : ℝ | (1 : ℝ) / 2 ≤ (T^[2]) x} := by
  intro hUp
  have ha : ((1 : ℕ) : ℝ) / 2 ^ 2 ∈ {x : ℝ | (1 : ℝ) / 2 ≤ (T^[2]) x} := by
    change (1 : ℝ) / 2 ≤ (T^[2]) (((1 : ℕ) : ℝ) / 2 ^ 2)
    rw [tent_iterate_dyadic 2 1 (by norm_num), if_pos (by decide : Odd 1)]; norm_num
  have hab : ((1 : ℕ) : ℝ) / 2 ^ 2 ≤ ((2 : ℕ) : ℝ) / 2 ^ 2 := by norm_num
  have hb := hUp hab ha
  have hcon : (1 : ℝ) / 2 ≤ (T^[2]) (((2 : ℕ) : ℝ) / 2 ^ 2) := hb
  rw [tent_iterate_dyadic 2 2 (by norm_num), if_neg (by decide : ¬ Odd 2)] at hcon
  norm_num at hcon

end Sundog.FoldCancellation

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.FoldCancellation.isMono_no_fold
#print axioms Sundog.FoldCancellation.isMono_not_iterTentFun
#print axioms Sundog.FoldCancellation.isMono_not_iterTent
