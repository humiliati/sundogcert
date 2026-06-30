/-
# Polylog *gates* for the sawtooth: the shared-DAG follow-on (Slate-4 U-3 continuation)

`SawtoothApprox` builds the `x²` approximant `R m` as a *tree* (`Rcirc`, by `m`-fold `subst0`
composition), whose node count is **exponential** in `m` — so `ApproxCost`'s tree-keyed cost bound
is vacuous there (`SHARED_SIZE_NOT_CAPTURED`). The real gate count is small only via DAG *sharing*.

This module supplies the **value core** that makes the sharing visible: unrolling the recursion
gives the closed form

    R m x = x − Σ_{k=1}^{m} T^[k](x) / 4^k,

a *flat linear combination of `m` iterated tents* `T^[k]`. The iterated tents form a **chain**
(`T^[k+1] = T ∘ T^[k]`), so a DAG can compute all of `T^[1], …, T^[m]` reusing each previous
wire — `O(m)` gates — and the accumulation is `O(m)` more. The exponential blow-up was pure tree
duplication of the shared chain. (`Ssum_eq_R` is the closed form; `R_eq_iteratedTents` restates it
on `R` directly. The explicit `O(m)`-gate `RProg` is built on top in `SawtoothDag`.)
-/
import Sundogcert.SawtoothApprox

namespace Sundog.SawtoothShared

open Sundog.CircuitNet Sundog.DepthSeparation Sundog.SawtoothApprox

/-- The flat partial sum: `x` minus the weighted iterated tents `T^[k]/4^k`, `k = 1 … m`. -/
noncomputable def Ssum (m : ℕ) (x : ℝ) : ℝ :=
  x - ∑ k ∈ Finset.range m, (T^[k + 1] x) / 4 ^ (k + 1)

/-- **The closed form.** The Yarotsky self-similar approximant equals the flat linear combination
of iterated tents: `R m x = x − Σ_{k=1}^m T^[k](x)/4^k`. The structural fact behind the polylog
gate count — `R m` is a sum of `m` chain-shared tents, not a depth-`m` self-composition. -/
theorem Ssum_eq_R (m : ℕ) (x : ℝ) : Ssum m x = R m x := by
  induction m generalizing x with
  | zero => simp [Ssum, R]
  | succ m ih =>
    rw [R, ← ih (T x)]
    simp only [Ssum]
    rw [Finset.sum_range_succ']
    -- reindex the tail sum from `Ssum m (T x)` to match: T^[k+1](T x) = T^[k+2] x, weight ×1/4
    have hshift : (∑ k ∈ Finset.range m, (T^[k + 1] (T x)) / 4 ^ (k + 1)) / 4
        = ∑ k ∈ Finset.range m, (T^[k + 1 + 1] x) / 4 ^ (k + 1 + 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Function.iterate_succ_apply T (k + 1) x]
      rw [pow_succ]
      ring
    have h0 : T^[0 + 1] x = T x := by simp
    rw [h0]
    -- both sides reduce to `x - T x/4 - (tail)`
    have hcancel : T x / 4 ^ (0 + 1) = T x / 4 := by norm_num
    rw [hcancel, ← hshift]
    ring

/-- **The closed form, on `R` directly.** `R m x = x − Σ_{k=1}^m T^[k](x)/4^k`: the approximant is
a flat linear combination of `m` iterated tents (a chain), not a depth-`m` self-composition — the
structural reason an `O(m)`-gate shared DAG computes it. -/
theorem R_eq_iteratedTents (m : ℕ) (x : ℝ) :
    R m x = x - ∑ k ∈ Finset.range m, (T^[k + 1] x) / 4 ^ (k + 1) :=
  (Ssum_eq_R m x).symm

end Sundog.SawtoothShared
