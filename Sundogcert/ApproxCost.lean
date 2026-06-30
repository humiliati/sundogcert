/-
# U-3 — Unified cost: the analytic gate's certified op-count (Slate-4)

The lane already has a straight-line **cost ledger** (`StraightLineCost`): a compiled tropical
tree's sharing-aware ReLU-DAG gate count is `≤ 4 · nodeCount` of the tree
(`compileToDag_cost_le`). This module wires the **approximation** side into that ledger: the
analytic gate `x²` (`AnalyticGate.sqNet`,
the `n`-piece secant interpolant) gets a **certified op-count linear in the piece count** —
`≤ 20n + 4` — and, combined with the proved error bound, a single "certified approximation"
statement carrying *both* the L∞ error and the op-count.

* **`linesTrop_nodeCount`** — the upper-envelope (`max`-of-lines) circuit over `L` lines has
  `≤ 5·|L| + 1` nodes (each line is a 4-node affine gate; each `max` fold adds 5). Reusable for
  any convex-interpolant net (`AnalyticGate`, `ExactRepr.convexCPL_realizable`).
* **`analyticGate_dag_cost`** — the analytic gate's sharing-aware DAG has cost `≤ 20n + 4`.
* **`analyticGate_cost_eps`** — for any `ε > 0`, a piece count `n` whose DAG approximates `x²`
  to error `≤ ε` *and* has cost `≤ 20n + 4`.

**Honest scope — the tree-vs-DAG fence (why this is the *flat* family only).** The cost theorem
keys on the **tree** `nodeCount`. The flat interpolant nets (`linesTrop`, a `max` over `n` pieces)
have node count linear in `n`, so the bound is tight and the op-count is genuinely `O(n)`. The
**deep** approximants — the Telgarsky sawtooth `SawtoothApprox.Rcirc` and everything built on it
(`MultiplyGate`/`MonomialEval`/`PolyEval`/`UniversalApprox`) — are built by `subst0`
*composition*, which duplicates the tent into every variable occurrence: their *tree* node count
is **exponential**
in the fold depth `m` (linear depth, exponential size — the lane's own depth-separation
phenomenon). For those, `compileToDag_cost_le`'s `4·nodeCount` bound is **vacuous**; their real
(small) gate count is recovered only by DAG *sharing*, which this tree-keyed bound does not
quantify. Capturing that —
a sharing-aware size bound for the composed approximants — is the named open piece
(`SHARED_SIZE_NOT_CAPTURED`), not part of this warm-up. So U-3 lands the cost ledger for the flat
construction and honestly fences the deep one.
-/
import Sundogcert.AnalyticGate
import Sundogcert.StraightLineCost

namespace Sundog.ApproxCost

open Sundog.CircuitNet Sundog.RegionCount Sundog.ExactRepr
open Sundog.AnalyticGate Sundog.StraightLineCost

/-! ### Node count of the flat (max-of-lines) interpolant -/

/-- An affine gate `a·x + b` is a 4-node tree (`add (scale (var)) (const)`). -/
@[simp] theorem affineCirc_nodeCount (a b : ℝ) : (affineCirc a b).nodeCount = 4 := rfl

/-- Each `max`-with-affine fold step adds exactly 5 nodes. -/
theorem foldl_lines_nodeCount (rest : List (ℝ × ℝ)) (init : Trop 1) :
    (rest.foldl (fun acc q => Trop.max acc (affineCirc q.1 q.2)) init).nodeCount
      = init.nodeCount + 5 * rest.length := by
  induction rest generalizing init with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih]
    simp only [Trop.nodeCount, affineCirc_nodeCount, List.length_cons]
    ring

/-- **Linear node count.** The upper-envelope circuit over `L` lines has `≤ 5·|L| + 1` nodes. -/
theorem linesTrop_nodeCount (L : List (ℝ × ℝ)) :
    (linesTrop L).nodeCount ≤ 5 * L.length + 1 := by
  cases L with
  | nil => simp [linesTrop, Trop.nodeCount]
  | cons pr rest =>
    simp only [linesTrop, foldl_lines_nodeCount, affineCirc_nodeCount, List.length_cons]
    omega

/-! ### The analytic gate's certified op-count -/

/-- **The analytic gate's certified op-count.** The sharing-aware ReLU DAG compiled from the
`n`-piece analytic gate `x²` has straight-line cost (gate count) `≤ 20n + 4` — *linear* in the
piece count, via `compileToDag_cost_le` over the linear `linesTrop` node count. -/
theorem analyticGate_dag_cost (n : ℕ) :
    costOf (compileToDag (RProg.nil) (linesTrop (secantList n))).prog ≤ 20 * n + 4 := by
  have hnil : costOf (RProg.nil : RProg 1 0) = 0 := rfl
  have hbound := compileToDag_cost_le (RProg.nil : RProg 1 0) (linesTrop (secantList n))
  have hlen : (secantList n).length = n := by simp [secantList]
  have hnode := linesTrop_nodeCount (secantList n)
  rw [hnil] at hbound
  rw [hlen] at hnode
  omega

/-- **Certified-cost analytic gate.** For every `ε > 0` there is a piece count `n` whose
sharing-aware ReLU DAG approximates `x²` on `[0,1]` to error `≤ ε` **and** has straight-line
cost `≤ 20n + 4` — one statement carrying both the proved L∞ error and the certified op-count. -/
theorem analyticGate_cost_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |x ^ 2 - realize1N (sqNet n) x| ≤ ε) ∧
      costOf (compileToDag (RProg.nil) (linesTrop (secantList n))).prog ≤ 20 * n + 4 := by
  obtain ⟨m, hm⟩ := exists_nat_ge (1 / ε)
  refine ⟨m + 1, fun x hx => le_trans (sqNet_approx (m + 1) (Nat.succ_pos m) x hx) ?_,
    analyticGate_dag_cost (m + 1)⟩
  have hn' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  rw [div_le_iff₀ (by positivity)]
  have hmn : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hn1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have h1e : 1 / ε ≤ 4 * ((m + 1 : ℕ) : ℝ) ^ 2 := by nlinarith [hm, hmn, hn1]
  calc (1 : ℝ) = ε * (1 / ε) := by field_simp
    _ ≤ ε * (4 * ((m + 1 : ℕ) : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1e (le_of_lt hε)

end Sundog.ApproxCost
