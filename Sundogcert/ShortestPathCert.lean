/-
# A shortest-path optimality certificate — the find/check ledger's optimization instance

Another worked example of the discipline in `Sundogcert.Certificate`: **machine-check the
cheap-CHECK core, name the hard-FIND wall.** The syndrome certificate is finite-field
algebra; the sorting certificate is combinatorics; `CircuitNet` is circuit complexity;
this is the **combinatorial-optimization** sibling, and the *second* concrete instance of
the shared `StraightLineCost` op-count ledger (after the syndrome verifier).

It is the Lean realization of slate hook **C-C1**: a shortest-path tree / feasible
potential is a cheap-to-verify witness, while finding it is the full search.

## What is PROVED here (Phase 1 — the dual certificate)

A weighted digraph on `Fin n` is an edge list `edges : List (Fin n × Fin n × ℝ)` with a
`source`. `Reaches edges s v d` means *there is a walk from `s` to `v` of total weight
`d`*. A **feasible potential** `dist : Fin n → ℝ` satisfies `dist source = 0` and the
relaxation inequality `dist v ≤ dist u + c` at **every** edge `(u,v,c)`.

* **`feasible_le_walk` (THE CORE).** A feasible potential **lower-bounds every walk
  weight**: if `dist` is feasible and `Reaches edges s v d`, then `dist v ≤ d`. So a
  feasible `dist` certifies that *no path beats it* — the LP-dual / Bellman–Ford
  optimality witness, the "nothing is shorter" half. Proof: induction on the walk; each
  edge contributes its relaxation inequality, telescoping along the walk.
* **`verifyCost` is linear (`O(E)`).** Checking feasibility costs `2·|edges| + 1`
  operations (one add + one compare per edge, plus the source check) — a faithful
  structural op-count against a transparent cost model, exactly the shape of
  `CheckCost.verifyCost`.
* **Same ledger as the certificate.** A `HasStraightLineCost (SPInstance n)` instance
  routes that cost through the shared `costOf`, so the construction-cost / verification-
  cost ledger of `StraightLineCost` now has its **optimization** instance alongside the
  ReLU-DAG gate count and the syndrome verifier.

## The HARD-FIND wall (named, NOT proved here)

* **Finding** the feasible potential / shortest-path tree is the actual search
  (Bellman–Ford `O(VE)`, Dijkstra `O(E log V)`); this module only *checks* a supplied
  `dist` cheaply. The find ≫ check gap is the point, and only the *check* side is here.
* The **cost model** is a trust-surface item, as in `CheckCost`: a reviewer checks that
  `verifyCost` faithfully counts the operations of the feasibility check.

## Phase 2 — the exact optimality certificate (now PROVED)

The matching upper bound is `cert_isLeast`: a `Feasible` potential together with a
`TightTree` (each non-source vertex tight on an incoming edge, with a `rank` decreasing to
the source) makes `dist v` the **least** achievable walk weight — so `dist` *is* the true
shortest-path distance, exactly, not merely a lower bound. `tree_achieves` supplies the
achieving walk (induction on the `rank` bound); the cheap `O(E + V)` check (feasibility +
the tree) certifies global optimality. Still imported: *finding* the tree (the search).

## References
* Bellman–Ford optimality / feasible potentials; LP duality for shortest paths
  (Schrijver, *Combinatorial Optimization*, §8). The dual certificate of a shortest path
  is a feasible potential — exactly `Feasible` below.
-/
import Sundogcert.StraightLineCost
import Mathlib.Order.Bounds.Basic

namespace Sundog.ShortestPathCert

variable {n : ℕ}

/-- A weighted directed edge `(u, v, c)`: from `u` to `v` with real weight `c`. -/
abbrev Edge (n : ℕ) := Fin n × Fin n × ℝ

/-- A shortest-path instance: a weighted digraph (edge list) with a source vertex. -/
structure SPInstance (n : ℕ) where
  edges : List (Edge n)
  source : Fin n

/-- `Reaches edges s v d` — there is a walk from `s` to `v` along `edges` of total
weight `d`. The empty walk has weight `0`; each step appends an edge and adds its weight. -/
inductive Reaches (edges : List (Edge n)) (s : Fin n) : Fin n → ℝ → Prop where
  | refl : Reaches edges s s 0
  | step {u v c d} : Reaches edges s u d → (u, v, c) ∈ edges → Reaches edges s v (d + c)

/-- A **feasible potential**: the source has potential `0`, and every edge satisfies the
relaxation inequality `dist v ≤ dist u + c`. This is the checkable core of the
certificate. -/
def Feasible (edges : List (Edge n)) (s : Fin n) (dist : Fin n → ℝ) : Prop :=
  dist s = 0 ∧ ∀ e ∈ edges, dist e.2.1 ≤ dist e.1 + e.2.2

/-- **The dual certificate (THE CORE).** A feasible potential lower-bounds the weight of
every walk: no path from the source to `v` is shorter than `dist v`. This is what makes
`dist` a sound optimality certificate — the "nothing is shorter" half, checked in `O(E)`.

Proof: induction on the walk. The empty walk has weight `0 = dist s`. Each appended edge
`(u,v,c)` contributes `dist v ≤ dist u + c`, and the inductive hypothesis `dist u ≤ d`
telescopes it to `dist v ≤ d + c`. -/
theorem feasible_le_walk {edges : List (Edge n)} {s : Fin n} {dist : Fin n → ℝ}
    (hf : Feasible edges s dist) {v : Fin n} {d : ℝ} (h : Reaches edges s v d) :
    dist v ≤ d := by
  induction h with
  | refl => exact le_of_eq hf.1
  | step hr hedge ih =>
      have hrelax := hf.2 _ hedge
      linarith

/-- The certified lower bound, packaged: under a feasible potential, `dist v` is a lower
bound on *every* achievable walk weight to `v`. -/
theorem cert_is_lower_bound {edges : List (Edge n)} {s : Fin n} {dist : Fin n → ℝ}
    (hf : Feasible edges s dist) (v : Fin n) :
    ∀ {d : ℝ}, Reaches edges s v d → dist v ≤ d :=
  fun h => feasible_le_walk hf h

/-! ## Phase 2 — the matching upper bound: an exact optimality certificate -/

/-- A **tight, well-founded shortest-path tree** witness: every non-source vertex `v` has
an incoming edge `(u,v,c)` on which its potential is *tight* (`dist v = dist u + c`), with a
`rank` that strictly decreases toward the source (so following the tree terminates). This
is the extra data — beyond `Feasible` — that upgrades the lower-bound certificate to an
exact one. (The verifier reads an explicit parent/rank; the predicate existentializes the
parent edge.) -/
def TightTree (edges : List (Edge n)) (s : Fin n) (dist : Fin n → ℝ) (rank : Fin n → ℕ) :
    Prop :=
  ∀ v, v ≠ s → ∃ u c, (u, v, c) ∈ edges ∧ dist v = dist u + c ∧ rank u < rank v

/-- **Achievability.** Under a tight well-founded tree, the source actually reaches each
`v` by a walk of weight exactly `dist v` — the matching upper bound. Proof: induction on a
`rank` bound; the source is the base case (`dist s = 0`, an empty walk), and each tight
tree edge appends to the strictly-lower-rank parent's walk. -/
theorem tree_achieves {edges : List (Edge n)} {s : Fin n} {dist : Fin n → ℝ}
    {rank : Fin n → ℕ} (hs : dist s = 0) (ht : TightTree edges s dist rank) :
    ∀ v, Reaches edges s v (dist v) := by
  have key : ∀ k, ∀ w : Fin n, rank w ≤ k → Reaches edges s w (dist w) := by
    intro k
    induction k with
    | zero =>
        intro w hw
        by_cases hws : w = s
        · subst hws; rw [hs]; exact Reaches.refl
        · exfalso
          obtain ⟨u, c, _, _, hrank⟩ := ht w hws
          omega
    | succ k ih =>
        intro w hw
        by_cases hws : w = s
        · subst hws; rw [hs]; exact Reaches.refl
        · obtain ⟨u, c, hedge, htight, hrank⟩ := ht w hws
          rw [htight]
          exact Reaches.step (ih u (by omega)) hedge
  exact fun v => key (rank v) v (le_refl _)

/-- **The exact optimality certificate (THE PHASE-2 CORE).** A feasible potential together
with a tight, well-founded tree pins `dist v` to the **least** achievable walk weight from
the source to `v` — so `dist` *is* the true shortest-path distance, exactly, not merely a
lower bound. The cheap check (feasibility `O(E)` + the tree `O(V)`) certifies global
optimality: achievability gives `dist v ∈` the walk-weight set, `feasible_le_walk` makes it
a lower bound, and `IsLeast` packages the two into "least element". -/
theorem cert_isLeast {edges : List (Edge n)} {s : Fin n} {dist : Fin n → ℝ}
    {rank : Fin n → ℕ} (hf : Feasible edges s dist) (ht : TightTree edges s dist rank)
    (v : Fin n) :
    IsLeast {d : ℝ | Reaches edges s v d} (dist v) :=
  ⟨tree_achieves hf.1 ht v, fun _ hd => feasible_le_walk hf hd⟩

/-! ## The verification cost — linear in the number of edges -/

/-- **Per-instance verification cost** of the feasibility check: one add + one compare per
edge (`2·|edges|`), plus the source-potential check. A faithful structural operation
count against a transparent cost model. -/
def verifyCost (I : SPInstance n) : ℕ := 2 * I.edges.length + 1

/-- **Checking is linear in `|E|`.** The feasibility certificate is verified in
`O(|edges|)` operations — the cheap-CHECK half of "cheaper to check than to find". -/
theorem verifyCost_le (I : SPInstance n) : verifyCost I ≤ 2 * I.edges.length + 1 :=
  le_refl _

/-- The shortest-path verifier plugs into the shared straight-line cost ledger: its
`costOf` is the feasibility-check operation count. -/
instance spHasStraightLineCost : StraightLineCost.HasStraightLineCost (SPInstance n) where
  program I := StraightLineCost.StraightLineProgram.ofCost (verifyCost I)

@[simp] theorem sp_cost_eq_verifyCost (I : SPInstance n) :
    StraightLineCost.costOf I = verifyCost I := rfl

/-- **The find/check ledger's optimization instance.** The same `costOf` interface that
reads as ReLU-DAG gate count (construction) and syndrome verifier op-count now also reads
as the shortest-path feasibility-check cost, linear in `|edges|`. -/
theorem sp_verifier_cost_le (I : SPInstance n) :
    StraightLineCost.costOf I ≤ 2 * I.edges.length + 1 := by
  simpa using verifyCost_le I

end Sundog.ShortestPathCert

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.ShortestPathCert.feasible_le_walk
#print axioms Sundog.ShortestPathCert.cert_isLeast
#print axioms Sundog.ShortestPathCert.sp_verifier_cost_le
