/-
# Max-flow / min-cut — a cut certifies a flow's optimality (N-3, find/check ledger)

The combinatorial-optimization sibling of `ShortestPathCert`, and the two-sided LP-duality
instance of `Certifies.weakDuality_tight`. A **cut** is a cheap-to-check *dual* witness that
upper-bounds *every* flow's value (`weak_duality`); so a **tight pair** — a flow and a cut of
equal value — certifies that the flow is **maximum** and the cut is **minimum** at once
(`maxflow_mincut`). Only the CHECK is here; *finding* the max flow (the augmenting-path /
push-relabel search) is the imported wall.

## What is PROVED here

* **`weak_duality`** — `value F ≤ capCut cap S` for every flow `F` and every `s`–`t` cut `S`.
  Proof: conservation collapses `∑_{u∈S} ∑_w f u w` to the source's net out-flow (`value F`);
  the within-`S` double sum cancels by skew-symmetry; the across-cut flow is `≤` the across-cut
  capacity edge by edge.
* **`maxflow_mincut`** — a tight flow/cut pair pins `value F = IsGreatest` of all flow values
  and `capCut cap S = IsLeast` of all cut capacities (via `Certifies.weakDuality_tight`).
* **`cutcert_cost_le`** — checking the cut bound costs `|S|·|Sᶜ| + 1` operations, routed through
  the shared `Certifies`/`StraightLineCost` ledger. Another find/check ledger instance.

## The HARD-FIND wall (named, NOT proved here)
* *Finding* the max flow / min cut is the search (Ford–Fulkerson / Dinic / push-relabel); this
  module only *checks* a supplied tight pair cheaply. The find ≫ check gap is the point.
-/
import Sundogcert.Certifies
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Sundog.MaxFlowMinCut

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **flow** in a capacitated network with source `s` and sink `t`: skew-symmetric,
capacity-bounded, and conserved at every internal vertex. -/
structure Flow (cap : V → V → ℝ) (s t : V) where
  f : V → V → ℝ
  skew : ∀ u v, f u v = - f v u
  cap_le : ∀ u v, f u v ≤ cap u v
  conserve : ∀ v, v ≠ s → v ≠ t → ∑ w, f v w = 0

/-- The **value** of a flow: net flow out of the source. -/
def value {cap : V → V → ℝ} {s t : V} (F : Flow cap s t) : ℝ := ∑ w, F.f s w

/-- The **capacity of an `s`–`t` cut** `S`: total capacity of the edges leaving `S`. -/
def capCut (cap : V → V → ℝ) (S : Finset V) : ℝ := ∑ u ∈ S, ∑ v ∈ Sᶜ, cap u v

/-- **Weak duality (the cheap dual bound).** Every flow's value is at most every cut's
capacity — so a cut certifies an upper bound on the maximum flow, checked by summing the
cut's edge capacities. -/
theorem weak_duality {cap : V → V → ℝ} {s t : V} (F : Flow cap s t)
    {S : Finset V} (hsS : s ∈ S) (htS : t ∉ S) :
    value F ≤ capCut cap S := by
  -- conservation collapses the sum over `S` to the source's net out-flow
  have hval : (∑ u ∈ S, ∑ w, F.f u w) = value F :=
    Finset.sum_eq_single_of_mem s hsS
      (fun u huS hus => F.conserve u hus (fun h => htS (h ▸ huS)))
  -- split each inner sum over `S` and its complement
  have hsplit : (∑ u ∈ S, ∑ w, F.f u w)
      = (∑ u ∈ S, ∑ w ∈ S, F.f u w) + ∑ u ∈ S, ∑ w ∈ Sᶜ, F.f u w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S (F.f u)).symm
  -- the within-`S` double sum cancels by skew-symmetry
  have hcancel : ∑ u ∈ S, ∑ w ∈ S, F.f u w = 0 := by
    have h2 : (∑ u ∈ S, ∑ w ∈ S, F.f u w) + (∑ u ∈ S, ∑ w ∈ S, F.f u w) = 0 := by
      nth_rewrite 2 [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun w _ => ?_
      have := F.skew x w; linarith
    linarith
  -- across the cut, flow ≤ capacity edge by edge
  have hle : (∑ u ∈ S, ∑ w ∈ Sᶜ, F.f u w) ≤ capCut cap S :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun w _ => F.cap_le u w
  calc value F = ∑ u ∈ S, ∑ w, F.f u w := hval.symm
    _ = (∑ u ∈ S, ∑ w ∈ S, F.f u w) + ∑ u ∈ S, ∑ w ∈ Sᶜ, F.f u w := hsplit
    _ = ∑ u ∈ S, ∑ w ∈ Sᶜ, F.f u w := by rw [hcancel, zero_add]
    _ ≤ capCut cap S := hle

/-- **Max-flow / min-cut (the certificate).** A tight flow/cut pair — a flow `F` and an
`s`–`t` cut `S` with `value F = capCut cap S` — certifies *simultaneously* that `value F` is
the **maximum** flow value (`IsGreatest`) and `capCut cap S` is the **minimum** cut capacity
(`IsLeast`). This is `Certifies.weakDuality_tight` instantiated with `weak_duality`. -/
theorem maxflow_mincut {cap : V → V → ℝ} {s t : V} {F : Flow cap s t} {S : Finset V}
    (hsS : s ∈ S) (htS : t ∉ S) (htight : value F = capCut cap S) :
    IsGreatest {x : ℝ | ∃ F' : Flow cap s t, value F' = x} (value F) ∧
      IsLeast {x : ℝ | ∃ S' : Finset V, s ∈ S' ∧ t ∉ S' ∧ capCut cap S' = x} (capCut cap S) := by
  apply Certifies.weakDuality_tight
  · rintro p ⟨F', rfl⟩ d ⟨S', hsS', htS', rfl⟩
    exact weak_duality F' hsS' htS'
  · exact ⟨F, rfl⟩
  · exact ⟨S, hsS, htS, rfl⟩
  · exact htight

/-! ## The verification cost — and the find/check ledger instance -/

/-- A cut certificate's data: the network capacities and the cut `S`. -/
structure CutCert (V : Type*) [Fintype V] [DecidableEq V] where
  cap : V → V → ℝ
  S : Finset V

/-- Checking the cut bound = summing the `|S|·|Sᶜ|` across-cut capacities (plus one compare). -/
def CutCert.verifyCost (c : CutCert V) : ℕ := c.S.card * c.Sᶜ.card + 1

/-- The cut certificate plugs into the shared find/check ledger. -/
instance cutCertifies : Certifies.Ledger (CutCert V) where
  program c := StraightLineCost.StraightLineProgram.ofCost c.verifyCost

/-- **Checking is cheap (`O(|S|·|Sᶜ|)`).** The min-cut bound is verified in
`|S|·|Sᶜ| + 1` operations — the cheap-CHECK half; *finding* the cut is the imported wall. -/
theorem cutcert_cost_le (c : CutCert V) :
    Certifies.checkCost c ≤ c.S.card * c.Sᶜ.card + 1 := le_refl _

end Sundog.MaxFlowMinCut
