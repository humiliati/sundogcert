/-
# PercivalBasin -- the corrigibility basin over ARBITRARY hypothesis space (LP-4)

`PercivalFixedPoint` gave the deploy-correct dynamics on a two-point hypothesis
space {V, W}. The corrigibility-basin debate (Christiano's "broad basin of
attraction" vs its critics; CAST's "Corrigibility Attractor Hypothesis", which
explicitly calls for the mathematical proofs it does not supply) is about BREADTH
over a whole neighbourhood of preferences. So the sharp question is not "does the
two-point chain topple" but "over how large a space is corrigibility a basin, and
what governs its breadth."

This module lifts the result to an ARBITRARY hypothesis type `H` (no finiteness,
no metric, no preference-neighbourhood structure) with:

* a distinguished corrigible target `V`,
* a `fall : H → H` successor for uncovered rounds (the divert-to-deceiver map),
* a coverage predicate `cov : H → Bool` (does this deployment's correction round
  cover its own disagreement region).

The `basin` is the set of hypotheses whose deploy-correct trajectory eventually
reaches and STAYS at `V`. Main results:

* `basin_empty_without_self_coverage` -- if `V` does not self-cover (`cov V =
  false`) and its uncovered successor is not `V`, the basin is EMPTY, for EVERY
  hypothesis space `H`. Breadth is zero regardless of how many preferences sit
  "near" `V`: the basin metaphor's breadth is not a property of preference-space
  geometry. This is the general form of `fall_without_coverage`, and it is the
  anti-basin (critic-side) statement made precise and structure-independent.
* `basin_univ_full_coverage` -- if coverage is sustained everywhere, the basin is
  the WHOLE space: corrigibility is reached from any start in one round. Breadth is
  total. So the basin's breadth swings between empty and total purely on the
  coverage predicate, with `H`'s structure playing no role -- **breadth is governed
  by coverage, not by preference-neighbourhood.**

Scope, honest: still a coverage-governed step over an arbitrary type; the mapping
to real preference dynamics is a model, not a claim about foundation models. The
point is the structure-independence: the breadth swing is entirely in `cov`.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Sundogcert.Percival.Basin

variable {H : Type*}

/-- One deploy-correct round: a covered round recovers the corrigible target `V`;
an uncovered round diverts along `fall`. -/
def step (V : H) (fall : H → H) (covered : Bool) (h : H) : H :=
  if covered then V else fall h

/-- The deploy-correct trajectory: coverage of the current deployment decides the
next one. -/
def traj (V : H) (fall : H → H) (cov : H → Bool) (h0 : H) : ℕ → H
  | 0 => h0
  | n + 1 => step V fall (cov (traj V fall cov h0 n)) (traj V fall cov h0 n)

/-- The corrigibility basin: hypotheses whose trajectory eventually reaches and
stays at the corrigible target. -/
def basin (V : H) (fall : H → H) (cov : H → Bool) : Set H :=
  {h | ∃ N, ∀ m, N ≤ m → traj V fall cov h m = V}

/--
**The basin is empty without self-coverage -- for every hypothesis space.** If the
corrigible target does not cover its own correction round and its uncovered
successor differs from it, then NO hypothesis eventually-stays at `V`: one reached
`V` is toppled the next round. Breadth is zero independent of `H`'s size or any
notion of preference proximity -- the anti-basin statement, structure-independent.
-/
theorem basin_empty_without_self_coverage (V : H) (fall : H → H) (cov : H → Bool)
    (hV : cov V = false) (hfall : fall V ≠ V) :
    basin V fall cov = ∅ := by
  ext h
  simp only [Set.mem_empty_iff_false, iff_false, basin, Set.mem_setOf_eq]
  rintro ⟨N, hN⟩
  have hNV : traj V fall cov h N = V := hN N (le_refl N)
  have hN1 : traj V fall cov h (N + 1) = V := hN (N + 1) (Nat.le_succ N)
  simp only [traj] at hN1
  rw [hNV, hV] at hN1
  simp only [step] at hN1
  exact hfall hN1

/--
**The basin is the whole space under full coverage.** If every deployment's
correction round is covered, corrigibility is reached from any start in one round
and stays. Breadth is total -- again independent of `H`'s structure.
-/
theorem basin_univ_full_coverage (V : H) (fall : H → H) (cov : H → Bool)
    (hfull : ∀ h, cov h = true) :
    basin V fall cov = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro h
  refine ⟨1, fun m hm => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  show step V fall (cov (traj V fall cov h n)) (traj V fall cov h n) = V
  rw [hfull]
  rfl

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.Basin.basin_empty_without_self_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms basin_empty_without_self_coverage

/-- info: 'Sundogcert.Percival.Basin.basin_univ_full_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms basin_univ_full_coverage

end Sundogcert.Percival.Basin
