import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Discrete holonomy: the finite gauge zero-out

This is the finite, model-agnostic version of the Aharonov-Bohm gauge
zero-out used by the agentic trace slate. It does **not** claim that
transformer attention is a gauge field. It only proves the reusable discrete
core:

* along any finite path, the sum of consecutive potential differences
  telescopes to the endpoint difference;
* around any closed finite loop, that gauge contribution is exactly zero.

Later runtime instruments may map attention or search traces into this shape,
but that mapping is an imported measurement wall, not part of this theorem.
-/

namespace Sundog.DiscreteHolonomy

variable {A V : Type*} [AddCommGroup A]

/-- The discrete derivative of potential values along a path. -/
def discreteDiff (potential : Nat -> A) (i : Nat) : A :=
  potential (i + 1) - potential i

/--
Finite telescoping: summing consecutive potential differences along a path
leaves only the endpoint difference.
-/
theorem sum_discreteDiff_eq_endpoint (potential : Nat -> A) (steps : Nat) :
    (Finset.range steps).sum (fun i => discreteDiff potential i)
      = potential steps - potential 0 := by
  induction steps with
  | zero =>
      simp [discreteDiff]
  | succ steps ih =>
      rw [Finset.sum_range_succ, ih]
      simp [discreteDiff]

/-- The gauge contribution induced by a scalar potential on a discrete path. -/
def gaugeStep (chi : V -> A) (path : Nat -> V) (i : Nat) : A :=
  chi (path (i + 1)) - chi (path i)

/-- A discrete gauge sum along a finite path is the endpoint potential difference. -/
theorem gauge_sum_eq_endpoint (chi : V -> A) (path : Nat -> V) (steps : Nat) :
    (Finset.range steps).sum (fun i => gaugeStep chi path i)
      = chi (path steps) - chi (path 0) := by
  simpa [gaugeStep, discreteDiff] using
    (sum_discreteDiff_eq_endpoint (A := A) (fun i => chi (path i)) steps)

/-- The finite gauge zero-out: a closed loop has zero gauge circulation. -/
theorem closed_gauge_sum_zero (chi : V -> A) (path : Nat -> V) {steps : Nat}
    (hclosed : path steps = path 0) :
    (Finset.range steps).sum (fun i => gaugeStep chi path i) = 0 := by
  rw [gauge_sum_eq_endpoint, hclosed, sub_self]

/--
Path independence for the pure gauge contribution: two paths with equal
endpoints have the same gauge sum.
-/
theorem gauge_sum_path_independent (chi : V -> A) (path1 path2 : Nat -> V)
    {steps1 steps2 : Nat} (hstart : path1 0 = path2 0)
    (hend : path1 steps1 = path2 steps2) :
    (Finset.range steps1).sum (fun i => gaugeStep chi path1 i)
      = (Finset.range steps2).sum (fun i => gaugeStep chi path2 i) := by
  rw [gauge_sum_eq_endpoint, gauge_sum_eq_endpoint, hstart, hend]

end Sundog.DiscreteHolonomy

-- Axiom audit: the finite gauge zero-out is pure algebra over a finite sum.
#print axioms Sundog.DiscreteHolonomy.sum_discreteDiff_eq_endpoint
#print axioms Sundog.DiscreteHolonomy.gauge_sum_eq_endpoint
#print axioms Sundog.DiscreteHolonomy.closed_gauge_sum_zero
#print axioms Sundog.DiscreteHolonomy.gauge_sum_path_independent
