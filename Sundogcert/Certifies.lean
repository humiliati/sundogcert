/-
# Certifies — the find/check ledger as a general certificate theory (N-3)

`ShortestPathCert`, the syndrome certificate, and the ReLU-DAG gate count are all instances
of one structure: **a witness whose verifier is a cheap straight-line program, soundness
proved, *finding* the witness the imported wall.** This module names the reusable optimality
core of that structure and lets new domains plug in.

The core is **LP weak duality**: a *dual* witness bounds *every* primal value, so a *tight
pair* (a primal and a dual value that coincide) certifies both optima at once. `ShortestPathCert`
is the one-sided shape (`IsLeast` from a feasible potential + an achiever); `MaxFlowMinCut`
(this slate's new module) is the two-sided shape (a cut certifies a flow's optimality and
vice versa) and is exactly `weakDuality_tight`.

As everywhere in this development, only the **CHECK** is here: the cheap verifier and its
soundness. *Finding* the tight pair (the max-flow / shortest-path search) is the imported wall.
-/
import Mathlib.Order.Bounds.Basic
import Sundogcert.StraightLineCost

namespace Sundog.Certifies

/-- **LP-duality optimality core (the reusable certificate).** If every primal value is `≤`
every dual value (*weak duality*), then a **tight pair** `p ∈ P`, `d ∈ D` with `p = d`
certifies that `p` is the primal **maximum** (`IsGreatest P p`) and `d` is the dual
**minimum** (`IsLeast D d`) — and the two optima coincide. The whole content of "a dual
witness certifies a primal optimum"; modules supply `weak` and the tight pair, *finding*
which is the search. -/
theorem weakDuality_tight {α : Type*} [Preorder α] {P D : Set α}
    (weak : ∀ p ∈ P, ∀ d ∈ D, p ≤ d) {p d : α}
    (hp : p ∈ P) (hd : d ∈ D) (htight : p = d) :
    IsGreatest P p ∧ IsLeast D d := by
  refine ⟨⟨hp, fun x hx => ?_⟩, ⟨hd, fun x hx => ?_⟩⟩
  · rw [htight]; exact weak x hx d hd
  · rw [← htight]; exact weak p hp x hx

/-- The one-sided shape (`ShortestPathCert.cert_isLeast`): a dual lower bound that is
attained pins the **least** element of an objective set. -/
theorem isLeast_of_bound_attained {α : Type*} [Preorder α] {S : Set α} {opt : α}
    (attained : opt ∈ S) (bound : ∀ x ∈ S, opt ≤ x) : IsLeast S opt :=
  ⟨attained, bound⟩

/-- A problem family in the find/check ledger: each instance carries a straight-line
verifier (its cheap CHECK) through the shared cost interface. The soundness obligation —
that the verifier certifies the intended optimum — is discharged per instance
(`feasible_le_walk` / `cert_isLeast`; `weak_duality` / `maxflow_mincut`), and *finding* the
witness is always the imported wall. -/
class Ledger (P : Type*) extends StraightLineCost.HasStraightLineCost P

/-- The certified check cost of a ledger problem. -/
def checkCost {P : Type*} [Ledger P] (p : P) : ℕ := StraightLineCost.costOf p

end Sundog.Certifies
