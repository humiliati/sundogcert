/-
# PercivalNodeEdge -- the node/edge typing law (ME-2)

The ME-quadrant slate's law-candidate: owned-NODE conditions live in M-and-E
(the duality regime); EDGE conditions (causal dependence) split even under full
endpoint ownership, because exogenous interventions are node-typed.

**Premise vs theorem (the definitional-emptiness fence, discharged up front).**
"Every exogenous intervention is a node intervention" is the MODELING PREMISE
(Pearl-native: do() operates on nodes; the mediation literature's path-specific
quantities are definable but not do()-implementable).  It is imported, not
proven.  What IS proven, and is not the definition:

* `owned_node_writable` -- the duality direction: any (decidable, satisfiable)
  predicate on the owned action node is enforceable by one output surgery, for
  every policy -- the cap's mechanism, made exact in the cell.
* `node_write_enforces_iff` -- **the characterization (the entry's content)**:
  a node-write (input surgery `iota` + output surgery `omega`, both fixed
  functions with no access to the policy) enforces do(U)-invariance for ALL
  policies **iff** at every `v` the u-slot of `omega` is dead AND either
  `iota` masks `u` (input constant in `u`) or `omega` voids the action
  (action-slot dead).  The forward direction requires constructing adversarial
  policies that separate rewired inputs -- it does not unfold from the
  definition.  In S1's channel language: **every universal enforcer of the
  edge condition is a per-`v` channel retreat -- mask (measure retreat) or
  void (act retreat).  There is no third way.**
* `node_write_enforce_price` -- every such enforcer pays the collapse: the
  written system's competence is at most `beta` (hence at least `rho - beta`
  below the optimum, by `comp_le_rho`/`followU_comp`).
* `node_edge_typing_law` -- the package: enforcement structure + price.

**Scope upgrade banked for OR-3:** the bridge's `sigma_write(target) = infinity`
previously inherited S2's *tested* projection family (mask / scramble /
permutation-average); this module quantifies over the ENTIRE node-write family
in the cell -- the residual scope is the model (binary-symmetric CI, the 2x2x2
cell), no longer the family.  Escaping the theorem now requires leaving the
node-write class (rewriting the policy's function -- excluded by exogeneity,
S2's horn (b)) or a richer joint.

Scope, honest: the Bool cell (as OR-4/ME-3); deterministic policies and
surgeries; ownership of BOTH input nodes and the action node is granted -- the
split is the edge's, not ownership's (the ME-1 census keeps the unowned-node
sub-row separate for exactly this reason).
-/
import Sundogcert.PercivalAuditPay

namespace Sundogcert.Percival

/-- A node-write: input-node surgery `iota` (rewires what the policy reads) and
output-node surgery `omega` (transforms the committed action), both fixed
functions of node values only -- exogenous, no access to the policy.  The
written system. -/
def nodeWrite (ι : Bool × Bool → Bool × Bool) (ω : Bool → Bool → Bool → Bool)
    (π : Bool → Bool → Bool) : Bool → Bool → Bool :=
  fun v u => ω v u (π (ι (v, u)).1 (ι (v, u)).2)

/--
**The duality direction: owned-node conditions are writable at arity one.**
Any decidable, satisfiable predicate on the action node is enforced for every
policy by one output surgery (project into the predicate) -- the cap's
mechanism in the cell.
-/
theorem owned_node_writable (P : Bool → Prop) [DecidablePred P] (a₀ : Bool)
    (h₀ : P a₀) :
    ∃ ω : Bool → Bool → Bool → Bool, ∀ (π : Bool → Bool → Bool) (v u : Bool),
      P (nodeWrite id ω π v u) := by
  refine ⟨fun _ _ a => if P a then a else a₀, fun π v u => ?_⟩
  simp only [nodeWrite, id_eq]
  split_ifs with h
  · exact h
  · exact h₀

/--
**The characterization: every universal enforcer is a channel retreat.**
A node-write enforces do(U)-invariance for ALL policies iff at every `v` the
u-slot of `omega` is dead and either `iota` masks `u` (measure retreat) or
`omega` voids the action (act retreat).  The forward direction separates
rewired inputs with adversarial policies; there is no third way.
-/
theorem node_write_enforces_iff (ι : Bool × Bool → Bool × Bool)
    (ω : Bool → Bool → Bool → Bool) :
    (∀ π, DoUInvariant (nodeWrite ι ω π)) ↔
      ∀ v, (∀ u u' a, ω v u a = ω v u' a) ∧
        ((∀ u u', ι (v, u) = ι (v, u')) ∨ ∀ u a a', ω v u a = ω v u a') := by
  constructor
  · intro henf v
    have hub : ∀ u u' a, ω v u a = ω v u' a := by
      intro u u' a
      have h := henf (fun _ _ => a) v u u'
      simpa [nodeWrite] using h
    refine ⟨hub, ?_⟩
    by_cases hmask : ∀ u u', ι (v, u) = ι (v, u')
    · exact Or.inl hmask
    · right
      obtain ⟨u₀, hu₀⟩ := not_forall.mp hmask
      obtain ⟨u₁, hne⟩ := not_forall.mp hu₀
      intro u a a'
      have h01 := henf (fun x y => if (x, y) = ι (v, u₀) then a else a') v u₀ u₁
      simp [nodeWrite, Ne.symm hne] at h01
      calc ω v u a = ω v u₀ a := hub u u₀ a
        _ = ω v u₁ a' := h01
        _ = ω v u a' := hub u₁ u a'
  · intro hstr π v u u'
    obtain ⟨hub, hcase⟩ := hstr v
    simp only [nodeWrite]
    rcases hcase with hmask | hvoid
    · rw [hmask u u']
      exact hub u u' _
    · calc ω v u (π (ι (v, u)).1 (ι (v, u)).2)
          = ω v u (π (ι (v, u')).1 (ι (v, u')).2) := hvoid u _ _
        _ = ω v u' (π (ι (v, u')).1 (ι (v, u')).2) := hub u u' _

/--
**Every enforcer pays the collapse.**  A node-write that enforces the edge
condition for all policies caps the written system's competence at `beta` --
the retreat is priced (and sits `>= rho - beta` below the optimum, by the
Bayes ceiling). -/
theorem node_write_enforce_price {β ρ : ℚ} (hβ : 1/2 ≤ β)
    (ι : Bool × Bool → Bool × Bool) (ω : Bool → Bool → Bool → Bool)
    (henf : ∀ π, DoUInvariant (nodeWrite ι ω π)) (π : Bool → Bool → Bool) :
    comp β ρ (nodeWrite ι ω π) ≤ β :=
  dou_comp_le_beta hβ (henf π)

/--
**The node/edge typing law, packaged.**  Full node ownership granted, every
node-write that universally enforces the edge condition (i) decomposes at each
`v` into a measure retreat (mask) or an act retreat (void) -- the
characterization -- and (ii) pays the collapse price.  The edge is not a node:
owning every node does not buy the edge.
-/
theorem node_edge_typing_law {β ρ : ℚ} (hβ : 1/2 ≤ β)
    (ι : Bool × Bool → Bool × Bool) (ω : Bool → Bool → Bool → Bool)
    (henf : ∀ π, DoUInvariant (nodeWrite ι ω π)) :
    (∀ v, (∀ u u', ι (v, u) = ι (v, u')) ∨ ∀ u a a', ω v u a = ω v u a')
    ∧ ∀ π, comp β ρ (nodeWrite ι ω π) ≤ β :=
  ⟨fun v => ((node_write_enforces_iff ι ω).mp henf v).2,
   fun π => node_write_enforce_price hβ ι ω henf π⟩

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.owned_node_writable' does not depend on any axioms -/
#guard_msgs in
#print axioms owned_node_writable

/-- info: 'Sundogcert.Percival.node_write_enforces_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms node_write_enforces_iff

/-- info: 'Sundogcert.Percival.node_write_enforce_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms node_write_enforce_price

/-- info: 'Sundogcert.Percival.node_edge_typing_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms node_edge_typing_law

end Sundogcert.Percival
