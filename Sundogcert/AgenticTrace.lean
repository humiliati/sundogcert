import Sundogcert.RSCertificate
import Sundogcert.Tauroctony
import Mathlib.Data.Finset.Card

/-!
# Agentic trace hooks

This module is the small formal receipt layer for the agentic-search hypothesis
slate. It does not formalize transformer internals, vector databases, or any
empirical net-layer claim. Those remain imported measurement walls.

What is checked here is narrower and useful:

* an accepted Reed-Solomon receipt implies the received trace is safe;
* inside the unique-decoding radius, the accepted message is unique;
* a policy gated only by a published signature is invariant under any
  signature-preserving attack;
* a finite branch trace injected into certified slots cannot exceed its budget.

That is the Lean-sized common skeleton behind the proposed "read the shadow,
test the boundary" instruments.
-/

namespace Sundog.AgenticTrace

open Sundog.RSCertificate

universe u

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Reed-Solomon trace receipts -/

/-- A received search trace together with the cheap verifier that checks it. -/
structure RSReceipt (S : RSScheme F) where
  word : Fin S.n -> F
  verifier : Verifier S

/-- The receipt accepts exactly when its verifier accepts the received word. -/
def RSReceipt.Accepted {S : RSScheme F} (r : RSReceipt S) : Prop :=
  r.verifier.run S r.word = Verdict.accept

/-- An accepted Reed-Solomon receipt is safe: the verifier exhibited a decoding witness. -/
theorem rs_receipt_accept_safe {S : RSScheme F} (r : RSReceipt S) :
    r.Accepted -> Safe S r.word :=
  Sundog.RSCertificate.accept_sound (S := S) r.verifier r.word

/-- Within the unique-decoding radius, two decodings of the same received trace are equal. -/
theorem rs_receipt_unique {S : RSScheme F} (hrad : 2 * S.τ + S.k <= S.n)
    (y : Fin S.n -> F) {p q : Polynomial F} (hp : Decodes S p y) (hq : Decodes S q y) :
    p = q :=
  Sundog.RSCertificate.unique_decoding (S := S) hrad y hp hq

/-! ## Signature-gated noninterference -/

/-- A trace-gated policy is one that factors through a published signature channel. -/
def TraceGated {Obs Act Signature : Type u}
    (policy : Obs -> Act) (signature : Obs -> Signature) : Prop :=
  Sundogcert.Tauroctony.FactorsThrough policy signature

/-- An attack is trace-preserving when it leaves the published signature unchanged. -/
def TracePreserving {Obs Signature : Type u}
    (signature : Obs -> Signature) (attack : Obs -> Obs) : Prop :=
  Sundogcert.Tauroctony.Preserves signature attack

/-- Trace-gated policies are invariant under trace-preserving attacks. -/
theorem trace_gated_noninterference {Obs Act Signature : Type u}
    {policy : Obs -> Act} {signature : Obs -> Signature} {attack : Obs -> Obs}
    (hpolicy : TraceGated policy signature)
    (hattack : TracePreserving signature attack) :
    forall obs, policy (attack obs) = policy obs :=
  Sundogcert.Tauroctony.signature_noninterference hpolicy hattack

/-! ## Finite search-budget receipts -/

/--
A finite search trace whose branches are injected into a certified set of slots.
This is the cap-set-style boundary in its most abstract form: the admissible
trace has a published finite coordinate witness.
-/
structure BudgetedTrace (Branch : Type u) (budget : Nat) [DecidableEq Branch] where
  branches : Finset Branch
  slot : Branch -> Fin budget
  slot_injective : Set.InjOn slot (branches : Set Branch)

/-- A budgeted trace cannot contain more branches than its certified slot budget. -/
theorem branch_count_le_budget {Branch : Type u} [DecidableEq Branch]
    {budget : Nat} (trace : BudgetedTrace Branch budget) :
    trace.branches.card <= budget := by
  calc
    trace.branches.card <= (Finset.univ : Finset (Fin budget)).card :=
      Finset.card_le_card_of_injOn trace.slot
        (by intro branch _; exact Finset.mem_univ (trace.slot branch))
        trace.slot_injective
    _ = budget := by simp

/-- If the certified budget is exceeded, the trace is impossible. -/
theorem not_branch_count_gt_budget {Branch : Type u} [DecidableEq Branch]
    {budget : Nat} (trace : BudgetedTrace Branch budget) :
    Not (budget < trace.branches.card) :=
  not_lt_of_ge (branch_count_le_budget trace)

end Sundog.AgenticTrace

-- Axiom audit: these wrappers stay inside the same foundation as their imported cores.
#print axioms Sundog.AgenticTrace.rs_receipt_accept_safe
#print axioms Sundog.AgenticTrace.rs_receipt_unique
#print axioms Sundog.AgenticTrace.trace_gated_noninterference
#print axioms Sundog.AgenticTrace.branch_count_le_budget
#print axioms Sundog.AgenticTrace.not_branch_count_gt_budget
