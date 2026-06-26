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

/-! ## Decisive-source binding (the H-I falsifier fix)

The RS receipt above certifies a low-degree *numeric* survivor and nothing else.
The falsifier in `AGENTIC_TRACE_H1_FALSIFIER_RESULT.md` showed that this is too
weak for the safety story H-I attaches to it: RS majority decoding prunes a
decisive *minority* source exactly as it prunes noise, so an accepted receipt can
drop the one cell that mattered, and — because the receipt is a function of the
numbers alone — one certificate can cover two incompatible readings.

The fix is a *decisive gate*: the caller designates a set `D` of authoritative
coordinates that an accepted prune must keep. The gate accepts only when the
survivor `f` reproduces the received word `y` on all of `D` (`D ⊆ agree S f y`).
The measurement wall is untouched — which coordinates *are* decisive is a
caller-supplied designation, not something the certificate derives — but, given
the designation, the lemmas below prove the drop is impossible. -/

variable (S : RSScheme F)

/-- The decisive gate: the designated authoritative coordinates `D` are all kept,
i.e. the survivor `f` reproduces the received word `y` on every coordinate of `D`
(none is pruned). -/
def DecisiveKept (f : Polynomial F) (y : Fin S.n → F) (D : Finset (Fin S.n)) : Prop :=
  D ⊆ agree S f y

/-- **Content preservation.** An accepted decisive-gated receipt reproduces the
received value at every decisive coordinate: the decisive source survives in the
decoding rather than being pruned as noise. This is the content-preservation
statement the count bound `branch_count_le_budget` could not supply. -/
theorem decisive_kept {f : Polynomial F} {y : Fin S.n → F} {D : Finset (Fin S.n)}
    (hgate : DecisiveKept S f y D) {i : Fin S.n} (hi : i ∈ D) :
    f.eval (S.nodes i) = y i :=
  (mem_agree S).mp (hgate hi)

/-- **Gate soundness (the falsifier-killer).** If the survivor disagrees with a
decisive coordinate — exactly the cell an RS prune deletes — the decisive gate
cannot pass. So no accepted decisive-gated receipt drops the decisive source: the
falsifier's "accepted receipt drops the decisive source" is impossible by
construction. -/
theorem decisive_pruned_not_kept {f : Polynomial F} {y : Fin S.n → F} {D : Finset (Fin S.n)}
    {i : Fin S.n} (hi : i ∈ D) (hpruned : f.eval (S.nodes i) ≠ y i) :
    ¬ DecisiveKept S f y D :=
  fun hgate => hpruned ((mem_agree S).mp (hgate hi))

/-- **Headline — safe AND decisive-preserving in one accepted receipt.** A
verifier that exhibits a survivor `f` for `y`, together with a passing decisive
gate, yields a receipt that is BOTH RS-safe (a decoding witness exists, via
`accept_sound`'s core) AND content-preserving (every decisive coordinate is
reproduced). This is the H-I receipt the falsifier demanded: the RS safety the
prototype already had, now provably bound to the decisive source it used to drop. -/
theorem decisive_receipt_safe_and_preserving
    (V : Verifier S) (y : Fin S.n → F) (D : Finset (Fin S.n))
    {f : Polynomial F} (hdec : V.decode? y = some f) (hgate : DecisiveKept S f y D) :
    Safe S y ∧ ∀ i ∈ D, f.eval (S.nodes i) = y i :=
  ⟨⟨f, V.decode_sound y f hdec⟩, fun _ hi => decisive_kept S hgate hi⟩

/-! ### The decisive designation is necessarily external

The fix above proves the *conditional* — given a decisive designation, the drop is
impossible — but leaves which coordinates are decisive caller-supplied. Could a
runtime instead *derive* the designation from the received word, removing the
caller? No: the word under-determines it. Whenever the survivor keeps two distinct
coordinates, two distinct singleton designations both pass the gate, so no function
of the word alone can return *the* decisive set. The caller (the authority/source
labelling) is a genuine imported wall, not an unfilled gap — this is the same shape
as the audit-blindness theorems (`AuditCost`): some information is provably absent
from the observable. -/

/-- **The word under-determines the decisive set.** If the survivor `f` keeps two
distinct coordinates `i ≠ j` of the received word `y`, then two *distinct* decisive
designations `{i}` and `{j}` both pass the gate. The same accepted word is
consistent with incompatible decisive sets. -/
theorem decisive_underdetermined_by_word
    {f : Polynomial F} {y : Fin S.n → F} {i j : Fin S.n}
    (hi : i ∈ agree S f y) (hj : j ∈ agree S f y) (hij : i ≠ j) :
    ∃ D₁ D₂ : Finset (Fin S.n),
      D₁ ≠ D₂ ∧ DecisiveKept S f y D₁ ∧ DecisiveKept S f y D₂ := by
  refine ⟨{i}, {j}, ?_, ?_, ?_⟩
  · rw [Ne, Finset.singleton_inj]; exact hij
  · exact Finset.singleton_subset_iff.mpr hi
  · exact Finset.singleton_subset_iff.mpr hj

/-- **No function of the word recovers the decisive set.** There is no single
decisive set that every gate-passing designation must equal — `{i}` and `{j}`
above are two that differ. So any `d : (Fin S.n → F) → Finset (Fin S.n)` claiming
to derive the designation from the word alone is underdetermined: the caller's
designation is a necessary import, not a gap the certificate can close. -/
theorem no_word_function_determines_decisive
    {f : Polynomial F} {y : Fin S.n → F} {i j : Fin S.n}
    (hi : i ∈ agree S f y) (hj : j ∈ agree S f y) (hij : i ≠ j) :
    ¬ ∃ D : Finset (Fin S.n), ∀ D' : Finset (Fin S.n), DecisiveKept S f y D' → D' = D := by
  rintro ⟨D, hD⟩
  obtain ⟨D₁, D₂, hne, h1, h2⟩ := decisive_underdetermined_by_word S hi hj hij
  exact hne ((hD D₁ h1).trans (hD D₂ h2).symm)

end Sundog.AgenticTrace

-- Axiom audit: these wrappers stay inside the same foundation as their imported cores.
#print axioms Sundog.AgenticTrace.rs_receipt_accept_safe
#print axioms Sundog.AgenticTrace.rs_receipt_unique
#print axioms Sundog.AgenticTrace.trace_gated_noninterference
#print axioms Sundog.AgenticTrace.branch_count_le_budget
#print axioms Sundog.AgenticTrace.not_branch_count_gt_budget
#print axioms Sundog.AgenticTrace.decisive_kept
#print axioms Sundog.AgenticTrace.decisive_pruned_not_kept
#print axioms Sundog.AgenticTrace.decisive_receipt_safe_and_preserving
#print axioms Sundog.AgenticTrace.decisive_underdetermined_by_word
#print axioms Sundog.AgenticTrace.no_word_function_determines_decisive
