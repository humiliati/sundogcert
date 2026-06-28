import Sundogcert.DiscreteHolonomy
import Mathlib.Tactic

/-!
# Hierarchy holonomy — the injection-quarantine core (H-III deductive core)

The H-III falsifier (`AGENTIC_TRACE_H3_FALSIFIER_RESULT.md`) showed the loop-circulation
filter measures only the non-conservative (curl) component of a trace field, while the
instruction hierarchy lives in the conservative (gradient / potential) component — which
`DiscreteHolonomy.closed_gauge_sum_zero` proves contributes zero to every loop. The
re-specified runtime (`scripts/hierarchy_holonomy_receipt.py`) keys the injection verdict
on the gradient: a reference dominance constraint (a trusted vertex must out-rank an
untrusted one) is checked directly.

This module pins that fix's deductive content, the way `ContextDecay` pinned the H-II
fix:

* the quarantine rule fires *exactly* on a hierarchy violation (`intact_iff_not_hijacked`,
  `hijack_witness`);
* **the loop circulation cannot determine the hierarchy** — two potentials with the SAME
  (zero) loop circulation but OPPOSITE hierarchy verdicts (`hierarchy_separates_what_loop
  _cannot`). This is the formal blind spot, the H-III analog of H-I's
  `no_word_function_determines_decisive`;
* the gradient/endpoint *does* carry the hierarchy — the gauge sum along a path is exactly
  the authority gap the loop discards (`authority_gap_along_path`).

It does **not** formalize the trace→holonomy measurement map or the trusted reference
hierarchy; those remain imports by design.
-/

namespace Sundog.HierarchyHolonomy

open Sundog.DiscreteHolonomy

variable {V : Type*}

/-- The instruction hierarchy is intact: every reference dominance constraint `(hi, lo)`
holds — the trusted vertex `hi` strictly out-ranks the untrusted `lo`. -/
def HierarchyIntact (potential : V → ℤ) (refs : List (V × V)) : Prop :=
  ∀ p ∈ refs, potential p.2 < potential p.1

/-- The hierarchy is hijacked: some reference constraint is violated. -/
def Hijacked (potential : V → ℤ) (refs : List (V × V)) : Prop :=
  ∃ p ∈ refs, ¬ potential p.2 < potential p.1

/-- **The quarantine rule fires exactly on a hijack.** The injection filter accepts iff
the hierarchy is intact, i.e. iff it is not hijacked. -/
theorem intact_iff_not_hijacked (potential : V → ℤ) (refs : List (V × V)) :
    HierarchyIntact potential refs ↔ ¬ Hijacked potential refs := by
  constructor
  · rintro h ⟨p, hp, hneg⟩
    exact hneg (h p hp)
  · intro h p hp
    by_contra hlt
    exact h ⟨p, hp, hlt⟩

/-- **A hijack is earned.** A flagged hijack exhibits a concrete violated constraint: a
trusted vertex that fails to out-rank its untrusted counterpart. (The H-III analog of
`ContextDecay.decay_earned`.) -/
theorem hijack_witness {potential : V → ℤ} {refs : List (V × V)}
    (h : Hijacked potential refs) : ∃ p ∈ refs, potential p.1 ≤ potential p.2 := by
  obtain ⟨p, hp, hneg⟩ := h
  exact ⟨p, hp, not_lt.mp hneg⟩

/-- **The gradient carries the hierarchy.** The gauge sum along a path is exactly the
authority gap between its endpoints — the information the loop circulation discards.
(`DiscreteHolonomy.gauge_sum_eq_endpoint`, read as an authority statement.) -/
theorem authority_gap_along_path (potential : V → ℤ) (path : Nat → V) (steps : Nat) :
    (Finset.range steps).sum (fun i => gaugeStep potential path i)
      = potential (path steps) - potential (path 0) :=
  gauge_sum_eq_endpoint potential path steps

/-- A closed reasoning loop visiting vertices `0 → 1 → 2 → 0`. -/
def loopPath : Nat → Nat
  | 1 => 1
  | 2 => 2
  | _ => 0

/-- The observed loop circulation of a pure gradient (gauge) field. -/
def loopCirc (potential : Nat → ℤ) : ℤ :=
  (Finset.range 3).sum (fun i => gaugeStep potential loopPath i)

/-- The loop circulation is identically zero — the gauge zero-out, so it carries no
information about the potential (the hierarchy). -/
theorem loopCirc_zero (potential : Nat → ℤ) : loopCirc potential = 0 :=
  closed_gauge_sum_zero potential loopPath (by rfl)

/-- **The loop is blind; the gradient is not.** Two authority potentials with the SAME
loop circulation (both zero) but OPPOSITE hierarchy verdicts — one intact, one hijacked.
The loop-circulation filter provably cannot separate a hijack from a benign trace, so the
gradient/hierarchy check (which does) is strictly necessary. This is the formal blind
spot, the H-III analog of H-I's `no_word_function_determines_decisive`. -/
theorem hierarchy_separates_what_loop_cannot :
    ∃ (χ₁ χ₂ : Nat → ℤ),
      loopCirc χ₁ = loopCirc χ₂ ∧
      HierarchyIntact χ₁ [(1, 2)] ∧ Hijacked χ₂ [(1, 2)] := by
  refine ⟨fun n => -(n : ℤ), fun n => (n : ℤ), ?_, ?_, ?_⟩
  · rw [loopCirc_zero, loopCirc_zero]
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    norm_num
  · exact ⟨(1, 2), List.mem_singleton.mpr rfl, by norm_num⟩

end Sundog.HierarchyHolonomy

-- Axiom audit: the injection-quarantine core (gauge zero-out + finite logic).
#print axioms Sundog.HierarchyHolonomy.intact_iff_not_hijacked
#print axioms Sundog.HierarchyHolonomy.hijack_witness
#print axioms Sundog.HierarchyHolonomy.authority_gap_along_path
#print axioms Sundog.HierarchyHolonomy.loopCirc_zero
#print axioms Sundog.HierarchyHolonomy.hierarchy_separates_what_loop_cannot
