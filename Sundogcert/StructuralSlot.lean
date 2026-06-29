import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Structural slot — the line-free (cap-set) trace-bound core (H-IV deductive core)

The H-IV falsifier (`AGENTIC_TRACE_H4_FALSIFIER_RESULT.md`) showed the count-by-score
budget receipt bounds the per-node admitted COUNT, which is neither the solution-bearing
structure (it prunes a low-score winner) nor the total tree complexity (per-node
acceptance composes to `budget**depth`). The re-specified runtime
(`scripts/structural_slot_receipt.py`) admits on a STRUCTURAL line-free predicate: a
branch's coordinate in `F₃ⁿ` is admitted iff it keeps the admitted set a cap (no three
distinct points `a + b + c = 0` — the collinearity / 3-AP condition in `AG(n,3)`).

This module pins that fix's deductive content, the way `ContextDecay` and
`HierarchyHolonomy` pinned the H-II and H-III fixes:

* the rule fires exactly on a line — a refusal is *earned* (`refusal_earned`);
* admission preserves the cap (`admit_preserves_lineFree`) — the fix's core correctness;
* the admitted cap is bounded by the ambient space, independent of how many candidates
  (the tree's `budget**depth`) produced it (`lineFree_card_le_univ`); the sharp
  Ellenberg–Gijswijt capacity is the named import;
* **a count cannot determine the structure** (`count_cannot_determine_structure`): two
  branch sets of equal cardinality, one a cap and one containing a line — so a count
  budget is blind to line-freeness. The H-IV analog of H-I's
  `no_word_function_determines_decisive` and H-III's `hierarchy_separates_what_loop_cannot`.

It does **not** justify mapping real agent branches into `F₃ⁿ`, nor reprove the
Ellenberg–Gijswijt bound; those remain imports by design.
-/

namespace Sundog.StructuralSlot

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- Three distinct points are collinear (a line / 3-term AP) iff they sum to zero. In
`F₃ⁿ` this is exactly the cap-set forbidden configuration. -/
def IsLine (a b c : A) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c = 0

/-- A set is line-free (a cap): it contains no line. -/
def LineFree (S : Finset A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ¬ IsLine a b c

/-- Adding `c` to `S` would create a line with two existing points; the receipt refuses
exactly these. -/
def FormsLine (S : Finset A) (c : A) : Prop := ∃ a ∈ S, ∃ b ∈ S, IsLine a b c

instance instDecidableIsLine (a b c : A) : Decidable (IsLine a b c) := by
  unfold IsLine; infer_instance

instance instDecidableLineFree (S : Finset A) : Decidable (LineFree S) := by
  unfold LineFree; infer_instance

/-- **A refusal is earned.** A refused candidate exhibits a concrete line: two admitted
points it is collinear with. (The H-IV analog of `decay_earned` / `hijack_witness`.) -/
theorem refusal_earned {S : Finset A} {c : A} (h : FormsLine S c) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c = 0 := by
  obtain ⟨a, ha, b, hb, hline⟩ := h
  exact ⟨a, ha, b, hb, hline.1, hline.2.1, hline.2.2.1, hline.2.2.2⟩

/-- **Admission preserves the cap.** If `S` is line-free and `c` forms no line with it,
the admitted set `insert c S` is still line-free. This is the fix's core correctness:
structural admission keeps the admitted set a cap. -/
theorem admit_preserves_lineFree {S : Finset A} {c : A}
    (hS : LineFree S) (hc : ¬ FormsLine S c) : LineFree (insert c S) := by
  intro a ha b hb d hd hline
  obtain ⟨hab, had, hbd, hsum⟩ := hline
  rw [Finset.mem_insert] at ha hb hd
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · rcases hd with rfl | hd
      · exact absurd rfl had
      · exact hc ⟨b, hb, d, hd, hbd, Ne.symm hab, Ne.symm had, by rw [← hsum]; abel⟩
  · rcases hb with rfl | hb
    · rcases hd with rfl | hd
      · exact absurd rfl hbd
      · exact hc ⟨a, ha, d, hd, had, hab, Ne.symm hbd, by rw [← hsum]; abel⟩
    · rcases hd with rfl | hd
      · exact hc ⟨a, ha, b, hb, hab, had, hbd, hsum⟩
      · exact hS a ha b hb d hd ⟨hab, had, hbd, hsum⟩

/-- **The structural budget is the capacity, not the count.** An admitted cap is bounded by
the ambient space — independent of how many candidates (the tree's `budget**depth`)
produced it. The sharp Ellenberg–Gijswijt cap capacity is the named import; this is the
trivial-but-depth-independent core. -/
theorem lineFree_card_le_univ [Fintype A] {S : Finset A} (_hcap : LineFree S) :
    S.card ≤ Fintype.card A := Finset.card_le_univ S

/-- **A count cannot determine the structure.** Two branch sets of equal cardinality, one a
cap and one containing a line — so a count (cardinality) budget cannot tell a line-free
set from one with a line. The H-IV analog of `no_word_function_determines_decisive`
(H-I) and `hierarchy_separates_what_loop_cannot` (H-III). -/
theorem count_cannot_determine_structure :
    ∃ S T : Finset (ZMod 3 × ZMod 3),
      S.card = T.card ∧ LineFree S ∧ ¬ LineFree T := by
  refine ⟨{(0, 0), (1, 0), (0, 1)}, {(0, 0), (1, 0), (2, 0)}, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end Sundog.StructuralSlot

-- Axiom audit: the line-free (cap-set) trace-bound core.
#print axioms Sundog.StructuralSlot.refusal_earned
#print axioms Sundog.StructuralSlot.admit_preserves_lineFree
#print axioms Sundog.StructuralSlot.lineFree_card_le_univ
#print axioms Sundog.StructuralSlot.count_cannot_determine_structure
