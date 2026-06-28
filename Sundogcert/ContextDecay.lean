import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Context decay — the fold-pair annihilation quarantine rule (H-II deductive core)

The H-II falsifier (`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md`) showed the sampled
`c2`-sign-change cusp detector reads an *inflection*, not the fold-pair annihilation
an A3 cusp is, and the re-specified `scripts/foldpair_detector.py` fixed it by
measuring the **fold count** (interior extrema = critical points) across a
two-parameter family: a fold-pair annihilation is a clean drop of the fold count by
two between adjacent control values.

This module pins the deductive content of that runtime rule, the way
`AgenticTrace.decisive_*` pinned the H-I fix: the quarantine rule fires *exactly* on
a genuine fold-pair annihilation (a fold pair was present and is removed), never on
a fold-free or stable family, and the number of annihilations is budgeted by the
fold count. It is `linarith`/`omega`/`simp` only — no `sorry`, no `native_decide`.

It does **not** formalize the vector-memory → A3-cusp mapping (still the imported
wall); it formalizes what an annihilation receipt licenses.
-/

namespace Sundog.ContextDecay

/-- Fold counts of a 2-parameter score family in increasing control order: entry `i`
is the number of folds (interior extrema / critical points) of the `i`-th curve. -/
abbrev FoldCounts := List ℕ

/-- A **fold-pair annihilation**: two adjacent control values whose fold count drops
by exactly two — one local max and one local min merge and vanish (the A3 event). -/
def Annihilation (cs : FoldCounts) : Prop :=
  ∃ l a b r, cs = l ++ a :: b :: r ∧ a = b + 2

/-- The decay / quarantine rule: a context must decay iff its fold family annihilates. -/
def Decays (cs : FoldCounts) : Prop := Annihilation cs

/-- **Decay is earned.** A flagged decay exhibits a genuine fold pair — at least two
folds present — that is annihilated (the next count is exactly two lower). The rule
cannot flag decay without a fold pair having existed. -/
theorem decay_earned {cs : FoldCounts} (h : Decays cs) :
    ∃ l a b r, cs = l ++ a :: b :: r ∧ 2 ≤ a ∧ b = a - 2 := by
  obtain ⟨l, a, b, r, hcs, hab⟩ := h
  exact ⟨l, a, b, r, hcs, by omega, by omega⟩

/-- **No false positive on a fold-free family (the leg-A fix, formal).** A family with
zero folds throughout is never flagged: a monotone, fold-free retrieval curve cannot
trigger a decay — the exact failure the `c2` detector had. -/
theorem foldfree_no_decay {cs : FoldCounts} (h0 : ∀ c ∈ cs, c = 0) : ¬ Decays cs := by
  rintro ⟨l, a, b, r, hcs, hab⟩
  have : a = 0 := h0 a (by rw [hcs]; simp)
  omega

/-- **No false positive on a stable family.** A constant fold count (folds present but
stable across the control sweep) is never flagged. -/
theorem stable_no_decay {cs : FoldCounts} {k : ℕ} (hk : ∀ c ∈ cs, c = k) :
    ¬ Decays cs := by
  rintro ⟨l, a, b, r, hcs, hab⟩
  have ha : a = k := hk a (by rw [hcs]; simp)
  have hb : b = k := hk b (by rw [hcs]; simp)
  omega

/-- **Headline — the quarantine rule fires exactly on genuine fold-pair
annihilations.** Decay is licensed *iff* some adjacent control step exhibits a fold
pair (≥ 2 folds) annihilating (dropping by exactly two). Soundness and completeness
of the rule in one statement — the analog of `decisive_receipt_safe_and_preserving`. -/
theorem decays_iff_foldpair {cs : FoldCounts} :
    Decays cs ↔ ∃ l a b r, cs = l ++ a :: b :: r ∧ 2 ≤ a ∧ a = b + 2 := by
  constructor
  · rintro ⟨l, a, b, r, hcs, hab⟩
    exact ⟨l, a, b, r, hcs, by omega, hab⟩
  · rintro ⟨l, a, b, r, hcs, _, hab⟩
    exact ⟨l, a, b, r, hcs, hab⟩

/-- A pure annihilation chain: every adjacent control step is a fold-pair
annihilation (drops the fold count by exactly two). -/
def PureAnnihilation : FoldCounts → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a = b + 2 ∧ PureAnnihilation (b :: t)

/-- **Annihilation budget (the `branch_count_le_budget` analog).** Along a pure
annihilation chain starting at `h` folds, the number of annihilation steps
(`t.length`) cannot exceed half the initial fold count: `2 · steps ≤ h`. You cannot
annihilate more fold pairs than were present. -/
theorem annihilation_budget {h : ℕ} {t : FoldCounts}
    (hp : PureAnnihilation (h :: t)) : 2 * t.length ≤ h := by
  induction t generalizing h with
  | nil => simp
  | cons y t' ih =>
    simp only [PureAnnihilation] at hp
    obtain ⟨hhy, hrest⟩ := hp
    have hib := ih hrest
    simp only [List.length_cons]
    omega

end Sundog.ContextDecay

-- Axiom audit: these stay inside the foundational triple (no sorryAx, no native_decide).
#print axioms Sundog.ContextDecay.decay_earned
#print axioms Sundog.ContextDecay.foldfree_no_decay
#print axioms Sundog.ContextDecay.stable_no_decay
#print axioms Sundog.ContextDecay.decays_iff_foldpair
#print axioms Sundog.ContextDecay.annihilation_budget
