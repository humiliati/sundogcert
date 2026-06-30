/-
# An unconditional find/check separation for an abstraction family (FC-2)

FC-1 (`AbstractionCert`) gave the find/check ledger its program-synthesis **CHECK** (a candidate
reproduces the training pairs) and witnessed that training evidence under-determines the program.
FC-2 supplies the matching **SEPARATION**: a concrete family of real DSL rules on which *checking* a
claimed candidate is a single probe, while *finding* whether any candidate fits needs probes linear
in the family size — both sides machine-checked, nothing imported, in the query model.
It reuses `QueryGap`'s adversary and is the abstraction instance of its `check ≪ find`.

## The needle family (a genuine DSL family, not a strawman)
Candidate `j : Fin D` is the real `AbstractionCert` program `recolor j (j+1)`. Its private
**distinguishing input** is `probe j = [[j]]` (a 1×1 grid of color `j`):

* `eval_ruleOf_probe_self` — rule `j` *changes* its own probe (`[[j]] ↦ [[j+1]]`).
* `eval_ruleOf_probe_other` — every *other* rule *fixes* `probe j` (no color `j` to recolor).

So each probe reveals exactly one candidate's consistency — the unstructured "needle" oracle.

## What is PROVED (both sides, nothing imported)
* `cbit_eq_verify` — the **CHECK** of one candidate (its consistency bit at its probe) is *exactly*
  `AbstractionCert.Verify` on the single distinguishing pair. The FC-1 verifier IS the query.
* `cvec_id` / `cvec_rule` — the adversary's hard instances are realized by **genuine behaviors**:
  the all-inconsistent oracle by the identity behavior, each one-hot by the rule that generated it.
  So the bound is not vacuous on this family — `GAP_COLLAPSES_IN_MODEL` does not fire.
* `find_ge` — any prober deciding whether some candidate is consistent needs `≥ D` probes
  (`QueryGap.search_needs_n_queries`, the adversary).
* `abstraction_check_lt_find` (**headline**) — for `D ≥ 2`, checking one candidate costs a single
  probe while any correct prober needs `≥ D`: `check ≪ find` for a real abstraction family.

## The wall (named, NOT proved)
This is an **unconditional lower bound in a restricted (query) model**, exactly as in `QueryGap` —
NOT a P-vs-NP separation. Program-search hardness in the full computational model stays the imported
wall; the honest content is that a genuine DSL rule-family instantiates the gap with no shortcut.
-/
import Sundogcert.QueryGap
import Sundogcert.AbstractionCert

namespace Sundog.AbstractionQueryGap

open Sundog.AbstractionCert Sundog.QueryGap

variable {D : ℕ}

/-- Candidate rule `j`: recolor color `j` to `j+1` (a real `AbstractionCert` program). -/
def ruleOf (j : Fin D) : Prog := .recolor (j : ℕ) ((j : ℕ) + 1)

/-- The distinguishing input ("probe") of candidate `j`: a 1×1 grid of color `j`. -/
def probe (j : Fin D) : Grid := [[(j : ℕ)]]

/-- Rule `j` **changes** its own probe: `[[j]] ↦ [[j+1]]`. -/
@[simp] theorem eval_ruleOf_probe_self (j : Fin D) :
    eval (ruleOf j) (probe j) = [[(j : ℕ) + 1]] := by
  simp [ruleOf, probe, eval]

/-- Every **other** rule `k ≠ j` **fixes** `probe j` (it has no color `j` to recolor). -/
theorem eval_ruleOf_probe_other {j k : Fin D} (h : k ≠ j) :
    eval (ruleOf k) (probe j) = probe j := by
  have hjk : (j : ℕ) ≠ (k : ℕ) := Fin.val_ne_of_ne (fun he => h he.symm)
  simp [ruleOf, probe, eval, hjk]

/-- The **consistency bit** (the CHECK of one candidate): does rule `j` reproduce the observed
behavior `h` on its own distinguishing input? -/
def cbit (h : Grid → Grid) (j : Fin D) : Bool :=
  decide (eval (ruleOf j) (probe j) = h (probe j))

/-- **CHECK = the FC-1 verifier on one example.** The consistency bit is exactly
`AbstractionCert.Verify` of the candidate against its single distinguishing training pair — the
query-model CHECK is the find/check ledger's CHECK. -/
theorem cbit_eq_verify (h : Grid → Grid) (j : Fin D) :
    cbit h j = Verify (ruleOf j) [(probe j, h (probe j))] := by
  simp [cbit, Verify]

/-- **The all-inconsistent oracle is realized by the identity behavior.** If nothing was
transformed, no candidate is consistent — the adversary's all-false instance is a genuine DSL
behavior. -/
theorem cvec_id (j : Fin D) : cbit (eval .id) j = false := by
  have hne : ([[(j : ℕ) + 1]] : Grid) ≠ probe j := by simp [probe]
  simp [cbit, eval_ruleOf_probe_self, hne]

/-- **Each one-hot is realized by the rule that generated it.** If rule `m` produced the behavior,
exactly candidate `m` is consistent — every adversary one-hot instance is a genuine DSL behavior. -/
theorem cvec_rule (m j : Fin D) : cbit (eval (ruleOf m)) j = decide (j = m) := by
  by_cases h : j = m
  · subst h; simp [cbit]
  · have ho : eval (ruleOf m) (probe j) = probe j := eval_ruleOf_probe_other (Ne.symm h)
    have hne : ([[(j : ℕ) + 1]] : Grid) ≠ probe j := by simp [probe]
    rw [cbit, eval_ruleOf_probe_self, ho, decide_eq_false hne, decide_eq_false h]

/-- **FIND is hard (both sides machine-checked, nothing imported).** Any decision tree over the
consistency bits that correctly decides "some candidate rule is consistent" needs `≥ D` probes. The
adversary's instances are realized by genuine DSL behaviors (`cvec_id`, `cvec_rule`), so the bound
is not vacuous on this family. -/
theorem find_ge (t : DTree D Bool)
    (hcorrect : ∀ x, t.eval x = true ↔ ∃ i, x i = true) : D ≤ t.depth :=
  search_needs_n_queries t hcorrect

/-- **The abstraction find/check separation (machine-checked, nothing imported).** For a needle
family of `D ≥ 2` candidate DSL rules: verifying one claimed candidate costs a single probe
(`QueryGap.checkTree`, depth 1), while any prober deciding whether some candidate is consistent
needs `≥ D` probes — `check ≪ find` for a real abstraction family. An unconditional lower bound in
the query model, NOT a P-vs-NP separation. -/
theorem abstraction_check_lt_find (hD : 2 ≤ D) (j : Fin D) (t : DTree D Bool)
    (hcorrect : ∀ x, t.eval x = true ↔ ∃ i, x i = true) :
    (checkTree j).depth < t.depth :=
  check_lt_find hD j t hcorrect

end Sundog.AbstractionQueryGap

-- Axiom audit: deductive core uses only mathlib's foundational axioms. Mirrored in `AxiomAudit`.
#print axioms Sundog.AbstractionQueryGap.cbit_eq_verify
#print axioms Sundog.AbstractionQueryGap.cvec_rule
#print axioms Sundog.AbstractionQueryGap.find_ge
#print axioms Sundog.AbstractionQueryGap.abstraction_check_lt_find
