/-
# Abstraction-task certificate — the find/check ledger's program-synthesis instance (FC-1)

The find/check ledger (`Certifies`/`Ledger`, `ShortestPathCert`, `QueryGap`) gets its
**abstraction / program-synthesis-from-examples** instance — the object ARC-style tasks live on.
An *abstraction task* is a list of input→output training grids; a *candidate program* from a tiny
total DSL is the witness; the **CHECK** is "the program reproduces every training pair," a cheap
straight-line evaluation (`O(|task|·evalCost p)`). *Finding* a consistent program is the imported
search wall, and — the abstraction-specific wall — consistency on the training pairs does **not**
pin the program: `train_underdetermines` exhibits two distinct programs that pass the same CHECK
yet disagree on a held-out input.

This is the Lean realization of slate hook **FC-1**
(`docs/findcheck/FIND_CHECK_SUFFICIENCY_SLATE.md`).

## What is PROVED here (the CHECK — everything about the toy, nothing about ARC itself)
* `eval` is a TOTAL, structural DSL evaluator (no unbounded fixpoint); `eval_comp` gives the
  composition semantics that make the DSL load-bearing (not a restatement of the cost interface).
* `verify_iff` — the CHECK is exactly "consistent with every training pair," decidable.
* `verify_planted` — the CHECK ACCEPTS the program that generated a task (completeness).
* `train_underdetermines` (**headline**) — a task + two distinct programs both passing CHECK but
  disagreeing off-train: the training evidence does not determine the program. The find/check
  analog of `ParityNoSufficientStat.partial_not_sufficient` — a cheap CHECK does not pin the answer.
* `cost_le` — the CHECK costs `|task|·(evalCost p + 1) + 1`, routed through the shared
  `Certifies`/`StraightLineCost` ledger: the find/check ledger's program-synthesis instance.

## The walls (named, NOT proved here)
* **FIND**: searching the DSL for a consistent program (program synthesis) is the hard side —
  imported, as in every ledger instance.
* **GENERALIZATION (the ARC wall)**: a CHECK-passing program need not be correct on a held-out
  test input (`train_underdetermines` witnesses the under-determination). This is *why* ARC is
  hard; it is named here, not resolved. No claim about cracking ARC.
-/
import Sundogcert.Certifies

namespace Sundog.AbstractionCert

/-- A colored grid: rows of natural-number color cells. -/
abbrev Grid := List (List ℕ)

/-- A tiny abstraction DSL over grids — total and structural (no unbounded fixpoint). -/
inductive Prog
  | id
  | recolor (a b : ℕ)
  | flipH
  | flipV
  | comp (p q : Prog)
  deriving DecidableEq

/-- Total structural evaluation of a program on a grid (recursion on the program). -/
def eval : Prog → Grid → Grid
  | .id,          g => g
  | .recolor a b, g => g.map (fun row => row.map (fun c => if c = a then b else c))
  | .flipH,       g => g.map List.reverse
  | .flipV,       g => g.reverse
  | .comp p q,    g => eval p (eval q g)

@[simp] theorem eval_id (g : Grid) : eval .id g = g := rfl

@[simp] theorem eval_comp (p q : Prog) (g : Grid) :
    eval (.comp p q) g = eval p (eval q g) := rfl

/-- An abstraction task: input→output training grid pairs. -/
abbrev Task := List (Grid × Grid)

/-- **The CHECK.** A candidate program reproduces every training pair. Decidable; one evaluation
and one grid-compare per pair. -/
def Verify (p : Prog) (task : Task) : Bool :=
  task.all (fun io => decide (eval p io.1 = io.2))

/-- **CHECK soundness + completeness.** `Verify` holds iff the program reproduces every pair. -/
theorem verify_iff (p : Prog) (task : Task) :
    Verify p task = true ↔ ∀ io ∈ task, eval p io.1 = io.2 := by
  simp only [Verify, List.all_eq_true, decide_eq_true_eq]

/-- **The CHECK accepts the generator (completeness on a generated task).** A task whose outputs
were produced by a program `g` is verified by `g`. -/
theorem verify_planted (g : Prog) (inputs : List Grid) :
    Verify g (inputs.map (fun i => (i, eval g i))) = true := by
  rw [verify_iff]
  intro io hio
  simp only [List.mem_map] at hio
  obtain ⟨i, _, rfl⟩ := hio
  rfl

/-- **The training evidence under-determines the program (the abstraction wall, witnessed).**
There is a task and two DISTINCT programs that both pass `Verify` yet DISAGREE on a held-out
input. The find/check analog of `ParityNoSufficientStat.partial_not_sufficient`: a cheap CHECK
does not pin the answer. (`id` and `recolor 1 2` agree on a grid with no color `1` but differ on
one that has it.) -/
theorem train_underdetermines :
    ∃ (task : Task) (p q : Prog) (held : Grid),
      p ≠ q ∧ Verify p task = true ∧ Verify q task = true ∧ eval p held ≠ eval q held :=
  ⟨[([[0]], [[0]])], .id, .recolor 1 2, [[1]], by decide, by decide, by decide, by decide⟩

/-! ## The verification cost — and the find/check ledger instance -/

/-- A transparent structural op-count of one `eval`. -/
def evalCost : Prog → ℕ
  | .id => 1
  | .recolor _ _ => 1
  | .flipH => 1
  | .flipV => 1
  | .comp p q => evalCost p + evalCost q

/-- An abstraction-certificate instance: a task and a candidate program. -/
structure ACInstance where
  task : Task
  prog : Prog

/-- The CHECK cost: one evaluation + one compare per training pair, plus a final tally. -/
def ACInstance.verifyCost (I : ACInstance) : ℕ := I.task.length * (evalCost I.prog + 1) + 1

/-- The abstraction certificate plugs into the shared find/check ledger — its
program-synthesis instance. -/
instance acCertifies : Certifies.Ledger ACInstance where
  program I := StraightLineCost.StraightLineProgram.ofCost I.verifyCost

/-- **Checking is cheap (`O(|task|·evalCost p)`).** Verifying a candidate against the training
pairs costs `|task|·(evalCost p + 1) + 1` operations — the cheap-CHECK half; *finding* a
consistent program is the imported wall. -/
theorem cost_le (I : ACInstance) :
    Certifies.checkCost I ≤ I.task.length * (evalCost I.prog + 1) + 1 := le_refl _

end Sundog.AbstractionCert

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (and `train_underdetermines` is a `decide` witness — axiom-light). Mirrored in `AxiomAudit`.
#print axioms Sundog.AbstractionCert.verify_iff
#print axioms Sundog.AbstractionCert.verify_planted
#print axioms Sundog.AbstractionCert.train_underdetermines
#print axioms Sundog.AbstractionCert.cost_le
