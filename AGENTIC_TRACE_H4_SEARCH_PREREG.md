# H-IV SEARCH WHITE-BOX PREREG — does count-by-score collapse where the structural slot stays diverse?

**Frozen:** 2026-06-29, repo HEAD `master`.
**Status:** PREREG — written and frozen BEFORE any real-search run or analysis. This is
the *empirical* leg that pushes H-IV to the end of the chain, the analog of the H-II
retrieval and H-III attention white-boxes. The deductive walls are shut (the falsifier,
the structural line-free fix `structural_slot_receipt.py`, and the Lean core
`StructuralSlot.lean`); the one remaining import named in
`AGENTIC_TRACE_H4_FALSIFIER_RESULT.md` is the **branch→cap-set map from real agent
search**. This prereg specifies that map and attacks it.
**Lane:** sundogcert agentic-trace slate, Hypothesis IV (Trace-Bounded Search Trees),
empirical premise.

**Standing discipline (binds this prereg):** pre-registered KILL criteria — a clean null
is a SUCCESS (it bounds H-IV); forward-generate only (declare metrics, thresholds, and the
branch each result selects BEFORE seeing data); deterministic analysis pinned on a
synthetic dry-run before any real branch touches it; cheap headless legs only (local 0.5B
CPU, no API); name the nearest prior, state the delta.

---

## §0 What is imported, and what this tests

The H-IV chain is closed and machine-checked: the count-by-score budget bounds the wrong
invariant; the structural fix admits on a line-free (cap-set) predicate; `StructuralSlot`
proves a count cannot determine line-freeness (`count_cannot_determine_structure`).

**Imported, not derived:** that a *real* agent search, mapped into a structural coordinate,
behaves this way — that count-by-score collapses onto redundant high-score branches (and
can prune the low-score solution), while a structural line-free admission keeps a diverse
set that retains the solution. This tests the *phenomenon* on real LLM search branches with
the very receipts the fix produced — not a claim about production agents.

## §1 The measurement map (frozen)

- **Model:** Qwen2.5-0.5B-Instruct (cached, CPU, free; same model as the H-I/H-II/H-III
  white-boxes).
- **Search:** for each of a fixed set of short-answer tasks (known ground-truth answer),
  sample `K = 8` candidate branches (completions, temperature 0.9), each with its sequence
  **logprob** (the agent's own score) and a **correct** flag (the known answer string
  appears in the branch).
- **Branch coordinate (the imported map):** mean-pool each branch's last-hidden-state
  embedding; PCA the `K` task-local embeddings to 3 components; **tercile-quantize** each
  component to `{0,1,2}` → a point in `F₃³`. (Per-task terciles, so coordinates capture
  within-task branch variation.)
- **Two admissions at matched size** `m` (= the structural receipt's admitted-cap size):
  - **count-by-score** (`branch_budget_receipt`): the top-`m` branches by logprob;
  - **structural line-free** (`structural_slot_receipt`): a greedy cap over the `F₃³`
    coordinates (admit iff it stays line-free), size `m`.

## §2 Metrics and claim (what a SUPPORT verdict asserts)

Per task: `score_recall` / `struct_recall` ∈ {0,1} (does the admitted set contain a correct
branch), and `score_redundancy` / `struct_redundancy` (mean pairwise cosine similarity of
the admitted branches' embeddings — high = near-duplicates). Aggregated over tasks:

(i) **Score-admission is redundant** — `mean score_redundancy − mean struct_redundancy ≥
0.05`: count-by-score collapses onto near-duplicate high-score branches; the structural
admission is more diverse.

(ii) **Structural admission retains solutions at least as well** — `mean struct_recall ≥
mean score_recall` over the tasks where the correct branch is **not** the single top-score
branch (the regime where the budgets can differ).

(iii) **The collapse is real** — on a non-trivial fraction (≥ ⅓) of tasks the correct
branch is **not** top-score, so count-by-score's redundancy actually costs recall.

SUPPORT = (i)+(ii)+(iii). This realizes the fix on real search: structural admission buys
diversity (and solution retention) where count-by-score collapses.

## §3 Verdicts and KILL criteria (declared before data)

- **K-SUPPORT** — (i)+(ii)+(iii) hold. The fix's advantage (diversity, retention) is real on
  this model/map (bounded: one 0.5B model, the PCA→F₃³ map).
- **K-NULL-NOEXPLORE** — the correct branch is the top-score one on ≥ ⅔ of tasks
  (precondition (iii) fails): count-by-score is already fine, so there is nothing to fix
  here. A SUCCESS that bounds H-IV (the failure mode does not arise on this task set).
- **K-NULL-STRUCT-NOHELP** — the structural admission is not more diverse (i fails) or does
  not retain solutions at least as well (ii fails): the PCA→F₃³ map does not realize the
  structural advantage. Bounds H-IV — the branch→cap-set map is not (this) justified.
- **K-ARTIFACT** — the structural receipt admits non-line-free sets, or the recalls are
  computed on mismatched sizes. Instrument fault.

Any K-NULL-* is a publishable bound, not a failure.

## §4 Analysis pin (dry-run before real data)

Before any model runs, the harness executes a **synthetic dry-run** on hand-built branches:
high-score near-duplicate WRONG branches (same coordinate) plus a low-score CORRECT branch
at a distinct coordinate. It asserts count-by-score admits the redundant wrong cluster
(misses the solution, high redundancy) while the structural cap admits the distinct correct
branch (retains it, low redundancy), and that the structural admitted set is line-free.
This pins the coordinate quantization, both receipts, the recall/redundancy metrics, and
the matched-size logic deterministically; the real run changes only the source of the
branches. Frozen as `scripts/test_h4_search_whitebox.py`.

## §5 Nearest prior / delta

- **Nearest prior:** diverse beam search / the failure of greedy/score-ranked decoding to
  retain correct low-probability continuations (Vijayakumar et al., diverse beam search);
  exploration-vs-exploitation in tree search. **Imported.**
- **Delta:** we do not propose a new decoder; we test whether a **structural line-free
  (cap-set) admission** — the H-IV fix `structural_slot_receipt` — realizes the
  diversity/retention advantage on real branches, read through the machine-checked
  `StructuralSlot` core. The H-IV analog of the H-II retrieval and H-III attention
  white-boxes.
