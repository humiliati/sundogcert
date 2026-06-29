# H-IV SEARCH-SCALE PREREG — does the collapse regime arise (and the structural fix help) at scale + longer branches?

**Frozen:** 2026-06-29, repo HEAD `master`.
**Status:** PREREG — written and frozen BEFORE any larger-model / reasoning-regime run or
analysis. This is the **re-run** of the H-IV search white-box
(`AGENTIC_TRACE_H4_SEARCH_{PREREG,RUN_NOTE}.md`), whose 0.5B short-answer result was a clean
`K-NULL-NOEXPLORE` (double-confirmed): the failure mode H-IV targets — a count-by-score
budget pruning a *low-score correct* branch — never arose, because (a) when the 0.5B model
sampled a correct branch it was also top-ranked, and (b) short answers gave near-duplicate
embeddings, so the cap map was degenerate. The run note named the next leg: **long
multi-step search** on a **larger model**. This prereg covers it.
**Lane:** sundogcert agentic-trace slate, Hypothesis IV (Trace-Bounded Search Trees),
empirical premise — scale + longer-branch follow-up.
**Execution:** operator-staged for ≥ 3B; the 1.5B reasoning run is in-env-backgroundable.

**Standing discipline (binds this prereg):** pre-registered KILL criteria — a clean null is
a SUCCESS (it bounds H-IV); forward-generate only; deterministic analysis pinned on the
synthetic dry-run before any real branch touches it; name the nearest prior (the 0.5B
short-answer leg), state the delta.

---

## §0 What is imported, and what this tests

The H-IV chain is closed and machine-checked (falsifier, the structural line-free fix
`structural_slot_receipt`, the Lean core `StructuralSlot`: a count cannot determine
line-freeness). The 0.5B short-answer leg did not reach the regime where the count-vs-
structure gap can appear. This re-run targets that regime directly, fixing the two named
causes of the prior null:

- **larger model** (Qwen2.5-1.5B, optionally 3B) — capable enough to *sample* a correct
  multi-step solution sometimes, while still mis-ranking it on hard problems;
- **longer branches** (multi-step reasoning chains, not 1-token answers) — so branch
  embeddings are genuinely diverse and the `F₃³` cap map is not degenerate.

It tests whether, in this regime, (a) the **collapse regime arises** (a correct branch
exists but is not top-score) and (b) the **structural line-free admission** retains the
solution and stays more diverse where count-by-score collapses. This is imported, not
derived: that real reasoning search, mapped into the cap coordinate, behaves this way.

## §1 The measurement map (frozen)

- **Model:** `Qwen2.5-1.5B-Instruct` (primary; cached, > the prior 0.5B), and optionally
  `Qwen2.5-3B-Instruct` (operator-staged, `bfloat16` if it does not fit fp32 — recorded).
  A verdict requires the **1.5B** run.
- **Tasks:** 8 fixed **multi-step arithmetic word problems** with known **integer** answers
  (declared in the harness `REASONING_TASKS`), chosen at the edge of 1.5B competence (it
  solves some, mis-ranks others).
- **Search:** `K = 8` sampled reasoning chains per task (`max_new_tokens = 96`, temperature
  0.9, fixed seed), each with its sequence **logprob** (the agent's score) and a **correct**
  flag — the known integer appears as a standalone number (`\b<answer>\b`) in the chain.
- **Branch coordinate (the imported map):** mean-pool each chain's last-hidden-state
  embedding over the full chain; PCA the `K` task-local embeddings to 3 components;
  **tercile-quantize** to `F₃³`. (Longer chains ⇒ real embedding spread, unlike the prior
  short-answer degeneracy.)
- **Two admissions at matched size** `m` (= the structural receipt's admitted-cap size):
  count-by-score (`branch_budget_receipt`, top-`m` by logprob) vs the structural line-free
  cap (`structural_slot_receipt`, one representative per distinct coordinate, admitted
  line-free).

## §2 Metrics and claim (what a SUPPORT verdict asserts)

Per task: `top_score_correct` (is the highest-logprob branch correct), `any_correct`,
`score_recall` / `struct_recall` (does the admitted set contain a correct branch),
`score_redundancy` / `struct_redundancy` (mean pairwise cosine of admitted embeddings).
**Usable** = a correct branch exists; **collapse** = usable ∧ ¬top_score_correct.

(0) **Precondition — the collapse regime arises:** `n_collapse ≥ ⅓ · n_usable` (the prior
run had `n_collapse = 0`; reaching > 0 is the point of the re-run).

(i) **Structural retains the solution where score collapses:** mean `struct_recall ≥` mean
`score_recall` over the **collapse** tasks.

(ii) **Structural is more diverse:** mean `score_redundancy − struct_redundancy ≥ 0.05`
over the usable tasks (now testable — longer chains give embedding spread).

SUPPORT = (0)+(i)+(ii). The structural line-free admission buys solution-retention and
diversity in exactly the regime count-by-score collapses.

## §3 Verdicts and KILL criteria (declared before data)

- **K-SUPPORT** — (0)+(i)+(ii) hold. The fix's advantage is real in-regime (bounded:
  1.5B/3B, the PCA→`F₃³` map, these tasks).
- **K-NULL-NOEXPLORE-STILL** — (0) fails (`n_collapse < ⅓ n_usable`): even a larger model on
  multi-step tasks keeps its correct branch top-ranked. A SUCCESS that bounds H-IV harder —
  the failure mode is elusive even here.
- **K-NULL-STRUCT-NOHELP** — (0) holds but (i) or (ii) fails: the collapse regime arises yet
  the structural admission does not beat count-by-score (no retention gain, or not more
  diverse). Bounds H-IV — the cap map does not realize the advantage even in-regime.
- **K-ARTIFACT** — the structural receipt admits non-line-free sets, or recalls are computed
  on mismatched sizes. Instrument fault.

Any K-NULL-* is a publishable bound, not a failure.

## §4 Analysis pin (before real data)

The synthetic dry-run (`scripts/test_h4_search_whitebox.py`) already pins the coordinate
map, both admissions, and the recall/redundancy metrics on hand-built branches (high-score
WRONG near-duplicates + a low-score CORRECT distinct branch ⇒ count-by-score misses it,
structural keeps it, less redundant, line-free). The only executable additions this prereg
authorizes are: (a) the `REASONING_TASKS` set, (b) parameters `max_new_tokens` / `K` /
`model` / `dtype`, and (c) the standalone-number answer match. All must keep the synthetic
pin green before any real model runs; the real run changes only the model, the task set, and
the branch length.

## §5 Nearest prior / delta

- **Nearest prior:** the 0.5B short-answer H-IV leg (`AGENTIC_TRACE_H4_SEARCH_RUN_NOTE.md`):
  clean `K-NULL-NOEXPLORE` — the collapse regime never arose, diversity degenerate.
  **Imported as the baseline.**
- **Delta:** larger model + longer (multi-step) branches + harder tasks, to reach the
  collapse regime and give the cap map embedding spread to work with; same receipts, same
  metrics, read through the machine-checked `StructuralSlot`. The H-IV analog of the H-III
  attention-scale re-run.
