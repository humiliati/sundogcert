# H-IV SLOT-MAP PREREG — does a faithful map + small-budget metric let the structural fix beat count-by-score?

**Frozen:** 2026-06-29, repo HEAD `master`.
**Status:** PREREG — frozen BEFORE any run or re-analysis under the new map/metric. This is
the **fair-test re-run** the H-IV scale run note (`AGENTIC_TRACE_H4_SEARCH_SCALE_RUN_NOTE.md`)
named: the 1.5B reasoning leg confirmed the **collapse regime is real** (`n_collapse = 6/8`:
the model samples a correct multi-step solution but ranks a wrong branch top), yet returned
`K-NULL-STRUCT-NOHELP-redundancy` for two *design* reasons the note flagged as fixable —
(1) the cap-determined matched budget was too large to discriminate, and (2) the
embedding→`F₃³` map was degenerate (same-problem chains ~0.95 cosine). This prereg fixes
both and tests whether the structural fix then beats count-by-score.
**Lane:** sundogcert agentic-trace slate, Hypothesis IV (Trace-Bounded Search Trees),
fair-test follow-up.
**Execution:** the model run is operator-staged (`--dump-branches`); the analysis runs
offline on the dump (no model, no teardown risk).

**Standing discipline:** pre-registered KILL criteria (a clean null is a SUCCESS); forward-
generate only (metrics/thresholds/branches declared before data); analysis pinned on the
synthetic dry-run before any real branch; name the nearest prior, state the delta.

---

## §0 What is imported, and what this tests

Closed and machine-checked: the falsifier, the structural fix `structural_slot_receipt`, the
Lean core `StructuralSlot` (a count cannot determine line-freeness). The scale leg confirmed
the failure mode (count-by-score's top choice prunes the mis-ranked solution) is real at
1.5B but did not give the fix a fair test. **Imported, not derived:** that a *diversity-
bearing* structural admission, at a *small budget*, retains the mis-ranked solution better
than count-by-score on real reasoning search. This tests exactly that, with the same
receipts, on the same kind of branches.

## §1 The two fixes (frozen)

**Item 1 — small-budget metric.** For each task and budget `k ∈ {1, 2, 3}`:
- **count-by-score@k** = the top-`k` branches by sequence logprob;
- **structural@k** = a *diversity-constrained* top-`k`: the highest-logprob branch in each
  distinct line-free slot, taken best-logprob-first (one per slot, so the budget is spent
  across slots rather than on near-duplicates).
- `recall@k` = 1 iff the size-`k` admitted set contains a correct branch.
At `k = 1` the two are identical (both take the single top-logprob branch); they can differ
only at `k ≥ 2`, exactly where count-by-score spends budget on same-slot near-duplicates.

**Item 2 — faithful, diversity-bearing slot maps** (each branch → a point in `F₃³`):
- **`whitened`** (PRIMARY): per task, center the `K` embeddings (subtract their mean) and
  per-dimension standardize, then PCA→tercile→`F₃³`. Centering removes the dominant shared
  (anisotropic) direction that pins same-problem chains to ~0.95 cosine, so residual
  branch-specific variation gives genuine slot diversity.
- **`answer`** (SECONDARY / near-ceiling): bucket each branch by the **integer it concludes**
  (last integer in the chain) — the natural structural feature of a reasoning branch —
  assigning distinct concluded values to distinct points of a fixed `F₃³` cap. This is
  *diversity-by-conclusion*, computed with **no ground truth** (we bucket by what the branch
  *says*, not by correctness); it is the strongest faithful diversity signal and bounds what
  any map can buy.
- **`embedding`** (BASELINE): the prior raw PCA→tercile map (degenerate), for contrast.

The structural admission (`structural_slot_receipt`, one best-logprob rep per distinct
line-free slot) and count-by-score (`branch_budget_receipt`) are unchanged; only the
coordinate and the budget metric change.

## §2 Metrics and claim (what a SUPPORT verdict asserts)

On the **collapse tasks** (a correct branch exists, top-score wrong — the regime where the
budgets can differ):

(i) **small-budget retention gain** — mean `structural recall@k − count-by-score recall@k ≥
0.25` at some `k ∈ {2, 3}`, under the `whitened` (primary) map: the diversity-constrained
admission catches the mis-ranked solution where greedy's same-slot redundancy misses it.

(ii) **the faithful map buys it** — that gain **exceeds the `embedding`-baseline map's gain**
at the same `k`. The degenerate raw map does not produce the gain on its own; whitening (or
the answer-bucket) is what makes the slots meaningful. (Note: raw-embedding cosine stays
~0.95 under anisotropy regardless of which reps are picked, so admitted redundancy is *not*
a usable degeneracy gate — the recall-gain-over-baseline is. Admitted redundancy is reported
descriptively only.)

(iii) **the instrument is sound** — every structural admission is a genuine cap, and at
`k = 1` the two admissions tie (a sanity floor: they take the same single top-logprob branch).

SUPPORT = (i)+(ii)+(iii) on `whitened`. The `answer` map is the near-ceiling: if even
diversity-by-conclusion does not beat count-by-score at small budget, the failure is the
metric/branches, not the map.

## §3 Verdicts and KILL criteria (declared before data)

- **K-SUPPORT-FAIRTEST** — (i)+(ii)+(iii) on the `whitened` map. The structural fix beats
  count-by-score at small budget once the map is faithful: H-IV's fix is empirically real.
- **K-PARTIAL-ANSWER-ONLY** — `whitened` fails (i) but the `answer` map reaches the ≥ 0.25
  gain over baseline. Diversity-by-conclusion works; the automatic embedding proxy does not.
  A partial positive that localizes the remaining gap to the embedding→slot map.
- **K-NULL-NO-SMALLBUDGET-GAP** — no faithful map (`whitened` or `answer`) reaches a ≥ 0.25
  gain over the `embedding` baseline at `k ∈ {2,3}`. Bounds H-IV: even diversity-by-conclusion
  at small budget does not retain the mis-ranked solution better than count-by-score here.
- **K-NULL-NOEXPLORE-STILL** — `n_collapse < ⅓ · n_usable` on this run (the collapse regime
  did not reappear). Re-bounds the regime.
- **K-ARTIFACT** — non-cap admissions, mismatched `k`, or a map that leaks correctness.

Any K-NULL-* is a publishable bound.

## §4 Analysis pin (before real data)

The synthetic dry-run is extended: hand-built branches where the high-logprob branches are
near-duplicate WRONG (one slot) and a lower-logprob CORRECT branch sits in a distinct slot.
The pin asserts, on the faithful maps, `count-by-score recall@2 = 0` (greedy stays in the
wrong slot) while `structural recall@2 = 1` (diversity reaches the correct slot), `recall@1`
ties, all admissions are caps, and `whitened` redundancy < `embedding` redundancy. The
`answer`-bucket coordinate is pinned to map distinct concluded integers to distinct cap
points. These must pass before any real branch is analyzed.

## §5 Run architecture and nearest prior

- **Architecture:** `--dump-branches <file>` runs the 1.5B reasoning regime once (operator
  PowerShell, with `HF_TOKEN` set per `Dev\AGENTS.md`) and saves the raw branches (logprob,
  correctness, concluded integer, embedding). `--analyze <file>` then computes all maps +
  `recall@k` offline, with no model — so the expensive, teardown-prone model run happens
  once and the analysis iterates freely.
- **Nearest prior:** the H-IV scale leg (`…SCALE_RUN_NOTE.md`): collapse real, fix
  unrealized due to (1) large matched budget and (2) degenerate map. **Delta:** a small-
  budget `recall@k` metric and faithful (`whitened`, `answer`) maps — exactly the two items
  the scale note named — read through the unchanged `structural_slot_receipt` /
  `StructuralSlot`. Nearest external prior: diverse beam search (Vijayakumar et al.) — the
  known result that diversity beats greedy under mis-calibration; imported, not re-derived.
