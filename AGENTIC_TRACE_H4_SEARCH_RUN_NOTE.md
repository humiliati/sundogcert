# H-IV SEARCH WHITE-BOX RUN NOTE — a clean null: the collapse regime does not arise

**Frozen:** 2026-06-29, repo HEAD `master`. Run: `scripts/h4_search_whitebox.py --real`
on Qwen2.5-0.5B-Instruct (CPU, ~2.5 min, free). Pre-registration:
`AGENTIC_TRACE_H4_SEARCH_PREREG.md` (frozen before this run). Analysis pinned on the
synthetic dry-run (`scripts/test_h4_search_whitebox.py`, 4/4) before any real branch
touched it.
**Lane:** sundogcert agentic-trace slate, Hypothesis IV — the empirical leg that pushes
H-IV to the end of the chain, the analog of the H-II retrieval and H-III attention
white-boxes.

---

## Verdict

- **Pre-registered verdict: K-NULL-NOEXPLORE — double-confirmed (easy AND hard tasks).**
  Per §3 this is a SUCCESS that bounds H-IV: the failure mode the hypothesis targets — a
  count-by-score budget pruning a *low-score* solution branch — **does not arise** for this
  model/regime, so there is nothing for the structural fix to improve here.

## What ran, what came out

Two task sets (6 easy short-answer, 6 hard arithmetic/factual), `K = 8` sampled branches
each, scored by sequence logprob, embedded and quantized to `F₃³` (PCA→tercile), then
admitted two ways at matched size: count-by-score (top-m by logprob) vs the structural
line-free cap (`structural_slot_receipt`).

| set | usable | collapse (top-score wrong) | mean score-redundancy | mean struct-redundancy |
|---|---|---|---|---|
| easy | 5/6 | **0** | 0.945 | 0.922 |
| hard | 5/6 | **0** | 0.963 | 0.951 |

- **The collapse regime never occurs.** On *every* usable task in *both* sets,
  `top_score_correct = 1`: whenever a correct branch is sampled, it is also the
  highest-logprob branch. Tasks the model fails (e.g. "7th prime", "9×13" varied) have **no**
  correct branch at all (`any_correct = 0`) — a competence failure, not a ranking failure.
  So count-by-score is never the bottleneck: `score_recall == struct_recall` on every task.
- **Diversity is degenerate at this branch length.** Short answers give near-duplicate
  embeddings (redundancy ≈ 0.95 for *both* admissions); the structural cap is only
  marginally more diverse (≈ 0.015), well under the 0.05 SUPPORT bar. The `F₃³` map over
  short-text embeddings has little structure to exploit — the branch→cap-set map is **not
  realized** in this regime (the named import, unconfirmed here).
- **Instrument sound.** Every structural admission is a genuine cap (`all_struct_caps =
  True`); the synthetic pin (where a low-score correct branch *is* present) shows the
  intended dissociation — count-by-score misses it, the structural cap retains it, less
  redundant. So the null is about the data regime, not the receipt.

## Reading it honestly

This is a clean, pre-registered, double-confirmed null. The deductive core stands
(`StructuralSlot`: a count cannot determine line-freeness; the falsifier's Leg A/B against
the live receipt). What the empirical leg shows is that **eliciting the failure mode needs a
regime this setup does not reach**: a model that *samples* a correct branch but ranks it
*below* incorrect ones, among *genuinely diverse* branches. A 0.5B model on short-answer
tasks is not that regime — its branch ranking is calibrated (correct ⇒ top-score) and its
branches are near-duplicates. When count-by-score is adequate, the structural fix has
nothing to add; H-IV's value is bounded to the regimes where ranking *fails*, which remain
to be exhibited.

## Bounds (honest)

One 0.5B model; short-answer tasks with `K = 8` branches; the PCA→`F₃³` quantization is one
choice and is degenerate on short branches. The failure mode H-IV targets is expected in
**long multi-step search** (code/proof/planning trees) where a correct continuation is
genuinely low-probability among diverse branches and explosion is real — a larger-model,
longer-branch re-run (own prereg, operator PowerShell) is the natural next leg. The
synthetic pin demonstrates the receipts behave as designed *when* the regime is present.

## The cross-lane mirror (and where it breaks)

- H-I: the override is internally legible, externally illegible (probe 0.99 vs entropy 0.54).
- H-II: the retrieval barrier really forms and annihilates on real embeddings.
- H-III: the injection really is a gradient move the loop is near-blind to (length-controlled).
- **H-IV: the targeted failure mode does not arise here** — a clean null. Three lanes found
  their effect on a real model (with honest caveats); the fourth bounds the regime in which
  its effect can appear. The deductive cores are uniform (the proxy cannot determine the
  structure); the empirical legs are honestly heterogeneous — H-IV's says *when the proxy is
  already adequate, the fix is not needed*, which is exactly the right negative knowledge.
