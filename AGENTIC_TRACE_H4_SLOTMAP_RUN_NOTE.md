# H-IV SLOT-MAP RUN NOTE — the fix beats count-by-score at small budget with a faithful map

**Frozen:** 2026-06-29, repo HEAD `master`. Model run (operator PowerShell, fp32):
`--dump-branches h4_branches_15b.json --model Qwen/Qwen2.5-1.5B-Instruct`. Analysis (offline,
no model): `--analyze h4_branches_15b.json`. Pre-registration:
`AGENTIC_TRACE_H4_SLOTMAP_PREREG.md` (frozen before this run). Analysis pinned on the
synthetic dry-run (`scripts/test_h4_search_whitebox.py`, 10/10).
**Lane:** sundogcert agentic-trace slate, Hypothesis IV — the fair-test re-run delivering
items 1 (small-budget metric) and 2 (faithful slot map) the scale note named.

---

## Verdict

- **K-SUPPORT-FAIRTEST.** With the `whitened` (faithful) map and the small-budget `recall@k`
  metric, the structural diversity-constrained admission **beats count-by-score** at `k = 2`
  on the collapse tasks — the advantage the prior scale leg's large matched budget and
  degenerate map had masked. H-IV's structural fix is empirically real once fairly tested.

## Results (collapse-task means, `n_collapse = 6/8`; same 1.5B branches as the scale leg)

| map | recall@1 (score/struct) | recall@2 (score/struct) | recall@3 (score/struct) | **gap@2** | gap@3 |
|---|---|---|---|---|---|
| `embedding` (degenerate baseline) | 0.00 / 0.33 | 0.33 / 0.50 | 0.67 / 0.67 | +0.167 | +0.000 |
| **`whitened` (primary)** | 0.00 / 0.33 | 0.33 / **0.67** | 0.67 / 0.83 | **+0.333** | +0.167 |
| `answer` (near-ceiling) | 0.00 / 0.00 | 0.33 / 0.50 | 0.67 / 0.67 | +0.167 | +0.000 |

- **(i) small-budget retention gain** — under `whitened`, `struct recall@2 = 0.67` vs
  `score recall@2 = 0.33`: a **+0.333** gain (≥ 0.25), and **+0.167** at `k = 3`. The
  diversity-constrained admission retains the mis-ranked solution on **4/6** collapse tasks
  where count-by-score retains it on **2/6**. ✓
- **(ii) the faithful map buys it** — the whitened gain (+0.333 @2) **exceeds the
  `embedding` baseline** (+0.167 @2, +0.000 @3): whitening (centering away the dominant
  anisotropic direction) is what makes the slots separate the solution. ✓
- **(iii) instrument sound** — every admission is a cap; at `k = 1` score and struct tie on
  every map (the sanity floor). ✓

Per collapse task at `k = 2` (`score@2` vs `struct@2` under embedding/whitened/answer):

```
ans  28 : score@2=0  struct@2 e/w/a = 0/1/0   <- caught ONLY by whitened
ans 260 : score@2=0  struct@2 e/w/a = 1/1/1
ans 144 : score@2=1  struct@2 e/w/a = 1/1/1
ans 391 : score@2=0  struct@2 e/w/a = 0/0/0   <- correct branch low-logprob AND not slot-distinct
ans 145 : score@2=1  struct@2 e/w/a = 1/1/1
ans 140 : score@2=0  struct@2 e/w/a = 0/0/0
```

## Reading it honestly

- **The fix is real, at small budget, with a faithful map.** Spending a 2-branch budget on
  *distinct slots* rather than the two highest-logprob (same-slot, wrong) near-duplicates
  recovers the sampled-but-mis-ranked solution on twice as many collapse tasks (4 vs 2).
  This is the diverse-beam intuition, instantiated through the H-IV structural receipt and
  read through the machine-checked `StructuralSlot`.
- **A surprise: `whitened` beat the `answer` near-ceiling.** Diversity-*by-representation*
  outperformed diversity-*by-conclusion* (gap@2 +0.333 vs +0.167). Bucketing by the
  concluded integer spreads the budget across many *distinct wrong* answers (the model
  samples several different wrong numbers, each more confident than the low-logprob correct
  one), so its top-2 distinct-answer reps often miss; the whitened embedding instead floats
  a representationally-distinct correct branch into the top-2. The automatic, deployable map
  is the effective one — no ground-truth-adjacent feature needed.
- **The gain is at very small budgets and is modest in n.** It is +0.333 at `k = 2` and
  narrows to +0.167 at `k = 3` (count-by-score catches up as the budget grows toward the
  cap size — exactly why the scale leg's large matched budget saw no gap). 2/6 collapse
  tasks (391, 140) are caught by no map at `k = 2` (the correct branch is both low-logprob
  and not slot-separated).

## Bounds

One model (1.5B), one family, fp32, 8 tasks (6 collapse), `K = 8`, the PCA→tercile
coordinate; gains are small-n and concentrated at `k = 2`. The result establishes the fix's
advantage *exists and is map-dependent*, not its magnitude. Natural extensions (own prereg):
more tasks/branches for tighter intervals, a learned or contrastive embedding map, and a 3B
point. The `StructuralSlot` deductive core and the falsifier are unchanged; this closes the
empirical gap the scale leg left open.

## Where H-IV now sits

Across the legs: the falsifier fired, the fix landed, the Lean core landed, the 0.5B leg
found no collapse regime, the 1.5B scale leg found the collapse regime real but the fix
unrealized (large budget + degenerate map) — and this fair-test leg, fixing both, shows the
**structural fix beats count-by-score at small budget under a faithful (whitened) map**.
The failure mode is real and the fix capitalizes on it when measured correctly.
