# H-IV SEARCH-SCALE RUN NOTE — the collapse regime is real at scale, but the cap map doesn't capitalize

**Frozen:** 2026-06-29, repo HEAD `master`. Run: `scripts/h4_search_whitebox.py --real
--regime reasoning --model Qwen/Qwen2.5-1.5B-Instruct --dtype float32` (operator PowerShell,
fp32). Pre-registration: `AGENTIC_TRACE_H4_SEARCH_SCALE_PREREG.md` (frozen before this run).
Analysis pinned on the synthetic dry-run (`scripts/test_h4_search_whitebox.py`, 6/6), which
this run reproduces (synthetic: score-recall 0, struct-recall 1, struct less redundant).
**Lane:** sundogcert agentic-trace slate, Hypothesis IV — the larger-model / longer-branch
re-run of the search white-box.

---

## Verdict

- **Pre-registered verdict: K-NULL-STRUCT-NOHELP-redundancy.** Two findings, separated:
  the **collapse regime now arises** (the failure mode H-IV targets is real at scale), but
  the **structural cap-slot fix does not realize an advantage** on real reasoning branches.

## What ran, what came out

8 multi-step arithmetic word problems, `K = 8` sampled reasoning chains each (96 tokens,
fp32), branches embedded over the full chain and quantized to `F₃³`; count-by-score vs the
structural line-free cap at matched admitted size `m`.

| metric | 0.5B short-answer (prior) | **1.5B reasoning (this run)** |
|---|---|---|
| `n_usable` | 5/6 | **8/8** |
| **`n_collapse`** (correct branch exists, top-score wrong) | **0** | **6/8** |
| mean score-redundancy | 0.95 | 0.962 |
| mean struct-redundancy | 0.92 | 0.955 |
| recall on collapse tasks (score / struct) | — (none) | 1.0 / 1.0 |
| all structural admissions are caps | yes | yes |

- **(0) The collapse regime AROSE — the failure mode is real at scale.** On **6 of 8** tasks
  the 1.5B model samples a correct multi-step solution but ranks a **wrong** branch highest
  (`top_score_correct = 0`, `any_correct = 1`). A budget-1 (greedy / top-logprob) search
  would pick the wrong answer and prune the sampled-but-low-ranked solution. This is exactly
  the regime the 0.5B short-answer run could not reach (`n_collapse = 0`); larger model +
  longer reasoning chains + harder tasks delivered it. **The premise of H-IV's Leg A — a
  count-by-score budget can prune the solution — is confirmed real on a live model.**
- **(i) but the structural fix does not beat count-by-score on recall:** both retain the
  solution on every collapse task (recall 1.0 vs 1.0). The matched admitted size `m` (5–7 of
  8, = the cap size) is **large**, so count-by-score at that budget also includes the
  correct branch — the top-1 is wrong, but the top-5+ is not. The fix's advantage would
  only bite at a **small** budget (m ≈ 1–2), which the cap-coordinate sizing does not
  produce here.
- **(ii) and the fix is not more diverse:** mean redundancy 0.962 (score) vs 0.955 (struct),
  a gap of **0.007** — far under the 0.05 bar. Even 96-token reasoning chains for the *same*
  problem are near-duplicate in embedding space (~0.95 cosine), so the `F₃³` cap map has
  almost no diversity to exploit. **The branch→cap-set map (the named import) is still
  degenerate** — longer branches did not fix it.

## Reading it honestly

This is a more informative null than the 0.5B one, and it splits the claim cleanly:

- **The phenomenon is real at scale.** The collapse regime — a sampled-but-mis-ranked
  solution — arises in 6/8 reasoning tasks. Count-by-score's top choice is wrong most of the
  time here; the thing H-IV says a budget can do (prune the winner) genuinely happens.
- **The structural cap-slot fix does not realize its advantage on real reasoning branches.**
  The synthetic pin shows the receipts *do* dissociate when branches occupy distinct
  coordinates (score-recall 0, struct-recall 1, less redundant) — so the instrument is
  sound. On real data the null is the **map**: same-problem reasoning chains are
  near-duplicate embeddings (redundancy ~0.95), so quantizing to `F₃³` yields no real
  diversity, and the cap-determined admitted size is too large to expose the small-budget
  regime where count-by-score actually fails. The fix's value is structural and real in
  principle; it is **not realized by this embedding→cap coordinate map** on real search.

## Bounds and the honest next step

One model (1.5B), one family, fp32, 8 tasks, `K = 8`, the PCA→`F₃³` map, recall measured at
the cap-determined (large) matched size. Two design facts the next prereg should fix to give
the structural fix a fair test: (a) measure recall at a **small fixed budget** (recall@1 /
recall@2), where count-by-score provably prunes the mis-ranked solution; and (b) a **faithful
branch→slot map** in which solution-bearing branches occupy genuinely distinct, line-free
slots — same-problem reasoning embeddings do not. Until such a map exists, the cap-set
realization of H-IV's fix remains the named, unrealized import; the deductive core
(`StructuralSlot`) and the falsifier stand unchanged.

## The cross-lane mirror (where H-IV sits)

- H-I/H-II/H-III empirical legs found their effect on a real model (H-III now clean at scale).
- **H-IV: the failure mode is confirmed real at scale (collapse 6/8), but the *fix's*
  empirical realization is bounded** — the cap coordinate map is degenerate on real reasoning
  embeddings, and the matched-budget metric does not isolate the regime where the fix would
  help. The deductive core proves a count cannot determine line-freeness; the open empirical
  question is whether a faithful, diversity-bearing slot map for real agent branches exists.
  That is the right negative knowledge: the problem H-IV targets is real, and the specific
  cap-set instrument does not yet capture it on live search.
