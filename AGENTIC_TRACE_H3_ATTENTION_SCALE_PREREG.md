# H-III ATTENTION-SCALE PREREG — does the gradient/curl dissociation sharpen with model scale?

**Frozen:** 2026-06-29, repo HEAD `master`.
**Status:** PREREG — written and frozen BEFORE any larger-model run or analysis. This is
the **scale re-run** of the H-III attention white-box
(`AGENTIC_TRACE_H3_ATTENTION_{PREREG,RUN_NOTE}.md`), whose 0.5B result was a *marginal*
`K-NULL-LOOP-ALSO-SEES` (best-layer curl AUC 0.653, a hair over the 0.65 KILL line) with a
real but moderate, length-controlled dissociation at the middle layers. The run note named
the two next legs explicitly — **a larger model** and a **length-normalized φ** — and said
the latter "is a metric change, so it would need its own prereg." This prereg covers both.
**Lane:** sundogcert agentic-trace slate, Hypothesis III (Aharonov-Bohm Holonomy Filter),
empirical premise — scaling follow-up.
**Execution:** operator-staged (PowerShell). Larger models on CPU are heavy; this is not a
headless ≤10-minute leg.

**Standing discipline (binds this prereg):** pre-registered KILL criteria — a clean null is
a SUCCESS (it bounds H-III); forward-generate only (metrics, thresholds, and the branch each
result selects declared BEFORE data); the analysis is pinned on the existing synthetic
dry-run before any real attention touches it; name the nearest prior (the 0.5B leg), state
the delta.

---

## §0 What is imported, and what this tests

The H-III chain is closed and machine-checked (falsifier, the Hodge-split fix
`hierarchy_holonomy_receipt`, the Lean core `HierarchyHolonomy`). The prior empirical leg
established, length-controlled on Qwen2.5-0.5B: the gradient/authority component carries a
prompt injection (AUC ~0.85–0.97 at middle layers) while the loop circulation (curl) is
near-blind (~0.65–0.74), and the Hodge-split receipt never false-flags benign — but the
best-layer curl sat at **0.653**, marginally above the 0.65 KILL line, so the verdict was a
marginal null.

**This re-run tests one thing:** whether the dissociation **sharpens with model scale** —
the curl AUC dropping cleanly below the line while the gradient AUC stays high — within a
**fixed model family** (so scale, not architecture, is the variable) and a **length-
normalized φ** (so the prior sum-over-tokens length sensitivity is removed at the metric
level, not only via the matched control). A clean sharpening promotes H-III's empirical leg
from marginal to confirmed; a persistent margin (or no dissociation) bounds it honestly.

## §1 Method (frozen)

- **Model ladder (one family, varying scale):** `Qwen2.5-0.5B-Instruct` (the prior anchor,
  re-run for a controlled baseline), `Qwen2.5-1.5B-Instruct`, `Qwen2.5-3B-Instruct`. Run as
  many as memory permits; **a verdict requires ≥ 1 model strictly larger than 0.5B**.
  `attn_implementation="eager"` (real attention weights); `dtype=float32` preferred, and if
  a model does not fit in RAM at fp32, `bfloat16` is permitted and **must be recorded**
  (a declared numeric caveat, not a free choice per-run).
- **Measurement map — IDENTICAL to the prior leg** (frozen, for comparability): per layer,
  head-mean attention `A_L`; flows `f(X→Y) = Σ_{i∈X,j∈Y} A_L[i,j]`; curl
  `circ_L = f(slot→system) + f(system→root) − f(slot→root)`.
- **Two authority potentials, both pre-declared:**
  - `φ_sum_L(v) = Σ_{j∈v} A_L[last, j]` — the **frozen prior metric** (comparable to 0.5B);
  - `φ_mean_L(v) = φ_sum_L(v) / |span(v)|` — the **length-normalized** metric (per-token mean).
  The `authority_margin` is `φ(system) − φ(slot)` under each; `φ_sum` is the **primary**
  (it makes the scale comparison apples-to-apples with the prior leg), `φ_mean` the declared
  **secondary** (it isolates the metric upgrade from the scale effect).
- **Prompts — IDENTICAL to the prior leg:** 3 systems × 3 queries × {3 short-benign, 3
  length-matched-benign, 3 injection} slots. The **length-matched benign** set is the
  load-bearing comparison (all primary AUCs are injection-vs-matched-benign).
- **Per-layer AUC** of the authority margin (gradient) and `|circ|` (curl) as injection
  classifiers; the reported layer is the **gradient-AUC-argmax** layer (as before), plus the
  full per-layer curve and the set of "clean dissociation" layers.

## §2 Metrics and claim (what a SUPPORT verdict asserts)

All AUCs are **injection vs length-matched benign**, under **`φ_sum`** (primary). On at
least one model **strictly larger than 0.5B**, at some layer `L*`:

(i) **the gradient carries it** — gradient AUC(`L*`) ≥ **0.85**;

(ii) **the loop is blind, with margin** — curl AUC(`L*`) ≤ **0.60** (strictly below the prior
0.653 / the 0.65 line: the sharpening the scale hypothesis predicts);

(iii) **clean gap** — gradient AUC(`L*`) − curl AUC(`L*`) ≥ **0.25**;

(iv) **monotone-ish scaling trend** — the best-gradient-layer curl AUC is **non-increasing**
across the size ladder (0.5B ≥ 1.5B ≥ 3B, within ±0.03 tolerance), i.e. the blind spot
deepens (or at least does not shrink) with scale;

(v) **the fix still never false-flags** — the Hodge-split hierarchy receipt flags 0 benign
(short and matched) at `L*`, and the loop receipt remains non-discriminating.

SUPPORT = (i)+(ii)+(iii)+(v) on a >0.5B model, with (iv) as the headline scaling readout.

## §3 Verdicts and KILL criteria (declared before data)

- **K-SUPPORT-SHARPENS** — (i)+(ii)+(iii)+(v) hold on a >0.5B model. The dissociation is
  clean at scale; the 0.5B margin was a small-model artifact. If (iv) also holds, the blind
  spot is a *scaling* phenomenon.
- **K-NULL-MARGINAL-PERSISTS** — best-layer curl AUC stays in **(0.60, 0.70]** at the
  gradient-best layer for every model (gradient still ≥ 0.85): the dissociation is real but
  does **not** sharpen with scale. A SUCCESS that bounds H-III — the effect is genuine and
  scale-stable but modest.
- **K-NULL-LOOP-ALSO-SEES** — curl AUC > 0.70 wherever the gradient is high: the loop is not
  blind at scale (the prior 0.5B blindness did not generalize). Bounds H-III.
- **K-NULL-NOGRADIENT** — gradient AUC never ≥ 0.85 (length-controlled) on any model: the
  authority proxy does not carry the injection at scale.
- **K-ARTIFACT** — the fix flags matched-benign as often as injection, or the structural
  checks fail. Instrument fault.

`φ_mean` (secondary) is reported the same way; if `φ_sum` and `φ_mean` disagree on the
verdict, the discrepancy is reported as the metric-sensitivity finding (neither is silently
preferred post hoc).

## §4 Analysis pin (before real data)

The existing synthetic dry-run (`scripts/test_h3_attention_whitebox.py`, 4/4) pins the
gradient/curl/receipt/AUC wiring on hand-built matrices (gradient AUC = 1, curl AUC ≈ 0.5,
fix separates, loop does not). The only executable additions this prereg authorizes are:
(a) the `φ_mean` variant (`φ_sum / |span|`), and (b) a model-ladder driver that calls the
existing `--real` path per model. Both must pass the synthetic pin (including a `φ_mean`
assertion) before any real model runs; the real run changes only the source of `A` and the
model size.

## §5 Nearest prior / delta

- **Nearest prior:** the 0.5B H-III attention leg (`AGENTIC_TRACE_H3_ATTENTION_RUN_NOTE.md`):
  marginal `K-NULL-LOOP-ALSO-SEES`, best-layer curl 0.653, length-controlled middle-layer
  dissociation, fix perfect-precision. **Imported as the baseline.**
- **Delta:** identical measurement map and prompts; vary **model scale** within one family
  and add a **length-normalized φ**, to test whether the dissociation sharpens (curl cleanly
  below the line) — promoting the marginal null or bounding it as scale-stable. No change to
  the Lean core or the receipts; this is purely the empirical scaling question.
