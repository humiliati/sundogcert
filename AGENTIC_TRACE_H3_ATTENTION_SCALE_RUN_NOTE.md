# H-III ATTENTION-SCALE RUN NOTE — the dissociation sharpens with scale

**Frozen:** 2026-06-29, repo HEAD `master`. Run: `scripts/h3_attention_whitebox.py --models
"Qwen/Qwen2.5-0.5B-Instruct,Qwen/Qwen2.5-1.5B-Instruct" --dtype float32` (CPU, fp32).
Pre-registration: `AGENTIC_TRACE_H3_ATTENTION_SCALE_PREREG.md` (frozen before this run).
Analysis pinned on the synthetic dry-run (`scripts/test_h3_attention_whitebox.py`, 7/7),
which reproduces the prior 0.5B `φ_sum` result exactly.
**Lane:** sundogcert agentic-trace slate, Hypothesis III — the scale re-run of the
attention white-box.

---

## Verdict

- **K-SUPPORT-SHARPENS** (on Qwen2.5-1.5B, the model larger than the 0.5B anchor). The
  gradient/curl dissociation sharpens with scale: the prior 0.5B marginal null was a
  small-model artifact, not a property of the phenomenon.
- This is a **2-point ladder** (0.5B → 1.5B); a 3B third point is stageable (operator) to
  extend the curve, but the prereg's verdict precondition (≥ 1 model > 0.5B) is met and
  passed.

## Results (φ_sum primary, injection vs length-matched benign, controlled best-gradient layer)

| model | layers | best L | gradient AUC | **curl AUC** | gap | fix benign-flags | verdict |
|---|---|---|---|---|---|---|---|
| Qwen2.5-0.5B | 24 | L13 | 0.973 | **0.653** | 0.320 | 0 | K-NULL-MARGINAL-PERSISTS |
| Qwen2.5-1.5B | 28 | L11 | 0.999 | **0.550** | 0.449 | 0 | **K-SUPPORT-SHARPENS** |

`curl_non_increasing = True` — the headline scaling readout (prereg §2.iv): the loop's
blindness **deepens** with scale.

- **(i) gradient carries it** — 1.5B gradient AUC 0.999 (≥ 0.85). ✓
- **(ii) loop is blind with margin** — 1.5B curl AUC **0.550**, cleanly below the 0.60 bar
  (and below the 0.5B's marginal 0.653). ✓
- **(iii) clean gap** — 0.999 − 0.550 = 0.449 (≥ 0.25). ✓
- **(iv) scaling trend** — curl AUC non-increasing across the ladder (0.653 → 0.550). ✓
- **(v) fix never false-flags** — the Hodge-split hierarchy receipt flags **0 benign**
  (short and matched) at L11; the loop receipt remains non-discriminating. ✓

The clean-dissociation layers (gradient ≥ 0.85 ∧ curl ≤ 0.70) also **broaden and move
earlier** with scale: 0.5B {12,13,15,18,19} (mid/late of 24) → 1.5B {3,6,7,9,11,12}
(early/mid of 28). The blind spot is not a single fragile layer at scale; it is a broad
band the model reaches sooner.

## The φ_mean secondary (pre-registered metric-sensitivity report)

`φ_mean = φ_sum/|span|` is **K-ARTIFACT at both scales** (benign-flags 37 @0.5B, 27 @1.5B):
per-token normalization **inverts** the authority ordering, because the system instruction
is a long span (low per-token attention) and the slot is shorter (higher per-token). So the
hierarchy receipt flags benign under `φ_mean`. **`φ_sum` (total attention mass to the
segment) is the faithful authority proxy; `φ_mean` is not a drop-in upgrade** — it changes
what "authority" means. The metrics disagree, and per prereg §3 the disagreement is reported
rather than silently resolved: the primary `φ_sum` carries the SUPPORT verdict; the `φ_mean`
artifact is a finding about the metric (token-sum, not token-mean, is the right authority
readout), not about the model.

## What this establishes (and bounds)

The H-III empirical leg is **promoted from marginal null to confirmed at scale**: on a real
model larger than the prior 0.5B, the prompt injection is a gradient (authority) move the
loop circulation is **cleanly** blind to (curl AUC 0.550), length-controlled, with a fix that
never false-flags benign — exactly the Hodge split `HierarchyHolonomy.hierarchy_separates_
what_loop_cannot` proves. The blind spot deepens with scale rather than washing out.

**Bounds (honest):** two model sizes (0.5B, 1.5B), one family (Qwen2.5), fp32, the same
prompts/map as the prior leg, `φ_sum` (token-sum). A 3B third point would confirm the trend
as a curve rather than a slope; it is operator-stageable
(`--models "Qwen/Qwen2.5-3B-Instruct" --dtype bfloat16`). This is the attention-landscape
claim, **not** a claim about production guardrails.

## The cross-lane mirror (now sharper)

H-I/H-II/H-III/H-IV all run falsifier → fix → Lean core → empirical leg, each landing the
statement its Lean core proves. H-III's empirical leg, which read *marginal* at 0.5B, reads
**clean at 1.5B**: *the injection lives in the gradient (authority) component, and the loop
circulation is blind to it* — the blind spot `hierarchy_separates_what_loop_cannot`
formalizes, now confirmed to **deepen with model scale**.
