# H-I cliff — open-weight generality + the instrumentation-portability finding (2026-06-30)

**Status:** black-box generality sweep COMPLETE (Groq free tier, ~330 calls, $0). Extends the
banked cliff-transfer campaign (`AGENTIC_TRACE_H1_CLIFF_TRANSFER_RUN_NOTE.md`) from 2 OpenAI stacks
to 8 stacks across 3 families and 8B–70B. This is the behavioral-level answer to the deep-research
report's hypothesis #7 ("verdicts are instrumentation-limited, not phenomenon-limited"); the
white-box half (internal legibility) is in the run note and stays GPU-gated.

Data: `results/h7_groq_scout/scout_llama.json`, `results/h7_groq_scout/scout_reasoning.json`.

---

## Finding 1 — the volume-override cliff is a weak-model artifact, not a general phenomenon

The v2 authority-vs-volume task (one designated authority states a fact; a fraction λ of unflagged
field reports contradict it; the model must choose) run across the open-weight zoo:

| stack | family / size | O(λ) behaviour | cliff? |
|---|---|---|---|
| gpt-3.5-turbo | OpenAI (banked) | graded override, λ*≈0.58 | **yes** (graded) |
| gpt-4o-mini | OpenAI (banked) | O caps ~0.33, no crossover | no |
| llama-3.1-8b-instant | Llama 3.1, 8B | 0 until λ=1.0→0.33 | no |
| llama-4-scout-17b | Llama 4, 17B | 0 until λ=1.0→0.33 (see Finding 2) | no |
| llama-3.3-70b-versatile | Llama 3.3, 70B | 0 at every λ | no |
| qwen3-32b | Qwen3, 32B | 0 at every λ | no |
| qwen3.6-27b | Qwen 3.6, 27B | 0 at every λ | no |
| openai/gpt-oss-20b | GPT-OSS, 20B | 0 until λ=0.75→0.20, 1.0→0.40 | no |

**7 of 8 stacks are robust.** Only gpt-3.5-turbo — the oldest, weakest instruction-follower — is
outvoted by volume. Every current open-weight model, across three families and 8B→70B, honours the
authority designation even at 100% contradiction. The cliff is capability/era-bounded, not universal,
and it is not a within-family scale threshold (8B is already robust). This **bounds H-I's empirical
premise**: the phenomenon its syndrome-gate was meant to catch is largely gone in current models.

## Finding 2 — the verdicts ARE instrumentation-limited (hypothesis #7, confirmed on the hard cases)

The sweep surfaced four concrete measurement-portability frictions — the exact "instrumentation-limited
rather than phenomenon-limited" concern, made empirical:

1. **Cloudflare UA fingerprint.** Groq fronts its API with Cloudflare, which 1010-blocks `urllib`'s
   default User-Agent on the chat POST (list-models GET passes). The adapter's app UA clears it, but
   `cliff_transfer_task_v2.probe` calls `chat_once` with **no 429 backoff** and dies on the free-tier
   rate limit; only the `ApiModelAdapter` path (exponential backoff + `CallBudget`) survives.
2. **qwen inline `<think>` mis-score.** Qwen reasoning models emit `<think>…</think>\n\nAnswer` in
   `content`; `score_o` matches the *first* whole-word answer token, so it scores a mention mid-reasoning
   instead of the conclusion. Fix: strip through `</think>` before scoring.
3. **gpt-oss separate `reasoning` field + truncation.** GPT-OSS reasons in a dedicated `reasoning`
   field with the answer in `content`; at a naive token cap it hits `finish_reason=length` still
   reasoning, leaving `content` empty → scored malformed. Fix: read `content` (not `reasoning`), set
   `reasoning_effort=low`, raise the token budget.
4. **llama-4-scout format non-compliance.** Even in the direct-answer harness, ~50% of Scout's replies
   don't fit the one-word format (malformed) — a real model whose behaviour the current harness cannot
   read at all.

With the model-aware harness (per-family parsing + backoff + budget), the scorable models drop to
**malformed=0, truncated=0**. So the naive uniform harness would have produced artifact verdicts
(mis-scores, malforms) that a portable harness dissolves — a direct, if modest, confirmation of #7 on
the reasoning-model cases. (Finding 4 is the residual: some behaviour is un-scorable by *any* terse
harness.)

## Finding 3 — white-box internal legibility holds across the low-end scale ladder (local GPU, $0)

Local GTX-1080 harvest (fp16, n=30, full 9-λ grid; `results/whitebox_local_ladder/`) of the Qwen2.5
{0.5B, 1.5B, 3B} ladder, analysed offline (`scripts/whitebox_harvest.py` + `whitebox_analyze.py`):

| model | O-rate | cliff λ* | hidden-probe AUC | same-model entropy AUC |
|---|---|---|---|---|
| Qwen2.5-0.5B | 0.46 | 0.64 | **0.998** | 0.658 |
| Qwen2.5-1.5B | 0.39 | 0.68 | **0.998** | 0.658 |
| Qwen2.5-3B | 0.23 | 0.86 | **1.000** | 0.741 |

- Internal legibility is near-perfect at every size and **does not fade with scale** → the 0.5B result
  (AUC 0.994 in the run note) generalizes across the low end.
- The cliff itself **fades with capability** (O-rate 0.46→0.23, λ* rising) — a within-Qwen2.5 gradient
  consistent with the black-box finding (small Qwen2.5 caves; large Qwen3-27/32B robust). Note the
  local *small* Qwen2.5 models DO show the override that the Groq-hosted *large* Qwen3 did not.
- The same-model entropy AUC here (0.66–0.74, full-vocab first-token) is higher than the run note's
  0.537 (a narrower proxy) and the API's ~0.50 — the "external signal" magnitude is itself
  instrument-definition-dependent (on-theme for #7). Internal (~1.0) dwarfs every external estimator,
  so the internal≫external gap is robust to the definition.

## Finding 4 — cross-stack transfer: the adoption axis is scale-invariant within family

Paired-trial CCA (n≈270; each model runs the identical corpus seeds → trials are paired; PCA-50
pre-reduction then held-out canonical correlation, so it is well-posed — random inputs give ~0 at this
N): canonical correlations ~0.97–0.999 and adoption-axis transfer AUC **0.81–0.83** across all three
Qwen2.5 size pairs. An "about-to-adopt" direction trained on one size predicts adoption in another.
Caveat: the high canonical correlation partly reflects shared task-structure (λ) encoding; the transfer
AUC (predicting O) is the decision-specific number. Cross-*family* transfer (Qwen↔Llama) and 7B–70B
scale are untested here — that is the rented box's remaining, narrowed contribution.

## Cross-reference — the white-box half (0.5B banked; low end now local; 7B–70B GPU-gated)
The run note's white-box probe (Qwen2.5-0.5B, same forward pass) found the override is
**internally legible** (hidden-state linear probe AUC → 0.994) while the model's **output uncertainty
carries no signal** (same-model entropy AUC 0.537). Together with Finding 1–2 the #7 picture is:
behavioral/API instruments are phenomenon-bounded for the *observable* (theorem-backed by
`no_word_function_determines_decisive`); internal instruments escape that bound; and even the
behavioral verdicts that exist are instrument-sensitive on the reasoning-model cases. Whether internal
legibility holds at 7B–70B is the one open piece, and it needs GPU (CPU-only repo caps local white-box
at ~0.5B).

---

## Promo / webdev handoff seed (owner-gated; nothing deployed)

**Keep-true guardrails (do not cross):**
1. This is a **bound**, not a capability claim: "the volume-override cliff is largely absent in current
   models" — not "Sundog fixes it." H-I's gate is *less needed* because the phenomenon receded, which is
   an honest negative that bounds the lane.
2. Free-tier scout (n≤6/λ): **directional, not powered.** The banked powered numbers are the OpenAI
   n=30 run; the open-weight rows are a scouting sweep. Say "scouting sweep across 6 open-weight models,"
   not "benchmarked."
3. The instrumentation finding is the transferable one: **"the same behavioral question needs
   model-specific measurement; a naive uniform harness produces artifact verdicts."** That generalizes
   beyond this task and is the citable methods contribution.
4. Don't overstate the white-box "0.994" — it's one 0.5B model; scale generality is unproven.

**Paste-ready framing (one paragraph):**
> Across eight model stacks spanning three families and 8B–70B, the "outvoted by volume" failure the
> monitor targets appears on only the oldest, weakest instruction-follower; every current open-weight
> model honours the designated authority even at total contradiction. The harder finding is
> methodological: reading that verdict correctly required model-specific instrumentation — stripping
> inline reasoning for one family, reading a separate reasoning channel for another, and surviving an
> edge rate-limit — without which a uniform harness silently mis-scores or fails to read the model at
> all. Measurement portability, not the phenomenon, was the binding constraint.

**Shippable / not:** shippable as a methods/bound note; **not** as a headline result. No public page is
staged; this seeds a future handoff if the lane is promoted.
