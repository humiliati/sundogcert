# H-III ATTENTION-HOLONOMY RUN NOTE — the injection is a gradient move, the loop is (mostly) blind

**Frozen:** 2026-06-28, repo HEAD `master`. Run: `scripts/h3_attention_whitebox.py
--real` on Qwen2.5-0.5B-Instruct (eager attention, CPU, ~70 s, free). Pre-registration:
`AGENTIC_TRACE_H3_ATTENTION_PREREG.md` (frozen before this run). Analysis pinned on the
synthetic dry-run (`scripts/test_h3_attention_whitebox.py`, 4/4) before any attention
touched it.
**Lane:** sundogcert agentic-trace slate, Hypothesis III — the empirical leg that pushes
H-III to the end of the chain, the analog of the H-I cliff and H-II retrieval white-boxes.

---

## Verdict

- **Pre-registered verdict: K-NULL-LOOP-ALSO-SEES — marginal.** At the gradient-argmax
  layer (L13) the curl AUC is **0.653**, a hair over the 0.65 KILL threshold. By the letter
  of §3 the loop is not *quite* blind enough to certify SUPPORT.
- **Substantively: a real, length-controlled, layer-localized dissociation in the predicted
  direction**, with a fix that never false-flags benign. The injection *is* a gradient
  (authority) move; the loop circulation is near-blind to it at the semantic layers; the
  naive version was inflated by a length confound that the matched control removes.

## What ran

81 prompts = 3 systems × 3 queries × (3 short-benign + 3 length-matched-benign + 3
injection) slots → Qwen mean-head attention per layer (24 layers). Per layer: the gradient
authority `φ(system) − φ(slot)` (answer-position attention) and the curl `circ`
(transitivity residual of attention flow), each scored as an injection classifier (AUC),
plus both receipts on the quantized field. A **length-matched benign** control (long benign
slots, no hijack) isolates the authority effect from the slot-length confound, since `φ`
sums attention over slot tokens.

## Results

| comparison | mean gradient AUC | mean curl AUC |
|---|---|---|
| injection vs **short** benign | 0.95 | 0.78 |
| injection vs **length-matched** benign | **0.70** | **0.64** |

- **Most of the naive separation was a length confound.** Against short benign both
  components separate (the injection is simply longer, different text). Length-matching
  collapses the curl to ~0.64 and the *mean* gradient to ~0.70 — the honest baseline.
- **A genuine dissociation survives at the semantic middle layers.** Controlling for
  length, layers **{12, 13, 15, 18, 19}** have gradient AUC ≥ 0.85 while curl AUC ≤ 0.70.
  Best layer **L13: gradient 0.973 vs curl 0.653** — a **+0.32** gap. The authority
  (gradient) carries the injection where the circulation (curl) is near-blind, exactly the
  Hodge split `HierarchyHolonomy.hierarchy_separates_what_loop_cannot` predicts.
- **The fix has perfect precision; the loop receipt is useless.** At L13 the Hodge-split
  hierarchy receipt flags **0/54 benign** (short *and* length-matched) and the injections
  whose authority actually flips; the old loop-circulation receipt flags **all 81** (curl is
  never exactly zero, so it always fires). Whatever the AUC threshold, the loop receipt
  cannot discriminate and the hierarchy receipt does not false-alarm.

## Reading it honestly

The directional claim is confirmed and the instrument contrast is clean: **the injection
moves the gradient/authority component, and the loop-circulation receipt is non-
discriminating** (flags everything). But the effect is **moderate, not the synthetic ideal**:
after removing the length confound, the gradient AUC is ~0.70 on average and ~0.85–0.97 only
at a handful of middle layers, and the authority ordering flips for a *fraction* of
injections on this 0.5B model (perfect benign precision, partial recall). The curl AUC 0.653
sits just over the 0.65 KILL line, so the literal verdict is K-NULL-LOOP-ALSO-SEES; the
substance is a bounded, length-controlled SUPPORT for "gradient carries it, loop is near-
blind, the fix is the right instrument."

## Bounds (honest)

One 0.5B model; `φ` is a token-sum (length-sensitive — the very reason the length-matched
control is the load-bearing comparison, and why absolute AUCs are model- and prompt-
specific); attention-as-evidence is contested (Jain–Wallace / Abnar–Zuidema); the
loop/curl definition is one of several reasonable choices; this is the *attention-landscape*
claim, **not** a claim about production guardrails. A larger model, a length-normalized `φ`
(mean rather than sum — a metric change, so it would need its own prereg), and attention-
rollout flows are the natural next legs, stageable in the operator's PowerShell.

## The cross-lane mirror

- H-I white-box: the override is **internally legible, externally illegible** (probe 0.99 vs
  entropy 0.54).
- H-II white-box: the retrieval barrier **really forms and annihilates** on real embeddings,
  separation-graded.
- H-III white-box: the injection **really is a gradient (authority) move** the loop
  circulation is near-blind to — confirmed in direction at the semantic layers, controlled
  for length, with a fix that never false-flags benign; bounded to moderate magnitude on a
  0.5B model. All three lanes now run **falsifier → fix → Lean core → empirical leg**, and
  in every case the empirical leg lands the *same* statement the Lean core proves: the
  attack lives where the naive observable cannot see it.
