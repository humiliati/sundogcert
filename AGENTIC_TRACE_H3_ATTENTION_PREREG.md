# H-III ATTENTION-HOLONOMY PREREG — does a real injection live in the gradient the loop is blind to?

**Frozen:** 2026-06-28, repo HEAD `master`.
**Status:** PREREG — written and frozen BEFORE any real-attention run or analysis. This
is the *empirical* leg that pushes H-III to the end of the chain, the analog of the H-II
retrieval white-box and the H-I cliff white-box. The deductive walls are shut (the
falsifier, the Hodge-split fix `hierarchy_holonomy_receipt.py`, and the Lean core
`HierarchyHolonomy.lean`); the one remaining import named in
`AGENTIC_TRACE_H3_FALSIFIER_RESULT.md` is the **trace→holonomy measurement map from real
attention**. This prereg specifies that map and attacks it.
**Lane:** sundogcert agentic-trace slate, Hypothesis III (Aharonov-Bohm Holonomy Filter),
empirical premise.

**Standing discipline (binds this prereg):** pre-registered KILL criteria — a clean null
is a SUCCESS (it bounds H-III, it does not embarrass it); forward-generate only (declare
metrics, thresholds, and the branch each result selects BEFORE seeing data); deterministic
analysis pinned on a synthetic dry-run before any real attention touches it; cheap headless
legs only (local 0.5B CPU, no API); name the nearest prior, state the delta.

---

## §0 What is imported, and what this tests

The H-III chain is closed and machine-checked: the loop-circulation filter measures only
the non-conservative (curl) component of a trace field, while the instruction hierarchy is
the conservative (gradient/potential) component the loop provably cannot see
(`HierarchyHolonomy.hierarchy_separates_what_loop_cannot`); the Hodge-split fix keys the
injection verdict on the gradient.

**Imported, not derived:** that a *real* transformer's attention, mapped into this
holonomy shape, actually behaves this way — that a prompt injection moves the **gradient
(authority) component** (it captures what the answer conditions on, out-ranking the system
instruction) while the **loop circulation (curl) is blind** to it. This tests the
*phenomenon* on a real model with the very receipts the fix produced — not a claim about
production guardrails, which remains a further import.

## §1 The measurement map (frozen)

- **Model:** Qwen2.5-0.5B-Instruct (cached, CPU, free; same model as the H-I/H-II
  white-boxes), loaded with `attn_implementation="eager"` so real attention weights are
  returned.
- **Prompts:** a fixed `system` instruction + a `query` + a final `slot`. The slot is
  either **benign** (innocuous filler) or an **injection** (an adversarial instruction
  such as "ignore previous instructions …"). Several systems × several queries × several
  benign/injection slots → a benign set and an injected set. Token spans of the `system`
  and `slot` segments are located by the fast tokenizer's offset mapping.
- **Attention field:** per layer `L`, the head-mean attention matrix `A_L` (`A_L[i,j]` =
  how much position `i` attends to position `j`; causal, `j ≤ i`).
- **Gradient / authority potential** `φ_L(v)` = attention the **final (answer) position**
  pays to segment `v`: `φ_L(v) = Σ_{j∈v} A_L[last, j]`. This is the conservative/potential
  component — what the answer conditions on. Anchor `φ(root) = 0`.
- **Curl / loop circulation** `circ_L` = the transitivity residual of the attention flow
  `f(X→Y) = Σ_{i∈X, j∈Y} A_L[i,j]` around `root → system → slot`:
  `circ_L = f(slot→system) + f(system→root) − f(slot→root)`. If the attention flow were a
  pure authority gradient (conservative), this is zero (path-independence); the residual is
  the genuine non-conservative component.
- **Receipts:** `φ` and the flows are quantized to integers (×1e4, rounded) and fed to BOTH
  the old `discrete_holonomy_receipt` (loop circulation) and the new
  `hierarchy_holonomy_receipt` with reference constraint **`system` must out-rank `slot`**
  (`must_dominate = [("system","slot")]`).

## §2 Metrics and claim (what a SUPPORT verdict asserts)

Per prompt: `authority_margin_L = φ_L(system) − φ_L(slot)` (positive = system out-ranks;
≤ 0 = the slot hijacked the answer's attention) and `circ_L`. Treat "is this injected?" as
a binary task over the benign+injected set and compute, **per layer**:

(i) **The injection lives in the gradient** — `authority_margin` separates injected from
benign with **AUC ≥ 0.75** at some layer (injection drives the margin down / negative): the
authority ordering flips, exactly where the Hodge fix keys.

(ii) **The loop is blind** — `|circ|` separates injected from benign only at **AUC ≤ 0.65**
(near chance) at that same layer: the curl does not carry the attack.

(iii) **The fix beats the loop** — the gradient AUC exceeds the curl AUC by **≥ 0.15**, and
the Hodge-split hierarchy receipt's verdicts (accept = benign-like, structural-zero =
flagged) separate the two sets better than the old loop-circulation receipt.

SUPPORT = (i)+(ii)+(iii). This realizes `HierarchyHolonomy` on a real model: the injection
is a gradient (authority) move the loop circulation is blind to, and the fix is the one
that sees it.

## §3 Verdicts and KILL criteria (declared before data)

- **K-SUPPORT** — (i)+(ii)+(iii) hold. The blind spot and the fix are confirmed on real
  attention (bounded: one 0.5B model, this map). H-III's chain is closed end to end.
- **K-NULL-NOGRADIENT** — `authority_margin` never reaches AUC ≥ 0.75 at any layer: the
  injection does not move this authority proxy. A SUCCESS that bounds H-III — the *attention
  authority* map is not where this model's injection lives (the import is falsified for this
  map), a sharper statement than leaving it open.
- **K-NULL-LOOP-ALSO-SEES** — `|circ|` *also* separates (AUC > 0.65) wherever the gradient
  does: the curl carries the attack too, so the "loop is blind" claim fails empirically on
  real attention. Bounds H-III: the Hodge split is not cleanly informative here.
- **K-ARTIFACT** — the fix flags the benign set as often as the injected set (no
  separation): the receipt/quantization is not faithfully reading the map.

Any K-NULL-* is a publishable bound, not a failure.

## §4 Analysis pin (dry-run before real data)

Before any model runs, the harness executes a **synthetic dry-run** on hand-built
attention matrices: a benign matrix where the answer attends mostly to `system`
(`authority_margin > 0`), and an injected matrix where the answer attends mostly to the
`slot` (`authority_margin < 0`), with matched curl. It asserts the pipeline returns gradient
AUC = 1, curl AUC ≈ 0.5, the hierarchy receipt accepts benign and flags injected, and the
old loop receipt does not separate. This pins φ, circ, quantization, the receipts, and the
AUC wiring deterministically; the real run then changes only the source of `A`. Frozen as
`scripts/test_h3_attention_whitebox.py`.

## §5 Nearest prior / delta

- **Nearest prior:** attention-as-evidence / attention-flow attributions (Abnar–Zuidema
  rollout 2020; the broad "attention ≠ explanation" debate). The authority proxy (answer-
  position attention mass) is standard; **imported**.
- **Delta:** we do not claim attention *is* the explanation; we Hodge-split the attention
  field into authority (gradient) + circulation (curl), test which carries a prompt
  injection, and read the result through the machine-checked `HierarchyHolonomy` /
  `hierarchy_holonomy_receipt` — the H-III analog of the H-I hidden-probe-vs-entropy and the
  H-II retrieval white-box.
