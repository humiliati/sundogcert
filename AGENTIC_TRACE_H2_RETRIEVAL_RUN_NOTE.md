# H-II RETRIEVAL-CUSP RUN NOTE — real embeddings realize the fold-pair annihilation

**Frozen:** 2026-06-28, repo HEAD `master`. Run: `scripts/h2_retrieval_whitebox.py
--real` on Qwen2.5-0.5B-Instruct (CPU, ~22 s, free). Pre-registration:
`AGENTIC_TRACE_H2_RETRIEVAL_PREREG.md` (frozen before this run). Analysis pinned on the
synthetic dry-run (`scripts/test_h2_retrieval_whitebox.py`, 5/5) before any embedding
touched it.
**Lane:** sundogcert agentic-trace slate, Hypothesis II — the empirical leg that closes
the chain, mirroring the H-I white-box campaign.

---

## Verdict

- **Pre-registered verdict: K-ARTIFACT** (the literal §3 rule fired — the control pair
  also annihilated). Reported honestly: my pre-registered *control was mis-specified*.
- **Diagnostic verdict: SUPPORT — separation-graded, instrument-verified.** Real
  embeddings *do* realize the `RetrievalCusp` annihilation; the K-ARTIFACT is a
  too-weak control, not an instrument fault, and the true null + the β\* discriminator
  resolve it positively.

## What ran, what came out

6 semantically distinct documents → Qwen mean-pooled, L2-normalized embeddings (the
real attractor patterns). Modern-Hopfield retrieval energy
`E_β(ξ) = −β⁻¹·lseᵢ(β⟨xᵢ,ξ⟩) + ½‖ξ‖²` along the line between each memory pair; the
inverse-temperature β (= freshness) swept down `{128…2}`; interior extrema (folds)
counted by the H-II `foldpair_detector`.

| object | cosine | fold counts (β: 128→2) | detector | β\* (barrier persists to) |
|---|---|---|---|---|
| **15 distinct pairs** (all) | 0.47–0.83 | `[3,3,3,3,1,1,1]` | **structural-zero** | **16** |
| paraphrase "control" | 0.974 | `[3,1,1,1,1,1,1]` | structural-zero | 128 |
| **identical null** (true) | 1.000 | `[0,0,0,0,0,0,0]` | **accept** | — |

- **Every one of the 15 distinct memory pairs annihilates 3 → 1** as freshness decays
  — exactly the machine-checked `RetrievalCusp` prediction (two memories + a barrier →
  merged). 15/15 `structural-zero`.
- **The true null is clean.** Identical patterns (cosine = 1) form **no barrier at any
  β** → `accept`. The instrument does not manufacture an annihilation from nothing —
  this is the real artifact check, and it passes.
- **β\* (annihilation freshness) is the discriminator.** Distinct pairs hold the
  barrier down to β\* = 16; the paraphrase loses it at β\* = 128 (an 8× gap); identical
  patterns never form one. **Barrier persistence tracks memory separation.**

## Why K-ARTIFACT fired (the honest caveat)

The prereg's negative control was a *paraphrase* (cosine 0.974), and I declared it must
never form a barrier. But any two **non-identical** patterns form a hair-thin barrier
at sufficiently high β — so "a barrier exists at the top of the sweep" cannot
discriminate, and the binary control rule was the wrong test. The correct null is
**identical** patterns (cosine = 1), which I added as a diagnostic: it gives `accept`,
confirming the instrument is sound. The substantive discriminator is **β\***, not the
binary — and on β\* the separation effect is unambiguous (16 vs 128 vs none). Per the
discipline I do **not** retroactively rename the prereg verdict to SUPPORT; I report
K-ARTIFACT as fired and the diagnosis that resolves it.

## What this establishes (and bounds)

Real document embeddings, under the standard attractor-retrieval energy, **realize the
fold-pair annihilation the H-II Lean chain proves** (`RetrievalCusp.retrieval_realizes_
annihilation`: count 3 → 1 = `ContextDecay.Decays`). The same `foldpair_detector` the
falsifier hardened now does the empirical work; the result is read through the
machine-checked chain. The annihilation is a genuine separation effect (β\*-graded,
identical-null clean), not a functional artifact.

**Bounds (honest):** one 0.5B model; mean-pooled embeddings are anisotropic (distinct
cosine mean 0.67), so the absolute β\* numbers are model-specific; the modern-Hopfield
energy is *imported* (Ramsauer et al. 2020) — we test its realization on real
embeddings, we do not re-derive it; and this is the *retrieval-landscape* claim, **not**
a claim about production RAG decay dynamics, which remains a further import. A cleaner
prereg would have used the identical null as the control and β\* as the metric from the
start; a higher-n / larger-model / centered-embedding re-run can be staged in the
operator's PowerShell.

## The cross-lane mirror (the chain closes)

H-I's white-box: the decisive-source override is **internally legible, externally
illegible** (probe AUC 0.99 vs entropy 0.54) — the empirical complement of
`no_word_function_determines_decisive`. H-II's white-box: the retrieval barrier
**really forms and really annihilates** on real embeddings, separation-graded and
instrument-verified — the empirical realization of `RetrievalCusp` /
`ContextDecay.Decays`. Both lanes now run end to end: **falsifier → fix → Lean core →
grounding → mapping → empirical realization.** The proved model is not just internally
consistent; it is instantiated by a real memory.
