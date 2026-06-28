# H-II RETRIEVAL-CUSP PREREG — does a real embedding memory realize the fold-pair annihilation?

**Frozen:** 2026-06-28, repo HEAD `master`.
**Status:** PREREG — written and frozen BEFORE any measurement run or analysis on
real-model embeddings. This is the *empirical* leg that closes H-II's chain: the
deductive walls are shut (`ContextDecay` rule, `CuspGerm` germ, `RetrievalCusp`
attractor model), and the only remaining obligation named in
`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md` §10 is the import *"a real retrieval landscape
is (locally) this attractor energy with a decaying barrier."*
**Lane:** sundogcert agentic-trace slate, Hypothesis II (Whitney A3 cusp for context
decay), empirical premise. Mirrors the H-I white-box campaign
(`AGENTIC_TRACE_H1_CLIFF_TRANSFER_*`).

**Standing discipline (binds this prereg):** pre-registered KILL criteria — a clean
null is a SUCCESS (it bounds H-II, it does not embarrass it); forward-generate only
(declare metrics, thresholds, and the branch each result selects BEFORE seeing data;
no tuning the analysis to the outcome); deterministic analysis pinned on a synthetic
dry-run before any real embeddings touch it; cheap headless legs only inside the
~10-minute rule (this is a local 0.5B CPU embed + numpy sweep, ≈ 1 min — no API, no
operator-staging needed); name the nearest prior, state the delta.

---

## §0 What is imported, and what this tests

The H-II deductive chain is closed and machine-checked:

- `ContextDecay.Decays` — the quarantine rule fires *exactly* on a fold-pair
  annihilation (fold count drops by 2); never on a fold-free / stable family.
- `CuspGerm` — the cubic germ `x³ − a·x` realizes the abstract drop-by-two.
- `RetrievalCusp` — the attractor-memory energy `V_a(x) = x⁴/4 − a·x²/2` (Hopfield /
  modern-Hopfield double well) has critical-point count **3 for a>0** (two memories
  `±√a` + a barrier `0`, `memories_are_minima`) **→ 1 for a<0** (wells merged), a
  `Decays` event.

**Imported, not derived:** that a *real* embedding memory, under the standard
attractor-retrieval energy, actually exhibits this double-well-to-single-well
annihilation as a freshness control decays. Modern Hopfield (Ramsauer et al. 2020)
*guarantees* the metastability→single-fixed-point transition exists for sufficiently
separated patterns; what is **not** guaranteed and is tested here is whether **real
document embeddings sit in the geometry that realizes it** — i.e. whether distinct
memories form a genuine barrier that annihilates, while near-identical memories do
not. A clean result either way bounds H-II.

This tests the *phenomenon* (a real-embedding retrieval energy undergoes a fold-pair
annihilation under a declared decay control, detected by the very `foldpair_detector`
the H-II fix produced) — **not** any claim about production RAG decay dynamics, which
remains a further, unbounded import.

## §1 Method (frozen)

- **Model / memory (white-box):** Qwen2.5-0.5B-Instruct (cached, CPU, free; same model
  as the H-I white-box). Embedding of a text = **mean-pooled last-hidden-state**, L2
  normalized. These real embeddings are the stored attractor patterns `X`.
- **Retrieval energy (standard modern-Hopfield):**
  `E_β(ξ) = −β⁻¹ · logΣᵢ exp(β·⟨xᵢ, ξ⟩) + ½‖ξ‖²`,
  whose minima are the retrieval fixed points and whose update is attention.
- **1-D landscape:** for a memory pair `(x_i, x_j)`, query along the line
  `ξ(t) = x_i + t·(x_j − x_i)`, `t ∈ [−0.4, 1.4]` (so both wells, near `t=0,1`, and the
  barrier near `t=0.5`, are **interior** to the sampled range), 41 evenly spaced
  samples.
- **Decay control λ (= staleness):** the inverse-temperature `β` swept **descending**
  over a fixed log-grid `β ∈ {128, 64, 32, 16, 8, 4, 2}`. Decreasing β = fuzzier / staler
  retrieval (the declared decay direction); control = sweep index (increasing =
  staler), so an annihilation is the fold count **dropping** with the control.
- **Fold count:** each energy curve scaled to unit range, converted to exact
  `Fraction`, fed to `foldpair_detector.count_interior_extrema` with
  `min_slope = 1e-6`, calibrated on the synthetic pin (§4) to sit between the flat
  parabolic bottom of a real single well (per-step slope ≈ 1e-4 at this sampling) and
  numerical wiggle (≈ 1e-12), so one well reads as exactly 1 fold. The per-β
  fold-count family is fed to `foldpair_detector.make_foldpair_receipt`.
- **Pairs:** all distinct pairs among **6 real, semantically distinct documents**
  (declared in the harness), reported individually.
- **Control (negative):** a **near-identical** pair (a document and a trivial
  paraphrase) — its barrier should never form, so its fold count should stay ≤ 1 and
  the detector should `accept` (no annihilation). A control that *also* annihilated
  would mean the effect is an artifact of the energy, not of memory separation.

## §2 Claim (what a SUPPORT verdict asserts)

On real Qwen embeddings, under the standard modern-Hopfield retrieval energy:

(i) **A barrier exists at high freshness** — at the top of the β sweep, the energy
landscape between two distinct memories has fold count **≥ 3** (two wells + barrier).

(ii) **It annihilates as freshness decays** — descending β, the fold count drops by
**exactly 2** (3 → 1), a `foldpair_detector` **`structural-zero`** verdict, on **≥ ⅔
of the distinct memory pairs**.

(iii) **The control does not annihilate** — the near-identical pair never reaches fold
count ≥ 3 and yields **`accept`** (no spurious annihilation).

SUPPORT = (i)+(ii)+(iii). This empirically realizes `RetrievalCusp` on real
embeddings: distinct memories form a barrier that annihilates under decay; the model
the Lean proves is *instantiated*, not just internally consistent.

## §3 Verdicts and KILL criteria (declared before data)

- **K-SUPPORT** — (i)+(ii)+(iii) hold. The import is empirically realized (bounded:
  one 0.5B model, modern-Hopfield energy, 6 docs). H-II's chain is closed end to end.
- **K-NULL-NOBARRIER** — distinct pairs never reach fold count ≥ 3 at any β (no barrier
  forms on real embeddings). A SUCCESS that bounds H-II: the attractor model is
  internally proved but *not realized* by this embedding geometry — the import is
  **falsified on this model**, a sharper statement than leaving it open.
- **K-NULL-NOANNIHILATION** — a barrier exists (i) but the count never drops by 2 as β
  decays (no clean annihilation; e.g. it dissolves via an unpaired/odd change →
  `quarantine`). Bounds H-II: real geometry has the wells but not the clean A3 merge.
- **K-ARTIFACT** — the control pair *also* annihilates. Then (ii) is an artifact of the
  energy functional, not of memory separation; the result does **not** support the
  import and the harness/energy must be reconsidered.

Any of K-NULL-* is a publishable bound, not a failure. Only K-ARTIFACT invalidates the
instrument.

## §4 Analysis pin (dry-run before real data)

Before embedding anything, the harness runs a **synthetic dry-run** on closed-form
patterns engineered to be well-separated, asserting the pipeline returns
`structural-zero` with a clean 3→1 drop on the synthetic distinct pair and `accept`
on a synthetic near-identical pair. This pins the detector wiring (scaling, Fraction
conversion, `min_slope`, control ordering) deterministically; the real-embedding run
then changes only the source of `X`. The dry-run is frozen as a test
(`scripts/test_h2_retrieval_whitebox.py`).

## §5 Nearest prior / delta

- **Nearest prior:** modern Hopfield networks (Ramsauer et al. 2020) — the energy,
  the metastability transition, and its cusp character are theirs; **imported**.
- **Delta:** we do not re-derive the transition; we test whether *real document
  embeddings* realize it, detect it with the **H-II `foldpair_detector`** (so the same
  instrument that the falsifier hardened now does empirical work), and read the result
  through the machine-checked `RetrievalCusp`/`ContextDecay` chain — closing H-II the
  way the H-I white-box closed H-I.
