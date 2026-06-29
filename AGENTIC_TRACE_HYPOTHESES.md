# Agentic Trace Hypothesis Slate

This note turns the trace-conditioned agentic-reasoning brief into a
repo-facing slate. It follows the repository discipline:

> Machine-check the deductive core. Name the imported wall.

The aim is not to claim that the repository has formalized transformer
internals, long-horizon memory, or live attention topology. The aim is to
identify which parts of the proposed agent loop can already be made small,
checkable, and axiom-audited, and which parts still need empirical or modeling
receipts before they can carry load.

## Current Formal Receipt

The first Lean hook is `Sundogcert/AgenticTrace.lean`.

It checks four reusable facts:

- `rs_receipt_accept_safe`: an accepted Reed-Solomon receipt implies the trace
  is safe, by `RSCertificate.accept_sound`.
- `rs_receipt_unique`: inside the unique-decoding radius, two decodings of the
  same received trace are equal, by `RSCertificate.unique_decoding`.
- `trace_gated_noninterference`: if a policy factors only through a published
  signature channel, signature-preserving attacks cannot change its action, by
  `Tauroctony.signature_noninterference`.
- `branch_count_le_budget`: a finite branch trace injected into certified slots
  cannot exceed its published budget.

These are intentionally thin. They are the audited skeleton a future agentic
instrument can attach to; they are not a proof that a deployed model exposes
the required measurements.

## Hard Claim Boundary

Already checked in Lean:

- cheap RS acceptance implies a witness-backed safe trace;
- RS uniqueness under the standard radius condition;
- signature-gated noninterference;
- finite branch-count control from an injective coordinate witness;
- the Aharonov-Bohm gauge zero-out and loop/flux theorem in `FaradayAB.lean`;
- the existing syndrome, audit-cost, and Karp-reduction cores.

Named but not checked here:

- that a production model exposes a stable "net.7" or equivalent latent basin;
- that the empirical cliff at lambda approximately 0.953 transfers to a new
  agent stack;
- that a memory-retrieval topology really forms a Whitney A3 cusp under stale
  or contradictory context;
- that transformer attention heads can be faithfully mapped to a discrete
  holonomy or plaquette gauge field;
- that an agent search tree admits a useful cap-set or polynomial-method
  projection rather than only a generic finite budget;
- that any runtime trace extraction is tamper-resistant before certificate
  issuance.

Those walls are not defects. They are the agenda.

## Hypothesis I: Syndrome-Gated Tauroctony

Working hook:

> When latent reasoning stress approaches a certified boundary, prune first and
> emit a receipt, rather than letting the model hallucinate past the cliff.

Instrument:

- Monitor a low-dimensional state signature for out-of-envelope stress.
- Project the live reasoning state through a Tauroctony-style pruning channel.
- Emit an RS evaluation receipt for the surviving trace.
- Accept only if the cheap verifier returns a witness-backed decoding.

Lean surface:

- already supported by `rs_receipt_accept_safe`;
- uniqueness supported by `rs_receipt_unique`;
- signature attack separation supported by `trace_gated_noninterference`.

Imported wall:

- the live state measurement and the lambda cliff are empirical, not formal;
- the pruning map must be shown to preserve task-relevant content rather than
  merely deleting inconvenient context.

Forward cost target:

- certificate verification remains in the RS forward-check regime;
- the monitor should be cheaper than another model pass or classifier call.

Falsifier:

- produce contradictory corpus cases where pruning emits an accepted receipt
  while dropping the decisive source, or where the same receipt is accepted for
  two semantically incompatible resolutions.

Falsifier outcome (2026-06-25): **FIRED, then FIXED.** Both forms were satisfied by
a runnable, receipt-checkable counterexample against the live prototype
(`AGENTIC_TRACE_H1_FALSIFIER_RESULT.md`, `scripts/h1_decisive_source_falsifier.py`):
RS majority decoding prunes a decisive *minority* source exactly as it prunes
noise, and the receipt payload excluded labels, so one byte-identical accepted
receipt covered two safety-incompatible readings. The RS core was always intact
(the control confirms the *numeric* two-survivor attack is impossible in-radius —
`rs_receipt_unique`); the break was the unproven semantics-to-signature measurement
map, the gap `signature_noninterference` relocates rather than deletes.

The fix landed the same day (`AGENTIC_TRACE_H1_FALSIFIER_RESULT.md` §8): an opt-in
**decisive designation** bound into the receipt — `prune_trace(..., decisive_indices=...)`
quarantines (`decisive-source-pruned`) rather than accepting when a designated
decisive cell would be pruned, and the designation is part of the digest (so the
two skins no longer share a receipt). Malformed designations **fail closed**: an
out-of-range or non-int index (a typo like `(99,)`, or a partially valid `(0, 99)`)
quarantines (`malformed-decisive-designation`) rather than being silently dropped.
Lean: `DecisiveKept` + `decisive_kept`, `decisive_pruned_not_kept`,
`decisive_receipt_safe_and_preserving` (axiom-clean, in the `AxiomAudit` gate).
`scripts/decisive_gate_fix.py` (+ frozen test) shows the falsifier corpus now
quarantines, the skins split, and malformed designations fail closed.

Promotion status:

- **falsifier-gate cleared; remaining walls classified** (`AGENTIC_TRACE_H1_WALLS.md`).
  The decisive-source binding + the Lean content-preservation lemmas are done. The
  residual the fix introduced — can decisiveness be *derived* from the word rather
  than designated? — is now **resolved as a necessary import**, machine-checked:
  `decisive_underdetermined_by_word` / `no_word_function_determines_decisive` prove
  the word under-determines the decisive set (same shape as the `AuditCost`
  blindness theorems), so the caller designation is correct by necessity, not a
  shortcut. What remains is exactly what the slate always called empirical — the
  existence/transfer of the stress-signature λ cliff on a real model — plus an
  operational trace-extraction commitment-timing note. H-I is promotable against
  those clearly-labelled imported walls; it is not blocked by any unproved
  deductive claim.

## Hypothesis II: Whitney A3 Cusp for Context Decay

Working hook:

> Stale memory is not only old memory; it is memory whose retrieval geometry has
> entered a fold-pair annihilation regime.

Instrument:

- Treat memory retrieval as a one-parameter regularized risk curve.
- Detect a cusp-like transition in a local jet of the retrieval score.
- Quarantine or decay memory until the measured topology returns to the smooth
  side of the boundary.

Lean surface:

- no dedicated cusp formalization exists in this repository yet;
- a first formal target would be a small polynomial-jet predicate with a proved
  quarantine rule, keeping the model-specific detector outside the proof.

Imported wall:

- the mapping from vector memory to a Whitney A3 cusp is empirical/modeling
  work, not a consequence of catastrophe theory alone.

Forward cost target:

- local jet fitting over a small sampled window, not global vector-database
  recomputation.

Falsifier:

- find stale-context failures with no cusp signature, or clean fresh-context
  retrievals that repeatedly trigger the cusp detector.

Falsifier outcome (2026-06-27): **FIRES.** Both forms are satisfied against the live
`cusp_detector` (`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md`,
`scripts/h2_cusp_detector_falsifier.py` + frozen test). The detector's signature —
a `c2` (second-difference) sign-change with the center exactly 0 — detects an
**inflection**, not the **fold-pair annihilation** an A3 cusp is. It (A) false-positives
on a benign monotone, fold-free S-curve; (B) is **invariant** across the canonical
unfolding `x³ − e·x` (identical `structural-zero` / `c2 = (-6,0,6)` for every `e`,
even as the fold pair annihilates) — blind to the event it exists to find; (C)
false-negatives on the genuine cusp germ `x³` sampled off-center. Root cause: it
reads only the second difference (curvature), never the first (slope / critical
points), and a single 1-D jet cannot witness a control-parameter event.

Fix landed (2026-06-27): the re-specified `scripts/foldpair_detector.py`
(`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md` §7) measures the **fold count** (first
difference / interior extrema) across a **two-parameter family**, and declares a
fold-pair annihilation when the count drops by 2. It closes all three legs: monotone
fold-free curves now `accept`, the `x³ − e·x` unfolding is `structural-zero`
(annihilation witnessed, fold count 2 → 0), and off-center cusp germs are caught.

Lean core landed (2026-06-27): `Sundogcert/ContextDecay.lean` (`§8` of the result
doc) pins what an annihilation receipt licenses — `decay_earned`, `foldfree_no_decay`
(leg A, formalized), `stable_no_decay`, the headline `decays_iff_foldpair`
(soundness ∧ completeness), and `annihilation_budget` (the `branch_count_le_budget`
analog: `2·#annihilations ≤ initial fold count`). All five are axiom-clean
(`[propext, Quot.sound]` — a subset of the foundational triple), enforced by
`#guard_msgs` in `AxiomAudit.lean`; full `lake build` green.

Grounding landed (2026-06-27): `Sundogcert/CuspGerm.lean` (`§9` of the result doc)
grounds the abstract rule in the real germ — the cubic score curve `f_a(x) = x³ − a·x`
has fold count (critical points = real roots of `3x² − a`) **2 for `a>0`, 0 for
`a<0`**, so for `a₀<0<a₁` the family `[2,0]` is a `ContextDecay.Decays` event
(`cubic_realizes_annihilation`, `cubic_foldpair_witness`). (Count correction: 2→0 for
the *score curve*; the 3→1 figure is the degree-4 *potential* — both detector and
`ContextDecay` key on the drop-by-2, so the cubic is the faithful witness.) These four
are real-analysis (`Real.sqrt`, `Set.ncard`) → the full triple `[propext,
Classical.choice, Quot.sound]`, axiom-clean; full `lake build` green (3539 jobs).

Mapping landed (2026-06-27): `Sundogcert/RetrievalCusp.lean` (`§10` of the result doc)
takes the last step — a concrete, interpretable attractor-memory model and a proof it
realizes the rule. The model is the Hopfield-style double-well energy
`V_a(x) = x⁴/4 − a·x²/2` (control `a` = pattern separation / freshness): stored
memories = minima. Critical points (memories + barrier) = roots of `V' = x³ − a·x`:
**count 3 for `a>0`** (two memories `±√a` + barrier `0`; `memories_are_minima` proves
`V''>0` at the memories, `V''<0` at the barrier) **→ 1 for `a<0`** (wells merged). So
for `a₀<0<a₁` the family `[3,1]` is a `ContextDecay.Decays` event
(`retrieval_realizes_annihilation`, `retrieval_foldpair_witness`). Real-analysis → full
triple, axiom-clean; full `lake build` green (3540 jobs).

Empirical leg landed (2026-06-28): `scripts/h2_retrieval_whitebox.py` +
`AGENTIC_TRACE_H2_RETRIEVAL_{PREREG,RUN_NOTE}.md` — the H-I-style white-box. Real
Qwen2.5-0.5B mean-pooled embeddings as attractor patterns; modern-Hopfield retrieval
energy along each memory pair; β (freshness) swept down; folds counted by the H-II
`foldpair_detector`. **All 15 distinct memory pairs annihilate 3→1 (`structural-zero`)**
— the `RetrievalCusp` prediction realized on real embeddings — and the **identical-pattern
true null gives `accept`** (no barrier from nothing: instrument verified). The
annihilation freshness **β\* is separation-graded** (distinct β\*=16, paraphrase β\*=128,
identical none). Honest caveat: the pre-registered binary *control* fired **K-ARTIFACT**
(a paraphrase, cosine 0.974, is not a true null — any non-identical pair forms a thin
barrier at extreme β); diagnostic verdict = SUPPORT-separation-graded, carried by the
true null + β\*. Bounds: one 0.5B model, anisotropic embeddings, modern-Hopfield energy
imported.

Promotion status:

- **falsifier fired → fix landed → Lean core landed → germ grounding landed → mapping
  landed → empirical realization landed** (was: second wave). The full chain runs end
  to end: a real embedding memory realizes the proved annihilation. The remaining
  imports are now honestly external: the modern-Hopfield energy itself (cited, not
  re-derived) and any claim about *production* RAG decay (untested). H-II is the most
  complete hypothesis in the slate — the proved model is instantiated by a real memory,
  not merely internally consistent.

## Hypothesis III: Aharonov-Bohm Holonomy Filter

Working hook:

> A prompt injection can look locally ordinary while creating a nonzero loop
> anomaly in the reasoning path.

Instrument:

- Map selected attention or routing transitions to a discrete closed loop.
- Compute a gauge-style circulation receipt over that loop.
- Halt or quarantine when the loop fails the expected zero-out condition.

Lean surface:

- `FaradayAB.lean` already proves the continuous gauge zero-out and the
  loop/flux topological closure;
- the next Lean step should be a discrete-loop analogue, not a direct claim
  about transformer attention.

Imported wall:

- attention weights are not automatically physical gauge fields;
- a faithful measurement map from reasoning trace to holonomy must be specified
  and attacked independently.

Forward cost target:

- one pass over selected loop edges in the trace graph.

Falsifier:

- adversarial prompts that preserve the zero receipt while changing the
  instruction hierarchy, or benign OOD queries that create persistent nonzero
  phase.

Falsifier fired (2026-06-28): `scripts/h3_holonomy_filter_falsifier.py` +
`AGENTIC_TRACE_H3_FALSIFIER_RESULT.md`. The discrete theorem is done
(`DiscreteHolonomy.closed_gauge_sum_zero`) and the runtime filter
(`discrete_holonomy_receipt.py`) flags when the observed loop circulation `≠ 0` — but
that very zero-out theorem is the blind spot. A loop circulation sees only the
non-conservative (curl) component; the instruction hierarchy is the conservative
(gradient/potential) component, which contributes **zero to every loop**. Three legs,
all fire: **A** — a gradient-encoded hierarchy hijack (top authority flipped
`system→injected`) gives the *same* `accept`/zero receipt as benign (gauge invariance
`A→A+grad χ` is the attack's cloak); **B** — benign curl `(1,1,1)` is flagged
`structural-zero` (false positive); **control** — a curl-type attack `(5,5,5)` IS caught
(detector not dead). Mis-specification, not a threshold (curl ⊥ gradient Hodge
components; the loop integral is a functional of curl alone). 5-case frozen test.

Fix landed (2026-06-28): `scripts/hierarchy_holonomy_receipt.py` (`§7` of the result
doc) — a Hodge-split receipt that keys the injection verdict on the **gradient /
hierarchy** component (potential ordering vs a declared `must_dominate` reference,
supplied externally — the H-III analog of H-I's `decisive_indices`), reporting the curl
residual but not flagging it. Closes both legs: **A** the zero-circulation gradient
hijack is now `structural-zero` (`hierarchy-violation`) where the loop filter was blind;
**B** benign curl is `accept` (`hierarchy-intact`) where the loop filter false-positived.
8-test fix-verification vs the old filter.

Lean core landed (2026-06-28): `Sundogcert/HierarchyHolonomy.lean` (`§8` of the result
doc) pins what the hierarchy receipt licenses — `intact_iff_not_hijacked` (the rule
fires exactly on a violation; **axiom-free**), `hijack_witness` (`[propext]`),
`authority_gap_along_path` (the gradient carries the hierarchy), `loopCirc_zero` (the
gauge loop is identically zero — the blind spot), and the headline
`hierarchy_separates_what_loop_cannot` (two potentials, same zero loop circulation,
opposite hierarchy verdicts — the loop provably cannot determine the hierarchy; the
H-III analog of H-I's `no_word_function_determines_decisive`). Enforced by `#guard_msgs`
in `AxiomAudit.lean`; full `lake build` green (3543 jobs).

Empirical leg landed (2026-06-28): `scripts/h3_attention_whitebox.py` +
`AGENTIC_TRACE_H3_ATTENTION_{PREREG,RUN_NOTE}.md` — the H-I/H-II-style white-box. Real
Qwen2.5-0.5B eager-attention Hodge-split into a gradient/authority potential
`φ(v)` = answer-position attention to segment `v` and a curl `circ` = transitivity
residual of attention flow; 81 prompts (3 systems × 3 queries × short-benign / **length-
matched-benign** / injection slots), per-layer gradient-AUC vs curl-AUC. **Directional
dissociation confirmed, length-controlled:** at the semantic middle layers {12,13,15,18,19}
the gradient separates the injection from a *length-matched* benign (best L13 AUC 0.973)
while the curl is near-blind (0.653) — a +0.32 gap; the Hodge-split hierarchy receipt flags
**0/54 benign** (perfect precision) where the old loop receipt flags **all 81** (useless).
Honest bounds: literal verdict **K-NULL-LOOP-ALSO-SEES** (best-layer curl 0.653 a hair over
the 0.65 KILL line); most of the *naive* separation (vs short benign, AUC 0.95/0.78) was a
length confound the matched control removed; effect moderate / partial-recall on 0.5B; `φ`
is a token-sum; attention-as-evidence contested.

Promotion status:

- **falsifier fired → fix landed → Lean core landed → empirical leg landed** (was:
  promising but measurement-heavy). The full chain runs end to end on a real model: the
  injection is a gradient (authority) move the loop circulation is near-blind to, and the
  Hodge-split fix never false-flags benign while the loop receipt cannot discriminate.
  H-III now matches H-II's completeness. Named imports (by design): the trusted reference
  hierarchy, and the broader attention-as-trace interpretation.

## Hypothesis IV: Trace-Bounded Search Trees

Working hook:

> A recursive search tree should stop at a published structural boundary, not at
> an opaque token budget.

Instrument:

- Assign each admissible branch to a finite coordinate slot or polynomial
  trace.
- Refuse expansion when no certified slot remains.
- Emit a structural-zero receipt when a branch violates the trace predicate.

Lean surface:

- `branch_count_le_budget` proves the generic finite-budget core;
- a true cap-set version would need an explicit `F_3^n` search projection and
  a line-free/polynomial predicate.

Imported wall:

- mapping arbitrary agent branches into cap-set geometry is not yet justified;
- the current Lean hook proves a finite injection bound, not an
  Ellenberg-Gijswijt-style theorem.

Forward cost target:

- branch admissibility should be checked in linear time in the trace length or
  polynomial degree witness.

Falsifier:

- search tasks where the structural bound cuts off the only successful branch,
  or where branch explosion occurs despite every emitted trace satisfying the
  generic budget check.

Falsifier fired (2026-06-28): `scripts/h4_branch_budget_falsifier.py` +
`AGENTIC_TRACE_H4_FALSIFIER_RESULT.md`. The runtime `branch_budget_receipt.py` admits the
top-`budget` branches **by score** and refuses overflow — but a count-by-score cap is the
opaque token budget the hook warned against, relabelled structural. Two legs, both fire:
**A** — a low-score WINNER (the only solution-bearing branch) is refused, and the smallest
budget that keeps it is the one that admits *everything* (no bound); **B** — each node
emits `budget` branches so every per-node receipt is `accept`, yet a depth-8 tree has
9840 ≥ 3⁸ nodes (the per-node cap does not bound the search); **control** — genuine breadth
overflow is refused (detector not dead). Mis-specification, not a tunable budget (the
solution location and total complexity are orthogonal to a score-ranked count). 4-case
frozen test.

Fix landed (2026-06-28): `scripts/structural_slot_receipt.py` (`§7` of the result doc) —
admits on a STRUCTURAL line-free predicate, not score. Each branch carries an `F₃ⁿ`
coordinate; admitted iff it keeps the admitted set a **cap** (no three distinct points
`a+b+c≡0 mod 3`); the admitted set is bounded by the **cap-set capacity** of the space,
independent of candidate count. Closes both legs: **A** a low-score winner whose coord
completes a cap is **admitted** (`accept`) where the count cap refused it; **B** all 9
points of `F₃²` → admits a cap of **≤4** (`CAP_CAPACITY[2]`), refuses 5 — bounded by
capacity, not the `budget**depth` the count cap accepts. 8-test fix-verification vs the old
receipt (incl. structural refusals and tamper).

Promotion status:

- **falsifier fired → fix landed** (was: useful as a generic budget receipt). The next
  deductive step is the Lean quarantine theorem — surface `AgenticTrace.branch_count_le_budget`
  (finite-injection core) plus a line-free predicate, mirroring H-II's `ContextDecay` and
  H-III's `HierarchyHolonomy` cores. The branch→cap-set measurement map and the
  Ellenberg–Gijswijt bound remain named imports by design. **All four slate hypotheses now
  have a fired falsifier; H-I/H-II/H-III/H-IV all have a landed fix.**

## Deployment Sequence

1. Land the receipt layer.
   Done: `AgenticTrace.lean` compiles and is included in `AxiomAudit.lean`.

2. Build the RS-pruning prototype.
   Started in `scripts/rs_pruning_prototype.py`. It uses a tiny GF(17) RS
   scheme, explicit stale/contradictory trace cells, a deterministic brute-force
   verifier, and emits the trace, pruned trace, survivor polynomial, and receipt
   digest. Since 2026-06-25 it also supports the decisive-source binding
   (`prune_trace(..., decisive_indices=...)`) that closes the falsifier — a
   designated decisive cell that would be pruned forces a `decisive-source-pruned`
   quarantine, and the designation is bound into the digest. Run it with:

   ```sh
   python scripts/rs_pruning_prototype.py
   python scripts/rs_pruning_prototype.py --json
   python -m pytest scripts/test_rs_pruning_prototype.py -q
   ```

3. Add branch-budget receipts to search.
   Started in the same prototype and hardened as a reusable module in
   `scripts/branch_budget_receipt.py`. `scripts/rs_pruning_prototype.py` now
   generates deterministic search branches only from RS-kept trace cells, admits
   them into a finite slot budget, and emits a `structural-zero` receipt for
   overflow branches. Malformed candidate traces, such as duplicate branch IDs,
   emit verifier-checkable quarantine receipts. This corresponds to the Lean
   `BudgetedTrace` core: the admitted branch count is no larger than the
   certified slot budget. It is not yet a cap-set receipt.

   ```sh
   python -m pytest scripts/test_branch_budget_receipt.py -q
   ```

4. Specify a discrete loop theorem.
   Done at the finite core level in `Sundogcert/DiscreteHolonomy.lean`: finite
   gauge sums telescope to endpoint differences, closed loops zero out, and
   pure-gauge sums are path-independent when endpoints agree. The executable
   toy receipt in `scripts/discrete_holonomy_receipt.py` checks closed integer
   trace loops and emits `accept`, `structural-zero`, or verifier-checkable
   `quarantine`. This still does not attach the theorem to attention traces;
   that measurement map remains an imported wall.

   ```sh
   lake build Sundogcert.DiscreteHolonomy
   python -m pytest scripts/test_discrete_holonomy_receipt.py -q
   ```

5. Specify a cusp detector.
   Done at the runtime-spec level in `scripts/cusp_detector.py`. The detector
   consumes five evenly spaced score samples from a one-dimensional retrieval or
   regularization sweep, computes sampled second and third differences, and
   emits `structural-zero` only when the left/right second differences change
   sign with enough magnitude, the center second difference is near zero, and
   the local third differences stay inside a declared bound. Malformed samples,
   negative thresholds, and sign changes outside the third-difference envelope
   emit verifier-checkable quarantine receipts. This is still only a sampled
   detector spec; the vector-memory-to-cusp measurement map remains an imported
   wall. **FALSIFIED 2026-06-27** (`AGENTIC_TRACE_H2_FALSIFIER_RESULT.md`): the
   `c2`-sign-change signature detects an inflection, not the fold-pair annihilation
   — it false-positives on monotone fold-free curves, is invariant across the
   `x³ − e·x` unfolding (blind to the annihilation), and misses off-center cusp
   germs. Needs re-specifying around first-difference / interior-extrema (fold)
   structure + the two-parameter unfolding before any Lean quarantine theorem.

   ```sh
   python -m pytest scripts/test_cusp_detector.py -q
   python scripts/h2_cusp_detector_falsifier.py
   python -m pytest scripts/test_h2_cusp_detector_falsifier.py -q
   ```

## Promotion Criteria

A hypothesis graduates from slate to roadmap when it has all of:

- a Lean-checkable deductive core with no `sorry` and no `native_decide`;
- a named imported wall small enough for an external reviewer to attack;
- a runtime receipt whose verification is cheaper than the search/reasoning
  process it governs;
- at least one negative test where the instrument is expected to reject;
- a falsifier that would demote or retire the hypothesis.

## Recommended Next Move

**Updated 2026-06-25 — H-I falsifier fired AND was fixed the same day.** H-I's
pre-registered falsifier fired (`AGENTIC_TRACE_H1_FALSIFIER_RESULT.md`): the RS
receipt certified numeric low-degree agreement, not decisiveness, so an accepted
prune could drop the decisive source. The decisive-source-binding fix is now
landed (§8 of that doc): a designated decisive cell that would be pruned forces a
`quarantine`, the designation is bound into the receipt digest, and the Lean
content-preservation lemmas (`decisive_kept`, `decisive_pruned_not_kept`,
`decisive_receipt_safe_and_preserving`) are axiom-clean in the `AxiomAudit` gate.

H-I's walls are now classified (`AGENTIC_TRACE_H1_WALLS.md`): content preservation
CLOSED; the "derive decisiveness" residual RESOLVED as a necessary import
(machine-checked); the live-state / λ-cliff wall is empirical by design (needs a
model receipt, out of scope for the deductive core); trace-extraction reduced to a
commitment-timing operational note. The empirical artifact is now **pre-registered**
(`AGENTIC_TRACE_H1_CLIFF_TRANSFER_PREREG.md`): a forward-generated, attribution-gated
cliff-transfer test across ≥ 2 stacks, analysis frozen on a synthetic dry-run first,
the real-model sweep operator-gated. The headless harness/validator now lives in
`scripts/cliff_transfer_analysis.py` and `scripts/cliff_transfer_harness.py`: it
generates the λ-graded corpus, emits `(λ, s, O)` rows, runs `analyze_stack`, and
checks `transfer_verdict` on synthetic support/null fixtures. The model sweep still
waits on the operator. Reed-Solomon soundness, unique decoding, and Tauroctony
noninterference remain in place and intact.

Hypothesis IV (generic branch-budget receipt) is unaffected and can still run in
parallel, but the cap-set language should stay reserved until a real finite-field
projection exists.
