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

Promotion status:

- best first candidate. The repo already has the RS machinery and the
  noninterference theorem needed for a small prototype.

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

Promotion status:

- second wave. It needs a detector spec before Lean can do meaningful work.

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

Promotion status:

- promising but measurement-heavy. Do the discrete theorem before claiming the
  ML filter.

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

Promotion status:

- useful immediately as a generic budget receipt; cap-set-specific claims need
  a separate finite-field workbench.

## Deployment Sequence

1. Land the receipt layer.
   Done: `AgenticTrace.lean` compiles and is included in `AxiomAudit.lean`.

2. Build the RS-pruning prototype.
   Started in `scripts/rs_pruning_prototype.py`. It uses a tiny GF(17) RS
   scheme, explicit stale/contradictory trace cells, a deterministic brute-force
   verifier, and emits the trace, pruned trace, survivor polynomial, and receipt
   digest. Run it with:

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
   wall.

   ```sh
   python -m pytest scripts/test_cusp_detector.py -q
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

Promote Hypothesis I first. It is the only candidate where the formal pieces are
already mostly present: Reed-Solomon receipt soundness, unique decoding,
Tauroctony noninterference, and the existing axiom-audited certificate style.
Hypothesis IV can run in parallel as a generic branch-budget receipt, but the
cap-set language should stay reserved until a real finite-field projection
exists.
