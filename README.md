# sundogcert

**A machine-checked syndrome certificate: soundness + lossiness in Lean 4.**

The *soundness* and *lossiness* of a syndrome certificate are proved in Lean 4 (mathlib v4.30.0),
`sorry`-free and **axiom-clean** — every theorem depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`, no trusted compiler step.
That makes the result **referee-free**: the kernel re-checks it in seconds, so its *validity* is
author-independent.

> **The wall, stated up front.** Lean certifies **soundness + lossiness only.** The certificate's
> security rests on a decoding-hardness assumption (information-set decoding / SIS one-wayness) that is
> **imported, not proven** here — hardness is not a mathlib theorem. "Lean-verified" always means the
> deductive core, never the hardness.

## What is proved

- **Lossiness by algebra** — the syndrome `H(sG + e) = He` is independent of the secret `s`; there are
  `|F|ᵏ` bodies per syndrome. The shadow loses `k·log|F|` bits, forced by the algebra.
- **Soundness** — `accept ⟹ Safe` (the witness *is* the proof); no accepted body is unsafe (spoofing is
  structurally impossible); `reject ⟹ ¬Safe` under a sound lower bound.
- **The reject bound, fully characterized** — `colWeightLb` is sound at every basis; *tight* on a uniform
  parity-check (a linear scaling law, reject threshold `τ = n/2 − 1`); *basis-dependent and loose* on a
  denser row-equivalent matrix for the same code (it collapses to 0); and capped by `‖syndrome‖ / density`
  in general. Its looseness is the **shadow of the hardness assumption** — a cheap, basis-robust, tight
  bound would be a fast decoder.
- **Cheap to check, by theorem** — one verification query costs `O(m·n)` operations, linear in the
  parity-check size `|H|` (`verifyCost_le`), against a transparent (human-audited) cost model. The
  proven multiplication count `m·n` equals the deployed `[128,64]` regime's measured 8,192-op check.
  This is the *check-cheap* half of "cheaper to check than to find"; the *find-hard* half stays imported.

See [`WRITEUP.md`](WRITEUP.md) for the full consolidation.

## A machine-checked Karp reduction — the hardness wall, pushed inward

The certificate imports exactly one security assumption: that its bounded-weight GF(2) **decoding**
problem is hard. That assumption is now **anchored to a canonical NP-complete problem by a
machine-checked reduction.** The chain

> **3SAT ≤ 3DM ≤ X3C ≤ bounded-weight GF(2) decoding**

is formalized end to end, and its top-level correctness is an `iff` (`SATReductionMain.sat_iff_decodes`):

```lean
theorem sat_iff_decodes (φ : Formula n m) :
    Satisfiable φ ↔ Decodes (reduce3DM (reduce φ)) (2 * m * n)
```

A 3-CNF formula `φ` is satisfiable **if and only if** the decoding instance it maps to — via the
Garey–Johnson `3SAT → 3-dimensional-matching` gadget reduction, then `3DM → exact-cover-by-3-sets`,
then `X3C → decoding` — decodes within the weight bound. **Both directions** are proved: the
*forward* direction builds the perfect matching explicitly from a satisfying assignment
(variable-wheel + clause + garbage gadgets, the leftover tips absorbed by a counted bijection); the
*reverse* direction reads a satisfying assignment back out of any perfect matching. Axiom-clean, like
everything else here.

**What is checked is the *reduction correctness*** — the logical equivalence between the SAT instance
and its decoding image (the many-one / Karp correctness of the map). This pushes the certificate's
"decoding is hard" assumption inward: from an opaque premise to *"at least as hard as 3SAT, modulo the
standard complexity wrapping."*

**The imported wall, named.** That wrapping is exactly what stays imported — mathlib has no
complexity-theory framework:
- the **NP complexity class** itself (a resource-bounded notion, not formalized);
- the **poly-time-ness** of the reduction (each map is built and proved correct, but its running time
  is never modeled — the maps are visibly local, yet "polynomial" is unstated);
- **3SAT's own NP-hardness** — Cook–Levin, the deep terminal wall that sources every Karp-reduction
  hardness claim, formalized in no proof assistant to date.

So any "NP-hard" reading of the decoding problem stays **conditional on `P ≠ NP`** and on the imported
Cook–Levin hardness of 3SAT. This repository proves the reduction is *faithful*; it does **not** prove
decoding is hard, and makes **no** claim about P versus NP.

## Build

```sh
lake exe cache get   # prebuilt mathlib oleans
lake build           # re-certifies every theorem; 0 warnings
```

Axiom audit (the referee-free check):

```lean
#print axioms scaling_law
-- 'scaling_law' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This audit is **build-enforced**: [`AxiomAudit.lean`](Sundogcert/AxiomAudit.lean) pins each headline
theorem's axiom set with `#guard_msgs`, so a `sorry`, a `native_decide`, or any extra axiom slipping into a
proof makes `lake build` **fail**. The referee-free promise can no longer silently regress.

## Modules

| file | content |
|---|---|
| `Sundogcert/Certificate.lean` | lossiness + soundness core; the two sound reject bounds |
| `Sundogcert/Instance.lean` | a concrete `[4,2]` GF(2) code; an `#eval`-able three-valued verifier |
| `Sundogcert/Scaling.lean` | the `[2m,m]` projection family + the scaling law (proved for all `m`) |
| `Sundogcert/Looseness.lean` | basis-dependence: same code, denser `H`, the bound collapses to 0 |
| `Sundogcert/Degradation.lean` | the general ceiling `colWeightLb ≤ m/density` and the density sawtooth |
| `Sundogcert/CheckCost.lean` | the check-cost theorem: verification is polynomial-time, `O(m·n)` in `|H|` |
| `Sundogcert/CertWall.lean` | *types* the imported hardness wall: `minCosetWeight` is a code invariant while `colWeightLb` is basis-dependent, so a cheap basis-robust *tight* bound would be a decoder — a **conditional** (`tight_bound_decodes`), never a hardness claim |
| `Sundogcert/ShadowDecay.lean` | a second worked example (real analysis): a lossy *averaged* shadow loses a continuous variable — the Debye–Waller decay |
| `Sundogcert/ShadowDecayGeneral.lean` | a fifth worked example (real analysis, generalizing the second): the determine/resist split for **any** probability measure — resist ⟺ `‖charFun μ‖→0` (Riemann–Lebesgue), determine ⟺ a finite centered mean (two *independent* spectral conditions; the Cauchy law is the separator) — with Debye–Waller the Gaussian instance |
| `Sundogcert/ShadowDecayCauchy.lean` | *closes* the named wall of `ShadowDecayGeneral` (not a separate example): the Cauchy law is the **proven** separator — it resists (`cauchy_charFun_tendsto_zero`, by Riemann–Lebesgue) yet cannot determine (`cauchy_no_mean`, `¬ Integrable id`), so resist and determine are logically independent; only the *exact* `charFun = e^{−γ|s|}` stays named |
| `Sundogcert/ShadowDecayLattice.lean` | *sharpens* `ShadowDecayGeneral`'s resist condition (not a separate example): the charFun-decay is the boundary between **absolutely-continuous** populations (resist, `absCont_resists`) and **lattice/atomic** ones (survive — the two-point `charFun = cos` recurs to 1, `twoPoint_shadow_survives`), and it is **orthogonal to variance** (`resist_orthogonal_to_variance`: Cauchy ∞-variance resists, bounded two-point survives). Honest limit: brackets the Rajchman boundary, does *not* claim `resist ⟺ AC` |
| `Sundogcert/AuditCost.lean` | a seventh worked example (finite decidability / audit game): a proved-cheap full-access audit — sound + complete against an adversarial reporter at `auditCost ≤ 3n+2` — paired with **∀-verifier blindness** of the pooled-mean channel: an explicit same-mean fiber pair defeats *every* decidable channel verifier at any prescribed per-unit `δ` (`pooled_channel_blind`), so no channel verifier checks any per-unit claim (`no_verifier_checks_perUnit`). Non-vacuity proved: `n = 1` determines; the second moment separates the blind pair |
| `Sundogcert/HaloGeometry.lean` | a third worked example (geometric optics): the 22° halo's minimum-deviation principle, proved a **genuine local minimum** at the symmetric ray (`min_deviation_isLocalMin` — the bright ring forms at the deviation extremum) |
| `Sundogcert/FaradayAB.lean` | a fourth worked example (vector calculus / topology): the Aharonov–Bohm gauge-invariance (a gradient's closed-loop circulation is zero) *and* its topological closure (the loop integral *is* the enclosed flux, `∮(z−c)⁻¹ = 2πi`, path-independent) |
| `Sundogcert/DecodingNPHard.lean` | the chain's last link: exact-cover-by-3-sets ≤ bounded-weight GF(2) decoding (both directions, unconditional) |
| `Sundogcert/MatchingNPHard.lean` | `3DM ≤ X3C`, composed through to decoding (`threeDM_iff_Decodes`) |
| `Sundogcert/SATNPHard.lean` | the 3SAT problem (CNF / assignment / satisfies) + `decide`-validated SAT/UNSAT examples |
| `Sundogcert/VarWheel.lean` | the truth-setting "wheel" gadget: exactly two valid covers = the two truth values |
| `Sundogcert/ClauseGadget.lean` | the clause gadget + the polarity bridge (a literal's tip is free ⟺ the literal is true) |
| `Sundogcert/SATReduction.lean` | the global assembly: coordinate types, the reduction `reduce`, cardinalities, chain-connect |
| `Sundogcert/ThreeDMReindex.lean` | the reindexing bridge: a matching over a `Fintype` index ↔ the `Fin s`-indexed `ThreeDM` |
| `Sundogcert/SATReductionIncidence.lean` | which triple-indices cover each node — the shared incidence lemmas |
| `Sundogcert/SATReductionReverse.lean` | reverse correctness: a perfect matching yields a satisfying assignment |
| `Sundogcert/SATReductionForward.lean` | forward correctness: a satisfying assignment yields a perfect matching |
| `Sundogcert/SATReductionMain.lean` | the composition — `Satisfiable φ ↔ Decodes …`, closing `3SAT ≤ 3DM ≤ X3C ≤ Decodes` |
| `Sundogcert/AxiomAudit.lean` | the **self-enforcing axiom-clean gate**: every headline theorem's `#print axioms` pinned by `#guard_msgs` — a `sorry`/`native_decide`/extra-axiom regression fails the build |

## Agentic trace slate

[`AGENTIC_TRACE_HYPOTHESES.md`](AGENTIC_TRACE_HYPOTHESES.md) stages the
trace-conditioned agentic-search hypotheses from the current research brief.
Its first formal receipt layer is
[`Sundogcert/AgenticTrace.lean`](Sundogcert/AgenticTrace.lean): accepted RS
receipts are safe, RS decodings are unique inside the radius, trace-gated
policies are noninterferent under trace-preserving attacks, and finite branch
traces cannot exceed their certified slots. The speculative model-measurement
claims remain named imported walls.

The first executable prototype is
[`scripts/rs_pruning_prototype.py`](scripts/rs_pruning_prototype.py). It runs a
tiny deterministic GF(17) RS-pruning demo over stale/contradictory trace cells
and emits verifier-checkable receipts: an RS pruning receipt plus a finite
branch-budget receipt that marks overflow branches as `structural-zero`:

```sh
python scripts/rs_pruning_prototype.py
python -m pytest scripts/test_branch_budget_receipt.py -q
python -m pytest scripts/test_rs_pruning_prototype.py -q
python -m pytest scripts/test_discrete_holonomy_receipt.py -q
python -m pytest scripts/test_cusp_detector.py -q
```

The discrete-loop theorem for the next lane lives in
[`Sundogcert/DiscreteHolonomy.lean`](Sundogcert/DiscreteHolonomy.lean). It proves
that finite gauge sums telescope to endpoint differences and close to zero on
closed loops. The toy runtime receipt is
[`scripts/discrete_holonomy_receipt.py`](scripts/discrete_holonomy_receipt.py);
it checks integer trace loops only and keeps the attention-mapping claim outside
the proof.

The sampled cusp detector for context-decay experiments lives in
[`scripts/cusp_detector.py`](scripts/cusp_detector.py). It checks exact
five-point finite-difference jets and emits `accept`, `structural-zero`, or
verifier-checkable `quarantine`; it does not claim that any vector-memory system
has already been mapped to a Whitney cusp.

The H-I cliff-transfer empirical leg is pre-registered in
[`AGENTIC_TRACE_H1_CLIFF_TRANSFER_PREREG.md`](AGENTIC_TRACE_H1_CLIFF_TRANSFER_PREREG.md).
Its headless lock lives in
[`scripts/cliff_transfer_analysis.py`](scripts/cliff_transfer_analysis.py) and
[`scripts/cliff_transfer_harness.py`](scripts/cliff_transfer_harness.py): fixture
mode builds the lambda-graded corpus, emits `(lambda, s, O)` rows, and validates
the SUPPORT/K1/K2 controls without making model calls.

## Scope

This repository is about a verification *methodology* — a cheap check whose validity anyone can reproduce
— and a clean coding-theory characterization of one bound. It is **not** a cryptographic one-wayness
claim, and not a claim about P versus NP: the `3SAT ≤ 3DM ≤ X3C ≤ decoding` chain machine-checks the
reduction's *correctness* only, while the NP class, poly-time-ness, and 3SAT's Cook–Levin hardness stay
imported, named on the outside.

The same discipline — *machine-check the deductive core, name the imported wall* — is demonstrated a second
time, on a different kind of math, in [`ShadowDecay.lean`](Sundogcert/ShadowDecay.lean): a real-analysis
Gaussian-averaging (Debye–Waller) decay, proving *why* a continuous signal resists a lossy averaged shadow,
with the modeling assumption (that a real system realizes the averaging) named as the imported wall. See
[`METHOD.md`](METHOD.md) for the discipline stated in full across all seven worked examples — six kinds of
math (finite-field algebra, real analysis, geometric optics, vector calculus / topology, a
computational-complexity Karp reduction, and a finite audit game quantified over all decidable verifiers),
with real analysis carrying both the concrete Gaussian decay and its general characteristic-function law.
The method travels; it is not a one-off. Toolchain: Lean `v4.30.0`, mathlib `v4.30.0`.
