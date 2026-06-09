# The Syndrome Certificate, Machine-Checked

*A referee-free validity result, and an honest map of its one wall.*

Lean 4 / mathlib v4.30.0 · `lake build` is `sorry`-free, 0-warning, axiom-clean
· commits `9e114ce` → `ae4617b` · 2026-06-07

---

## The claim, in one line

The **soundness and lossiness** of the Sundog syndrome certificate are now *machine-checked* — proved
in Lean, re-checkable by anyone in seconds, with **no referee in the loop**. The proofs depend only on
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
`native_decide`, no trusted compiler step.

This is the lab's first result whose **validity** is author-independent. Reception and significance are
still earned the usual way — kernel-checking buys correctness, not an audience.

## The wall, named first

Lean certifies **soundness + lossiness only.** The certificate's *security* rests on a decoding-hardness
assumption (ISD / SIS one-wayness) that is **imported, not proven** — and provably can't be, here,
because hardness is not a `mathlib` theorem. Every time this work says "Lean-verified," it means the
deductive core, never the hardness. That boundary is written into the source files and is load-bearing
for every claim below.

## What is actually proved

The object is a parity-check `H`, a generator `G` whose rows lie in `ker H`, a body `y = sG + e`
(secret `s`, sparse error `e`), and a three-valued verifier that returns **accept / reject /
quarantine**. Over a generic field `F` (deployed at `F = ZMod 2`):

**Lossiness by algebra — the secret is gone.** The syndrome `H(sG + e) = He` does not depend on `s`
(`syndrome_independent_of_secret`); every message maps to the same syndrome
(`secret_fiber_eq_univ`); there are `|F|ᵏ` bodies per syndrome (`secret_bits_lost`). The shadow throws
away `k·log|F|` bits, and this is forced by the algebra, not assumed.

**Soundness — the certificate cannot lie.**
- `accept_sound` — if the verifier accepts, the body is **Safe**. The only route to *accept* is an
  exhibited light witness, which *is* the proof of safety.
- `no_passing_unsafe` — there is no accepted-but-unsafe body. Spoofing is structurally impossible.
- `reject_sound` — if a sound lower bound rules out every light witness, *reject* implies the body is
  genuinely unsafe.

Two concrete sound lower bounds discharge the *reject* side unconditionally:
- `supportLb` — a nonzero syndrome forces error weight ≥ 1. Cheap, sound, but only fires at `τ = 0`.
- `colWeightLb` — `⌊‖Hy‖ / maxColWeight(H)⌋`, the **non-degenerate** bound that fires at `τ > 0`.

## The trust surface

A human still reads ~30 lines: the `Scheme` definitions (especially `hHG`, the dual-pair law placing
the code in `ker H`) and the meaning of `Safe`. Everything above those definitions is machine-checked.
That is the whole point of formalization here: peer review shrinks from *"trust the proof"* to *"audit
the statement."*

## The bound's physics: one quantity, fully characterized

`colWeightLb` is the load-bearing reject bound, and it has been pinned down from every direction — each
fact kernel-verified:

1. **Sound — always.** `colWeightLb ≤ true witness weight`, at every parity-check basis. Reject never
   fires on a safe body.

2. **Tight on uniform `H` — a scaling law.** For the `[2m, m]` projection family, `colBound = 1` and the
   bound equals `m` exactly (the true minimum coset weight). The reject threshold scales **linearly:**
   `τ_max = m − 1 = n/2 − 1`. Proved for *all* `m` at once (`scaling_law`), with a structural dual-pair
   proof that carries no `2ᵐ` cost.

3. **Loose on dense `H` — basis-dependence.** Take the *same code* with a denser row-equivalent
   parity-check `H' = M·H` (`M` invertible, so `ker H' = ker H`, so `Safe` is provably identical and the
   true distance is unchanged at `m`). The bound **collapses from `m` to `0`** — vacuous — purely from
   the choice of `H` (`looseness`). `colWeightLb` measures the parity-check matrix you picked, **not the
   code it defines.**

4. **Degrades as `≤ m/density`.** In general, `colWeightLb S z ≤ S.m / colBound S.H`
   (`colWeightLb_le_card_div`, any scheme). Sweeping the density `c = 1…m` on one fixed code traces a
   **sawtooth** under the `⌊m/c⌋` envelope — odd density tracks the ceiling, even density collapses to
   `0` by GF(2) parity cancellation. The ceiling is the proven law; the sawtooth is the measured
   behavior beneath it.

Crucially, **(3) and (4) are completeness phenomena, not soundness breaks.** A collapsed bound still
never over-claims: it simply quarantines where it cannot reject. Soundness never depends on the basis;
only the bound's *strength* does.

## Cheap to check, by theorem

The certificate's whole point is an asymmetry — *cheaper to check than to find*. The find-hard side is
imported (above). The **check-cheap side is now a theorem**: one verification query costs `O(m·n)`
operations, linear in the parity-check size `|H|` (`verifyCost_le`), against a transparent cost model
that counts the deployed verifier's worst-case path — the syndrome `H *ᵥ y` is exactly `m·n`
multiplications, everything else lower-order. The cost model is a trust-surface item (audited by a human,
like the scheme definitions); given it, the polynomial bound is kernel-checked.

A consistency hook worth naming: the proven multiplication count `m·n` equals `64·128 = 8192` for the
deployed `[128,64]` regime — *exactly* the lane's measured "flat 8,192-op check." The deductive count and
the empirical op-count agree.

So the asymmetry now reads: **poly-time check, proved here; exp-time find, imported.** That is the
sharpest honest form of the claim — one side machine-checked, one side honestly assumed.

## The frontier: the looseness is the shadow of the hardness

The obvious next ask is a *cheap, basis-robust, tight* bound — one that doesn't degrade when `H` is
chosen adversarially. It does not exist, and the reason is the cleanest part of the story:

> A cheap bound that returned the true minimum coset weight on every basis **would be a fast decoder** —
> it would solve the very problem (information-set decoding) whose hardness the certificate imports.

So the basis-dependence of `colWeightLb` is not a defect to be patched away. It is the **shadow** of the
hardness assumption. Any improvement to a cheap reject bound is bounded by how far you can decode
cheaply — which is exactly the imported wall. The honest open question is quantitative: *how large is
the gap between a cheap bound and the true coset weight, as a function of the decoding margin?* That is a
coding-theory question with a hardness ceiling, not a bug report.

## Reproduce it

```
git clone <sundogcert>            # the Lean project, sibling to the mathlib cache
cd sundogcert
lake exe cache get                # prebuilt mathlib oleans (~6 GB)
lake build                        # re-certifies every theorem; 0 warnings
```

Axiom audit (the referee-free check), e.g.:

```
#print axioms scaling_law
-- 'scaling_law' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The certificate cluster — seven modules, all wired into the default build:
- `Certificate.lean` — lossiness + soundness core, the two bounds.
- `Instance.lean` — a concrete `[4,2]` GF(2) code; an `#eval`-able verifier where `V_supp` quarantines
  but `V_col` rejects the same body at `τ = 1`.
- `Scaling.lean` — the projection family and the scaling law.
- `Looseness.lean` — basis-dependence; the collapse to `0`.
- `Degradation.lean` — the general ceiling and the density sawtooth.
- `CheckCost.lean` — the check-cost theorem: one verification query is `O(m·n)`, linear in `|H|`.
- `CertWall.lean` — types the imported hardness wall: a basis-robust *tight* bound would be a decoder
  (a conditional, `tight_bound_decodes`, never a hardness claim).

(The repo also carries the method's other worked examples — `ShadowDecay`/`ShadowDecayGeneral`,
`HaloGeometry`, `FaradayAB` — and `AxiomAudit`, the build-enforced axiom-clean gate; see
[`METHOD.md`](METHOD.md).)

## What this is *not*

- **Not a cryptographic one-wayness claim.** The ISD/SIS hardness is imported; Lean proves the
  certificate's logic, not the attacker's cost.
- **Not the patent, and not the application framing.** Those stay internal. This document is about the
  verification *methodology* — a cheap check whose validity anyone can reproduce — and a clean
  coding-theory characterization of one bound.
- **Not peer-reviewed significance.** Kernel-checking is validity, not importance. The result is offered
  as a load-bearing pillar precisely because that distinction is the lab's whole discipline: *write the
  statement, check it independently, name the wall.*

---

*Internal-tier draft. Public adaptation (a `SUNDOG_V_*` ledger and a load-bearing-pillar SVG) pending
owner evidence-tier + patent review.*
