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

## Modules

| file | content |
|---|---|
| `Sundogcert/Certificate.lean` | lossiness + soundness core; the two sound reject bounds |
| `Sundogcert/Instance.lean` | a concrete `[4,2]` GF(2) code; an `#eval`-able three-valued verifier |
| `Sundogcert/Scaling.lean` | the `[2m,m]` projection family + the scaling law (proved for all `m`) |
| `Sundogcert/Looseness.lean` | basis-dependence: same code, denser `H`, the bound collapses to 0 |
| `Sundogcert/Degradation.lean` | the general ceiling `colWeightLb ≤ m/density` and the density sawtooth |
| `Sundogcert/CheckCost.lean` | the check-cost theorem: verification is polynomial-time, `O(m·n)` in `|H|` |
| `Sundogcert/ShadowDecay.lean` | a second worked example (real analysis): a lossy *averaged* shadow loses a continuous variable — the Debye–Waller decay |

## Scope

This repository is about a verification *methodology* — a cheap check whose validity anyone can reproduce
— and a clean coding-theory characterization of one bound. It is **not** a cryptographic one-wayness
claim, and not a claim about P versus NP.

The same discipline — *machine-check the deductive core, name the imported wall* — is demonstrated a second
time, on a different kind of math, in [`ShadowDecay.lean`](Sundogcert/ShadowDecay.lean): a real-analysis
Gaussian-averaging (Debye–Waller) decay, proving *why* a continuous signal resists a lossy averaged shadow,
with the modeling assumption (that a real system realizes the averaging) named as the imported wall. The
method travels; it is not a one-off. Toolchain: Lean `v4.30.0`, mathlib `v4.30.0`.
