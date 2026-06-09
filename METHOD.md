# Machine-check the deductive core, name the imported wall

*A small discipline for separating what a claim proves from what it assumes — checkably.*

---

## The thesis

A claim usually has two parts: what follows **deductively from its structure**, and what it **imports
from outside** — a hardness assumption, a modeling premise, an empirical measurement. The discipline is:

> **Machine-check the first. Name — do not bury — the second.**

The deductive core, once in Lean, has **referee-free validity**: the kernel re-checks it in seconds, so
its correctness is *author-independent*. Peer review of the proof shrinks to an audit of the *statement* —
the definitions (the trust surface) and the single imported assumption, both small and explicit.

This is not a claim that the imported part is true. It is the opposite: a clean, checkable line drawn
around exactly the thing that is *assumed*, so it cannot hide inside the proof.

(Validity is not significance. The kernel buys correctness, not an audience; reception is still earned the
usual way.)

## Five demonstrations, four kinds of math

This repository carries the same move on five worked examples, spanning four structurally distinct kinds of
math — which is the point: a method must travel, or it is a lucky one-off. (Real analysis appears twice: a
concrete Gaussian decay and the general law behind it.)

**1. A syndrome certificate — finite-field algebra.**
(`Certificate`, `Instance`, `Scaling`, `Looseness`, `Degradation`, `CheckCost`)
- **Lossiness:** the syndrome `H y = H e` is independent of the secret `s` — an exact algebraic identity;
  the shadow loses `k·log|F|` bits.
- **Soundness:** `accept ⟹ Safe` (the witness *is* the proof); spoofing is structurally impossible;
  `reject ⟹ ¬Safe` under a sound bound.
- **The reject bound, fully characterized:** sound at every basis; tight on a uniform parity-check (a
  linear scaling law); basis-dependent and loose on a denser one for the same code; capped by
  `‖syndrome‖ / density`.
- **Cheap to check, by theorem:** one verification query is `O(m·n)`, linear in the parity-check size.
- **The imported wall:** the decoding hardness (information-set decoding / SIS one-wayness) — assumed,
  never proved. The basis-dependence of the bound is the *shadow* of exactly this wall.

**2. Lossy averaging — real analysis.**
(`ShadowDecay`)
- A lossy *averaged* shadow **washes a continuous variable** — averaging a fringe `cos(2π(c+λξ)t)` over a
  Gaussian population spread gives `cos(2πct)·e^{−2π²λ²t²}`, the amplitude vanishing as the spread grows
  (`debye_waller`, `resistance`) — while **keeping a shared discrete label** exactly, at *every* spread
  (`determination`).
- **The imported wall:** that a real system instantiates this averaging — a genuine population with an
  honest lossiness knob — is a modeling premise, named not proved.
- *Generalized into its own worked example* (§5, `ShadowDecayGeneral`): the same determine/resist split
  holds for **any** probability measure, and which half fires turns out to be governed by two *independent*
  spectral conditions on the measure — Debye–Waller is just the Gaussian instance.

**3. Halo geometry — geometric optics / calculus.**
(`HaloGeometry`)
- The **minimum-deviation principle**: for a ray through an ice prism, the angular deviation
  `dev(r) = arcsin(n·sin r) + arcsin(n·sin(A−r)) − A` is **stationary at the symmetric ray** `r = A/2`
  (`min_deviation_stationary`: `dev'(A/2) = 0`, by a pure symmetric-ray cancellation) and a **genuine local
  minimum** there (`min_deviation_isLocalMin`: `dev''(A/2) = 2·g''(A/2) > 0`) — which is *why* the 22° halo
  is a bright ring at the radius `2·arcsin(n·sin(A/2)) − A` (`dev_value`).
- **The imported wall:** that ice crystals are hexagonal 60° prisms with `n ≈ 1.31`, that the ray refracts
  out (no total internal reflection — carried as a named differentiability hypothesis), and that the
  bright ring forms at the deviation extremum — physics and observation, named not derived.

**4. Gauge-invariant circulation — vector calculus / topology.**
(`FaradayAB`)
- The observable Aharonov–Bohm phase is the line integral of the vector potential `A` around a **closed
  loop**. A gauge change `A → A + ∇χ` shifts that observable by the **circulation of a gradient field**,
  which is **exactly zero** around a closed loop (`gauge_circulation_zero`:
  `∫₀¹ (χ∘γ)' = χ(γ 1) − χ(γ 0) = 0`, the fundamental theorem of calculus plus `γ 0 = γ 1`) — so the
  observable is **gauge-invariant** (`gauge_invariant_loop`), depending only on the enclosed flux `Φ` (the
  `H¹` topological period), never on the gauge choice. The integrand is faithfully the line-element pairing
  `⟨∇χ, γ'⟩` (`gauge_integrand_eq`, chain rule + Riesz).
- **And the surviving observable is named** (the topological closure): the flux-line field's loop integral
  is the topological count — `∮_{C(c,R)} (z−c)⁻¹ dz = 2πi` for *every* radius `R`
  (`loop_integral_eq_flux`), the **same** value on every enclosing loop (`loop_integral_path_independent`).
  So the observable is exactly the enclosed flux / `H¹` period, path-independent. The first half shows the
  gauge freedom *washes out*; this half shows *what survives* — the flux itself.
- **The imported wall:** that `A` is the physical vector potential entering as a loop integral, that `∇χ`
  is the gauge freedom, that the AB phase / Faraday loop EMF *is* this integral, that the loop encloses the
  flux, and that the complex vortex field `(z−c)⁻¹` is that potential with `2πi` encoding the flux `Φ` (the
  physical observable being the *real* circulation) — physics, named not derived. That nature realizes this
  as the Aharonov–Bohm effect is named, not proved.

**5. The general law — real analysis (the characteristic-function spectrum).**
(`ShadowDecayGeneral`)
- Example 2, generalized. Averaging the fringe `cos(2π(c+λξ)t)` over **any** probability measure `μ` factors
  through `μ`'s **characteristic function**: `∫ cos(2π(c+λξ)t) ∂μ = Re[e^{2πi c t}·charFun μ (2πλt)]`
  (`shadow_decay_charFun`). From that single identity the dichotomy splits into **two independent spectral
  conditions**: **resist** (the continuous signal washes) ⟺ `‖charFun μ‖ → 0` (Riemann–Lebesgue;
  `resistance_general`); **determine** (the shared label survives) ⟺ a **finite centered mean**
  (`determination_general`). Neither implies the other — the **Cauchy** law is the separator: it resists
  (its charFun decays) yet cannot determine (it has no mean). The Gaussian discharges **both**, recovering
  Debye–Waller / example 2 as the instance (`general_recovers_debye_waller`).
- **The imported wall:** the **Cauchy instance** is *named, not built* — mathlib has neither a `charFun` for
  the Cauchy law nor the non-integrability of its mean, so the separator is the motivating boundary,
  established empirically and scoped as future work. And, as in example 2, that a real system instantiates
  this averaging is a modeling premise, named not proved.

## The shared shape (and where it breaks)

Four of the five share a deeper shape: a **map that *determines* a structural invariant while *losing* a
continuous or gauge degree of freedom**. The certificate's syndrome determines the coset and loses the
secret; the averaged shadow keeps the shared label and washes the continuous spread — and its general law
(§5) names *which* spectral condition governs each half; the closed loop washes the gauge freedom `∇χ` to
exactly zero (`gauge_circulation_zero`) and keeps the topological flux `Φ` — the `H¹` period — as the
surviving observable (`loop_integral_eq_flux`). The same shape recurs across a finite-field coset, a
measure-theoretic label and the characteristic-function spectrum that governs it, and a topological period.
The halo is *not* that shape — it is a pure geometric extremization — and that is the stronger point: the
discipline is not tied even to that recurring motif. What all five share is only the method itself: the
genuinely hard part — decoding hardness, real-world instantiation, the physical realization of the geometry,
the physical realization of the gauge field — is the import, named on the outside of the proof rather than
smuggled inside it.

## The honest limit

The method proves **deductive cores**; it never proves the **imported wall** — that is the design, not a
gap. What it buys is *honesty under formalization*: it turns "here is what follows, here is what we
assume" from a rhetorical posture into a machine-checkable statement. Every theorem here depends only on
Lean's three foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); the assumptions live in
the prose, named, where a reader can weigh them.

---

*Reproduce: `lake build` re-certifies every theorem; `#print axioms` on any result shows only
`[propext, Classical.choice, Quot.sound]`.*
