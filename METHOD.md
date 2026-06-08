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

## Four demonstrations, four kinds of math

This repository carries the same move on four structurally unrelated objects — which is the point: a
method must travel, or it is a lucky one-off.

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

**3. Halo geometry — geometric optics / calculus.**
(`HaloGeometry`)
- The **minimum-deviation principle**: for a ray through an ice prism, the angular deviation
  `dev(r) = arcsin(n·sin r) + arcsin(n·sin(A−r)) − A` is **stationary at the symmetric ray** `r = A/2`
  (`min_deviation_stationary`: `dev'(A/2) = 0`, by a pure symmetric-ray cancellation) — which is *why* the
  22° halo has the radius `2·arcsin(n·sin(A/2)) − A` (`dev_value`).
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
- **The imported wall:** that `A` is the physical vector potential entering as a loop integral, that `∇χ`
  is the gauge freedom, that the AB phase / Faraday loop EMF *is* this integral, and that the loop encloses
  the flux — physics, named not derived. That nature realizes this as the Aharonov–Bohm effect is named,
  not proved.

## The shared shape (and where it breaks)

Three of the four share a deeper shape: a **map that *determines* a structural invariant while *losing* a
continuous or gauge degree of freedom**. The certificate's syndrome determines the coset and loses the
secret; the averaged shadow keeps the shared label and washes the continuous spread; the closed loop keeps
the topological flux `Φ` (the `H¹` period) and washes the gauge freedom `∇χ` to exactly zero. The same
shape recurs across three different mathematical structures — a finite-field coset, a measure-theoretic
label, a topological period. The halo is *not* that shape — it is a pure geometric extremization — and
that is the stronger point: the discipline is not tied even to that recurring motif. What all four share is
only the method itself: the genuinely hard part — decoding hardness, real-world instantiation, the physical
realization of the geometry, the physical realization of the gauge field — is the import, named on the
outside of the proof rather than smuggled inside it.

## The honest limit

The method proves **deductive cores**; it never proves the **imported wall** — that is the design, not a
gap. What it buys is *honesty under formalization*: it turns "here is what follows, here is what we
assume" from a rhetorical posture into a machine-checkable statement. Every theorem here depends only on
Lean's three foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); the assumptions live in
the prose, named, where a reader can weigh them.

---

*Reproduce: `lake build` re-certifies every theorem; `#print axioms` on any result shows only
`[propext, Classical.choice, Quot.sound]`.*
