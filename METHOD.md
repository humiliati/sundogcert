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

## Three demonstrations, three kinds of math

This repository carries the same move on three structurally unrelated objects — which is the point: a
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

## The shared shape (and where it breaks)

The first two share a deeper shape: a **lossy shadow that *determines* a discrete / structural invariant
while *losing* a continuous / large fiber** — the certificate's syndrome determines the coset and loses
the secret; the averaged shadow keeps the shared label and washes the continuous one. The halo is *not*
that shape — it is a pure geometric extremization — and that is the stronger point: the discipline is not
tied to one motif. What all three share is only the method itself: the genuinely hard part — decoding
hardness, real-world instantiation, the physical realization of the geometry — is the import, named on
the outside of the proof rather than smuggled inside it.

## The honest limit

The method proves **deductive cores**; it never proves the **imported wall** — that is the design, not a
gap. What it buys is *honesty under formalization*: it turns "here is what follows, here is what we
assume" from a rhetorical posture into a machine-checkable statement. Every theorem here depends only on
Lean's three foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); the assumptions live in
the prose, named, where a reader can weigh them.

---

*Reproduce: `lake build` re-certifies every theorem; `#print axioms` on any result shows only
`[propext, Classical.choice, Quot.sound]`.*
