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

## Seven demonstrations, six kinds of math

This repository carries the same move on seven worked examples, spanning six structurally distinct kinds of
math — which is the point: a method must travel, or it is a lucky one-off. (Real analysis appears twice: a
concrete Gaussian decay and the general law behind it. The sixth is a computational-complexity Karp
reduction — the method's payoff for the certificate of example 1. The seventh is a finite audit game
quantified over *all* decidable verifiers.)

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
- **The separator, now proven** (`ShadowDecayCauchy`): the Cauchy law really does come apart — it
  **resists** (`cauchy_charFun_tendsto_zero`: its charFun decays by Riemann–Lebesgue, since the Cauchy
  density is `L¹` — *no variance needed*) yet **cannot determine** (`cauchy_no_mean`: `¬ Integrable id`, by
  an `x⁻¹` tail comparison), so `resist` and `determine` are *logically independent* (`cauchy_is_separator`).
  This closes the wall `ShadowDecayGeneral` named as future work.
- **The residual wall:** only the *exact* value `charFun(cauchy) s = e^{−γ|s|}` (the Poisson kernel) stays
  named-not-built — its *decay* is proved, which is all the separator needs; the exact contour computation
  is a candidate mathlib upstream. And, as in example 2, that a real system instantiates this averaging is a
  modeling premise, named not proved.
- **Which measures resist — the sharp boundary** (`ShadowDecayLattice`): the charFun-decay condition separates
  **absolutely-continuous** populations (resist by Riemann–Lebesgue — `absCont_resists`, generalizing the
  Gaussian/uniform/Cauchy) from **lattice/atomic** ones (survive — the symmetric two-point has `charFun = cos`,
  which recurs to `1` and never decays, so its averaged shadow `cos(2πct)·cos(2πλat)` *recurs* instead of
  washing). It is **orthogonal to variance** (`resist_orthogonal_to_variance`): the Cauchy resists with
  *infinite* variance, the bounded two-point survives with finite everything. Honest limit, named in the
  module: this is `AC ⟹ resist` and `lattice ⟹ survive`, *not* `resist ⟺ AC` — singular-continuous Rajchman
  measures resist too; AC and lattice only *bracket* the Rajchman boundary.

**6. A faithful Karp reduction — combinatorics / computational complexity.**
(`SATNPHard`, `VarWheel`, `ClauseGadget`, `SATReductionIncidence`, `ThreeDMReindex`, `SATReduction`,
`SATReductionForward`, `SATReductionReverse`, `SATReductionMain`, on `MatchingNPHard` / `DecodingNPHard`)
- The deductive core is a **reduction correctness**, proved as an `iff`: `Satisfiable φ ↔
  Decodes (reduce3DM (reduce φ)) (2·m·n)` (`sat_iff_decodes`). A 3-CNF formula is satisfiable exactly when
  the bounded-weight GF(2) decoding instance it maps to — through the Garey–Johnson chain
  `3SAT → 3DM → X3C → decoding` — decodes within the weight bound. Both directions are machine-checked
  combinatorics: the **forward** builds the perfect matching from an assignment (variable-wheel, clause, and
  garbage gadgets, the leftover tips absorbed by a counted bijection); the **reverse** reads an assignment
  back out of any perfect matching. The wheel gadget admits exactly the two constant covers — the two truth
  values — and the clause gadget's polarity bridge ties a tip being free to its literal being true.
- **The imported wall:** the NP complexity *class*, the *poly-time-ness* of the reduction maps (each built
  and proved correct, but never timed), and 3SAT's **own** NP-hardness — Cook–Levin, the deep terminal wall,
  in no proof assistant to date. What is checked is that the reduction is *faithful*; the hardness is the
  import, so any "NP-hard" reading stays conditional on `P ≠ NP`. This is **not** a claim about P versus NP.
- This is the method's *payoff* for example 1: the certificate's decoding-hardness assumption is no longer
  opaque — a checked reduction anchors it to the canonical NP-complete problem, leaving only the
  (unformalizable-in-mathlib) complexity wrapping named on the outside of the proof.

**7. An audit asymmetry — finite decidability / a game over verifiers.**
(`AuditCost`)
- In one finite setting (populations `u : Fin n → ℚ`, observation channel `(report, pooledMean u)`):
  a full-access **audit game** is sound and complete against an adversarial reporter at a proven linear
  op-cost (`audit_asymmetry`, `auditCost_le ≤ 3n+2` — the CheckCost cost-model discipline reused), while
  **every** decidable verifier seeing only the pooled channel is **per-unit blind** — an explicit
  same-mean fiber pair realizes any prescribed per-unit difference with identical verdicts for every
  report (`pooled_channel_blind`), so *no* channel verifier is sound-and-complete for *any* per-unit
  claim (`no_verifier_checks_perUnit`). Non-vacuity is proved, not asserted: at `n = 1` the channel
  *determines* the unit (`n1_channel_determines`), and the blind pair is *separated* one statistic up,
  by the second moment (`secondMoment_separates`) — the information is present in the population; the
  channel is what is blind.
- **The imported wall:** the cost model is the trust surface (exactly as in example 1's `CheckCost`),
  and that any real oversight interface *is* a pooled-mean channel is a modeling premise, named not
  proved. The blindness proofs are short by design — data processing is short; the content is the
  statement's quantifier (for ALL verifiers) and the explicit construction.
- This is the finite, verifier-quantified sibling of §5's determine/resist law: where §5 shows one
  statistic's limit washes, this quantifies the blindness over every decidable auditor of the channel.

## The shared shape (and where it breaks)

Five of the seven share a deeper shape: a **map that *determines* a structural invariant while *losing* a
continuous or gauge degree of freedom**. The certificate's syndrome determines the coset and loses the
secret; the averaged shadow keeps the shared label and washes the continuous spread — and its general law
(§5) names *which* spectral condition governs each half; the closed loop washes the gauge freedom `∇χ` to
exactly zero (`gauge_circulation_zero`) and keeps the topological flux `Φ` — the `H¹` period — as the
surviving observable (`loop_integral_eq_flux`); the pooled-mean channel (§7) keeps the population mean and
loses every per-unit coordinate — there the lost half is certified against *all* decidable verifiers, not
one statistic. The same shape recurs across a finite-field coset, a measure-theoretic label and the
characteristic-function spectrum that governs it, a topological period, and a finite audit channel.
Neither the halo (a pure geometric extremization) nor the Karp reduction (a combinatorial *equivalence*
whose import is hardness, not a model or a measurement) is that shape — and that is the stronger point: the
discipline is not tied even to that recurring motif. What all seven share is only the method itself: the
genuinely hard part — decoding hardness (and, behind the reduction, Cook–Levin), real-world instantiation,
the physical realization of the geometry, the physical realization of the gauge field — is the import, named
on the outside of the proof rather than smuggled inside it.

## The honest limit

The method proves **deductive cores**; it never proves the **imported wall** — that is the design, not a
gap. What it buys is *honesty under formalization*: it turns "here is what follows, here is what we
assume" from a rhetorical posture into a machine-checkable statement. Every theorem here depends only on
Lean's three foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); the assumptions live in
the prose, named, where a reader can weigh them.

---

*Reproduce: `lake build` re-certifies every theorem; `#print axioms` on any result shows only
`[propext, Classical.choice, Quot.sound]`.*
