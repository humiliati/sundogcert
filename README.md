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

## The Order-Relative Resolution Law — a synthesis core, eight grounded axes

The repository's worked examples keep meeting the same shape: a bounded process
*determines* some targets and *resists* others, and which one you get is set by an
order. That shape is proved once, as a schema ([`OrderRelative.lean`](Sundogcert/OrderRelative.lean)):

> **A bounded process with budget `k` resolves a target iff the target's order `≤ k`.
> The determine/resist split is finite-order vs infinite-order.** (`Resolves k t ↔ ord t ≤ k`)

**Eight instance families plus the resist pole** ground the schema, each a genuinely
different filtration: parity-determination, coordinate-locality, search-reachability
(`√2` an *earned* resist pole `⊤`, not a fiat one), radical-reach, spectral/moment (the
Cauchy law), algebraic degree, cohomological torsion-vs-free (the Aharonov–Bohm `H¹`
period), and the **surface-window** axis — over bracket strings the order-blind count
vector *determines* nesting depth (`bagSufficient_depth`) yet can **never** determine
the stack-top (`not_bagSufficient_stackTop`; witness: `([` vs `[(` share every count and
disagree on the state), and the resistance holds at **every window order**
(`stackTop_resists_every_window`, σ_surface = ∞). The surface pair is axiom-lean beyond
the house standard: `[propext, Quot.sound]` — no `Classical.choice`.

The guard rails are theorems too. `order_is_schema_not_scalar` blocks the
universal-scalar misread — orders are **incomparable across instances**; the law is a
schema, not one number. The **composition law** is a single general lemma
(`orderOf_prod_eq_lcm` — join by lcm, not max), with both walls proved
(`compose_lcm_not_max`: `4 ⊕ 6 = 12`, not `6`; `converse_fails`: join-homomorphic does
not mean group-order). The **structure theorem** (`structure_mode_vector`) identifies
the difficulty vector with a group's invariant-factor vector — the scalar order is its
lattice join, a lossy projection of a structured object. And an **approximation
dimension** (`OrderRelativeApprox*`) proves that approximating to any tolerance always
succeeds while *exact* representation stays order-relative — an unbounded ladder against
a hard resist pole.

| module group | what it proves |
|---|---|
| [`OrderRelative`](Sundogcert/OrderRelative.lean) | the schema + the law `Resolves k t ↔ ord t ≤ k`; `resolvable_iff_finite` / `resists_iff_infinite`; the honesty guard `order_is_schema_not_scalar` |
| axis instances — across `OrderRelative`, `ParityNoSufficientStat`, and `OrderRelative{AlgDegree, Cohomology, Moment, RadicalQuotient}` | the eight grounded filtrations: parity `ord = n`; prefix-locality `ord = d`; search-reach with `√2` an earned `⊤`; radical order 2 for `√2`; finite-mean vs Cauchy `⊤`; algebraic degree 2 vs denominator `⊤` on the lane optimum `(9+√17)/32`; torsion `m` vs free `⊤` (the `H¹` winding); mode-vectors proving one object carries divergent orders across axes |
| composition + structure — `OrderRelative{Compose, ComposeLaw, RadicalCompose, Converse, Grading, Structure, Keyed, MomentConv, SearchNeg}` | `orderOf_prod_eq_lcm` proved once with the group-order axes as instances; sharpness and converse walls; `structure_mode_vector`; the keyed/graded composition boundaries; the moment axis join-homomorphic under convolution, the search axis proved **not** join-homomorphic — both sides of the composition boundary machine-checked |
| approximation — `OrderRelativeApprox` / `…Graded` / `…Ladder` / `…LadderK` | ε-approximation always works; *exact* representation is order-relative |
| **surface-window** — [`SurfaceBag`](Sundogcert/SurfaceBag.lean), [`SurfaceBagGraded`](Sundogcert/SurfaceBagGraded.lean) | the order axis: the bag determines depth, never the stack-top, at every window order (σ_surface = ∞); axiom-lean `[propext, Quot.sound]` |

**The imported wall, named.** The schema is about labels and statistics, never about any
model or named hard problem: not P-vs-NP, not learnability, not a claim about what
neural networks "know." One boundary of the surface-window axis has been *measured*
off-repo — on real code, a small pretrained language model reads the stack-top exactly
where count statistics provably collapse, gated on matched baselines, and the
high-dimensional version of the same question was run to a pre-registered negative —
but that empirical half lives with its receipts on the Sundog site's
machine-checked-method ledger; nothing about it is a theorem here. Everything in this
section is `AxiomAudit`-gated like the rest of the repository.

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
| `Sundogcert/StraightLineCost.lean` | the H-A1 cost bridge: a shared `StraightLineProgram.cost` / `costOf` interface whose instances are the constructive ReLU-DAG gate count (`RProg.gateCount`) and the certificate verifier op-count (`verifyCost`). The existing linear bounds lift through the same ledger (`compileToDag_cost_le`, `verifier_cost_le`), with `shared_cost_instances` recording the bounded unification: same cost measure, different circuits on the find/check axis |
| `Sundogcert/ShortestPathCert.lean` | the find/check ledger's **optimization** instance: a shortest-path *feasible potential* `dist v ≤ dist u + c` is a cheap-to-check (`O(E+V)`) **exact** optimality certificate. `feasible_le_walk` proves it lower-bounds **every** walk weight (the LP-dual "nothing is shorter" half); `tree_achieves` + **`cert_isLeast`** prove the tight tree *achieves* it, so `dist` `IsLeast` the walk-weight set — `dist` *is* the true shortest distance, exactly. Routed through the same `costOf` ledger as the syndrome verifier and the ReLU-DAG gate count. *Finding* the tree (the search) is the named wall |
| `Sundogcert/CertWall.lean` | *types* the imported hardness wall: `minCosetWeight` is a code invariant while `colWeightLb` is basis-dependent, so a cheap basis-robust *tight* bound would be a decoder — a **conditional** (`tight_bound_decodes`), never a hardness claim |
| `Sundogcert/ShadowDecay.lean` | a second worked example (real analysis): a lossy *averaged* shadow loses a continuous variable — the Debye–Waller decay |
| `Sundogcert/ShadowDecayGeneral.lean` | a fifth worked example (real analysis, generalizing the second): the determine/resist split for **any** probability measure — resist ⟺ `‖charFun μ‖→0` (Riemann–Lebesgue), determine ⟺ a finite centered mean (two *independent* spectral conditions; the Cauchy law is the separator) — with Debye–Waller the Gaussian instance |
| `Sundogcert/ShadowDecayCauchy.lean` | *closes* the named wall of `ShadowDecayGeneral` (not a separate example): the Cauchy law is the **proven** separator — it resists (`cauchy_charFun_tendsto_zero`, by Riemann–Lebesgue) yet cannot determine (`cauchy_no_mean`, `¬ Integrable id`), so resist and determine are logically independent; only the *exact* `charFun = e^{−γ|s|}` stays named |
| `Sundogcert/ShadowDecayLattice.lean` | *sharpens* `ShadowDecayGeneral`'s resist condition (not a separate example): the charFun-decay is the boundary between **absolutely-continuous** populations (resist, `absCont_resists`) and **lattice/atomic** ones (survive — the two-point `charFun = cos` recurs to 1, `twoPoint_shadow_survives`), and it is **orthogonal to variance** (`resist_orthogonal_to_variance`: Cauchy ∞-variance resists, bounded two-point survives). Honest limit: brackets the Rajchman boundary, does *not* claim `resist ⟺ AC` |
| `Sundogcert/AuditCost.lean` | a seventh worked example (finite decidability / audit game): a proved-cheap full-access audit — sound + complete against an adversarial reporter at `auditCost ≤ 3n+2` — paired with **∀-verifier blindness** of the pooled-mean channel: an explicit same-mean fiber pair defeats *every* decidable channel verifier at any prescribed per-unit `δ` (`pooled_channel_blind`), so no channel verifier checks any per-unit claim (`no_verifier_checks_perUnit`). Non-vacuity proved: `n = 1` determines; the second moment separates the blind pair |
| `Sundogcert/HaloGeometry.lean` | a third worked example (geometric optics): the 22° halo's minimum-deviation principle, proved a **genuine local minimum** at the symmetric ray (`min_deviation_isLocalMin` — the bright ring forms at the deviation extremum) |
| `Sundogcert/FaradayAB.lean` | a fourth worked example (vector calculus / topology): the Aharonov–Bohm gauge-invariance (a gradient's closed-loop circulation is zero) *and* its topological closure (the loop integral *is* the enclosed flux, `∮(z−c)⁻¹ = 2πi`, path-independent) |
| `Sundogcert/CircuitNet.lean` | a worked example (circuit complexity / approximation theory): **exact** compilation of tropical (piecewise-linear) circuits into ReLU networks (`compile_eval`, via `max p q = q + relu(p−q)`), with a **linear depth** bound (`compile_depth_le ≤ 4·depth`) and the min-plus / Bellman–Ford gates the all-pairs-shortest-paths circuit is built from, each proved exact (`bellmanStep_compiles_exactly`). **The linear gate-count wall is now closed**: a sharing-aware ReLU DAG (`RProg`, wires reused by index) and a recursive compiler `compileToDag : Trop n → RProg n _` fold the shared-wire max gadget (`max p q = q + relu(p−q)`, exactly four gates with `q` reused — `appendMax_gate_count`/`appendMax_eval`) over a tropical tree, proving an `N`-node tree compiles to a `≤ 4N`-gate DAG (`compileToDag_gate_count`) that computes it **exactly** (`compileToDag_eval`). Remaining wall: only the analytic gates (reciprocal/radical), which are approximable, not exact; this is the exact ε = 0 piecewise-linear case of Kratsios et al. (arXiv:2606.26705) Thm 3.2 / Cor 5.1 |
| `Sundogcert/CancellationFree.lean` | locates the **monotone-vs-general wall**. The cancellation-free (monotone, max-plus polynomial) fragment `IsMono` of `Trop` (no negative scaling) computes exactly **monotone** functions (`monotone_of_isMono`; and its compiled ReLU net), and is **proper** — `abs` is in the general fragment but not monotone, so no cancellation-free circuit computes it (`abs_not_isMono`). The reverse compilation `decompile : Net → Trop` (`decompile_eval`, exact — every ReLU net is a tropical-rational circuit) plus the imported-bound transfer `monotone_transfer` (a Jerrum–Snir monotone max-gate bound, given as an explicit hypothesis, becomes a cancellation-free ReLU gate lower bound via `compileToDag_maxCount_ge`) sandwich the wall: monotone `(min,+)` lower bounds transfer to the cancellation-free fragment but **not** to general ReLU (the natural-proofs barrier, imported — `decompile` of a general net is a *general* `Trop`, not `IsMono`) |
| `Sundogcert/DepthSeparation.lean` | **depth = computation**, machine-checked: the tent map `T(x)=1−|2x−1|` is a tropical circuit (`tent_eval`); its `d`-fold composition `iterTent d` computes `T^[d]` (`iterTent_eval`) at depth **linear in d** (`iterTent_depth_le`), yet `tent_iterate_dyadic` proves `T^[d](j/2^d)=parity(j)` — the `2^d` dyadic samples alternate `0,1,0,1,…`, so the depth-`O(d)` circuit has **≥ 2^d linear pieces**: exponential expressivity from linear depth (Telgarsky's sawtooth as a tropical circuit). Named wall: the matching depth-vs-*width* lower bound for shallow nets (Telgarsky 2016), imported |
| `Sundogcert/RegionCount.lean` | **linear regions are an exact (realization-independent) tropical invariant**: because `compile` is exact, the compiled ReLU net realizes the *identical* function as its source tropical circuit (`realize1_compile`), so its linear-region structure is intrinsic — not a property of the ReLU wiring (`affine_compile_iff` kills `REGIONS_NOT_INTRINSIC`). Region anchor `max_two_not_affine`: a `max` of two distinct-slope affines is not globally affine (≥ 2 regions), via "an affine function `≥ 0` everywhere has zero slope". Named wall: the exact region-count *formula* for general circuits (tropical-hypersurface chambers / Newton-polytope mixed volume) — the literature's bounds-only part |
| `Sundogcert/FoldCancellation.lean` | **folding needs cancellation** — fuses the monotone wall (`CancellationFree`) with the depth witness (`DepthSeparation`). *Negative (sharp) half:* no cancellation-free (`IsMono`) circuit computes the `d`-fold tent for `d ≥ 1` (`isMono_not_iterTentFun` / `isMono_not_iterTent`), via `isMono_no_fold` — a monotone circuit cannot be `1` at `1/2^d` then `0` at the larger `2/2^d`; so the *same* witness that achieves `2^d` regions is unrealizable cancellation-free, i.e. depth's exponential expressivity is cancellation-essential. *Positive (qualitative) half:* an `IsMono` circuit's 1-D realization is `Monotone` (`isMono_realize1_monotone`), so every super-level set `{x ∣ c ≤ f x}` is an upper set (`isMono_superlevel_isUpperSet`) — no fold-back at any level — while the tent's `{x ∣ ½ ≤ T^[2] x}` is *not* an upper set (`tent_superlevel_not_isUpperSet`). The quantitative count is discharged downstream by `PieceCover.lean`/`RegionPoly.lean`, which turn the no-fold mechanism into the linear piece bound. |
| `Sundogcert/PieceCover.lean` | **the quantitative N-1 half** (monotone depth is region-*polynomial*). A bounded piece certificate `HasPieceCover f k` (`f` affine off a finite cut set of size `≤ k−1`, i.e. `≤ k` affine pieces) — an upper bound on the linear-region count with no exact chamber-count object. The load-bearing lemma `hasPieceCover_comp_mono`: `HasPieceCover h n → HasPieceCover g m → Monotone h → HasPieceCover (g∘h) (n+m)` — composing a **monotone** inner map makes pieces *add* (monotonicity pins each outer cut's preimage to a single ray `{x ∣ β ≤ h x} = Ici (crossing)`, so they can't multiply). Iterated: `hasPieceCover_iterate` — a monotone map with `k` pieces self-composed `d` times has `≤ d·k+1` pieces, **linear in depth**, vs the (non-monotone) tent's `2^d` (`DepthSeparation`). This closes the depth/composition axis; the arbitrary-circuit lift is discharged by `RegionPoly.lean`. |
| `Sundogcert/RegionPoly.lean` | **the circuit-level tight N-1 lift** (closing `isMono_regions_poly`). The **convexity bridge** `isMono_realize1_convexOn`: every cancellation-free (`IsMono`) circuit's 1-D realization is `ConvexOn ℝ univ` (`var`/`const`/`add`/nonneg-`scale`/`max` all preserve convexity) — the fact that makes `max` piece-*additive* rather than piece-*doubling*. Plus the cut-based gate lemmas needing no convexity: `hasPieceCover_add` (`+` is piece-additive `n+m`, cuts union) and `hasPieceCover_smul` (scaling preserves the cut set, `n`). The **convex-merge linchpin** `hasPieceCover_max_line` is proved: `ConvexOn h → HasPieceCover h k → HasPieceCover (fun x => max (ℓ x) (h x)) (k+1)` — adding a line to a convex function adds ≤ 1 piece, via the order-connected agreement region `{h ≤ ℓ}` and the bounded-case **absorption** (a convex dip carries an interior breakpoint that pays for the two endpoint cuts). This `+1` (not `+2`) is why monotone depth is region-polynomial. **The tight circuit-level bound is COMPLETE**: `lineBelow` (a convex function lies above any line it equals on a piece) + `convex_eq_sup_lines` (a convex `HasPieceCover`-`n` function is the max of its `≤ n` piece-lines, via cut-set secant enumeration) + `hasPieceCover_max` (convex-convex `max` is `n+m`, folding the linchpin) ⟹ **`isMono_hasPieceCover`**: `IsMono e → HasPieceCover (realize1 e) (leafCount e)` — region count **linear in circuit leaves**, vs the (cancellation) tent's `2^d`. The complete N-1 dichotomy, machine-checked |
| `Sundogcert/Certifies.lean` | **the find/check ledger as a general certificate theory** (N-3). The reusable optimality core `weakDuality_tight`: weak duality (every primal `≤` every dual) + a *tight pair* `p = d` ⟹ `IsGreatest P p ∧ IsLeast D d` (both optima at once) — the whole content of "a dual witness certifies a primal optimum". A `Certifies` class (extends `HasStraightLineCost`) marks a problem family in the ledger; soundness is discharged per instance, *finding* the witness is always the imported wall |
| `Sundogcert/MaxFlowMinCut.lean` | **max-flow / min-cut** — the LP-duality instance of `Certifies` and the 4th find/check-ledger entry. A skew-symmetric, capacity-bounded, conserved `Flow`; a cut `capCut`. `weak_duality`: `value F ≤ capCut cap S` (conservation collapses the `S`-sum to the source's net out-flow; the within-`S` double sum cancels by skew-symmetry; across-cut flow `≤` capacity edge by edge). `maxflow_mincut`: a tight flow/cut pair certifies the flow is **maximum** and the cut **minimum** at once. Cheap-check `cutcert_cost_le` (`O(|S|·|Sᶜ|)`); *finding* the max flow is the imported wall |
| `Sundogcert/MatchingCover.lean` | **König** — the second LP-duality `Certifies` instance (5th ledger entry). `matching_le_cover`: a vertex cover upper-bounds every matching (`|M| ≤ |C|`, via an injection matched-edge ↦ a cover endpoint — distinct matched edges share no vertex). `konig`: a tight matching/cover pair certifies the matching is **maximum** and the cover **minimum** at once. Cheap-check `covercert_cost_le` (`O(|E|)`); *finding* the maximum matching is the imported wall |
| `Sundogcert/TwoSat.lean` | **2-SAT** — the *decision-problem* `Certifies` instance (6th ledger entry; NP "verification is easy"). `check_correct`: the `O(|φ|)` clause evaluator decides satisfiability exactly. `cert_sound`: a satisfying assignment certifies `Satisfiable` (the witness is the proof). Cheap-check `satcert_cost_le`; *finding* the assignment (the implication-graph SCC algorithm) is the imported wall |
| `Sundogcert/PrattCert.lean` | **Pratt** — the *number-theoretic* `Certifies` instance (7th ledger entry; **primality is in NP**). A primitive-root `Witness` (`a^(p-1)=1`, `a^((p-1)/q)≠1` for every prime `q∣p-1`); `cert_sound` (Lucas) ⟹ `p.Prime`, `cert_complete` ⟹ every prime has one, `prime_iff_witness` the characterization — wrapping mathlib's `lucas_primality`/`reverse_lucas_primality`. Cheap-check `prattcert_cost_le` (`|factors|+1` modexps); *finding* the root + factoring `p−1` is the imported wall |
| `Sundogcert/CancellationSpine.lean` | **the cancellation spine** (N-2 synthesis anchor). `isMono_tame`: a cancellation-free (`IsMono`) circuit is *uniformly* tame — its realization is monotone **and** convex **and** region-polynomial, all from one hypothesis. Paired with `FoldCancellation.isMono_not_iterTent` (the cancellation-using tent is unreachable cancellation-free), this is the machine-checked half of "cancellation is the single coordinate." The full claim (additive/subtractive/division walls reducible too) stays a typed conjecture — the honest split is in `docs/ALGO_APPROX_N2_CANCELLATION_SPINE.md` |
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
[`scripts/cliff_transfer_keyring.py`](scripts/cliff_transfer_keyring.py) discovers
operator-held provider keys from `syek.*` files or environment variables and can
run no-generation list-models probes without printing secret values.
[`scripts/cliff_transfer_api_adapter.py`](scripts/cliff_transfer_api_adapter.py)
wires those keys into capped, operator-gated black-box API sweeps.

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
