import Sundogcert.Basic
import Sundogcert.Certificate
import Sundogcert.Instance
import Sundogcert.Scaling
import Sundogcert.Looseness
import Sundogcert.CertWall
import Sundogcert.Degradation
import Sundogcert.CheckCost
import Sundogcert.StraightLineCost
import Sundogcert.ShortestPathCert
-- The find/check ledger as a general certificate theory + its instances (N-3):
-- max-flow/min-cut and König (LP-duality optimization), 2-SAT (decision), Pratt (primality).
import Sundogcert.Certifies
import Sundogcert.MaxFlowMinCut
import Sundogcert.MatchingCover
import Sundogcert.TwoSat
import Sundogcert.PrattCert
-- The ledger's first PROVED (not imported) find/check gap: unstructured search in the query model.
import Sundogcert.QueryGap
-- The ledger's program-synthesis / abstraction instance (FC-1, find/check sufficiency lane).
import Sundogcert.AbstractionCert
-- The unconditional find/check separation for that abstraction family (FC-2, query model).
import Sundogcert.AbstractionQueryGap
import Sundogcert.ShadowDecay
import Sundogcert.ShadowDecayGeneral
import Sundogcert.ShadowDecayCauchy
import Sundogcert.HaloGeometry
import Sundogcert.FaradayAB
import Sundogcert.SortingCert
import Sundogcert.RSCertificate
import Sundogcert.DecodingNPHard
import Sundogcert.AxiomAudit
import Sundogcert.ShadowDecayLattice
import Sundogcert.AuditCost
-- The uniformization blind point attached to the AuditCost pillar: exactly-uniform phase
-- pushforward ⇒ identical verdict statistics for EVERY probe (an identity, so impossibility for
-- all probes at once); non-vacuity = off-uniform the identity probe distinguishes (HS6 ticket).
import Sundogcert.UniformBlind
-- Exact tropical-circuit → ReLU-network compilation (circuit-complexity / approx. theory).
import Sundogcert.CircuitNet
-- The cancellation-free (monotone) fragment: locating the monotone-vs-general wall.
import Sundogcert.CancellationFree
-- Depth separation: exponential linear regions from linear tropical depth.
import Sundogcert.DepthSeparation
-- Linear regions as an exact (realization-independent) tropical invariant.
import Sundogcert.RegionCount
-- Folding needs cancellation: the depth-separation witness is not cancellation-free (N-1).
import Sundogcert.FoldCancellation
-- Bounded piece certificate: monotone composition adds pieces (N-1 positive half, quantitative).
import Sundogcert.PieceCover
-- Cancellation-free circuits are convex; cut-based gate lemmas (N-1 circuit-level lift).
import Sundogcert.RegionPoly
-- The cancellation spine: cancellation-free ⇒ uniformly tame (N-2 synthesis anchor).
import Sundogcert.CancellationSpine
-- Exact representability (S3-1): every convex continuous-PL function IS a finite ReLU net.
import Sundogcert.ExactRepr
-- Graded cancellation (S3-2): region count ≤ 4^(cancellation budget) · leafCount.
import Sundogcert.GradedCancellation
-- Analytic gate at ε>0 (S3-4): x² is ReLU-approximable on [0,1] with a machine-checked L∞ bound.
import Sundogcert.AnalyticGate
-- The polylog rate (S3-4 hard step): x² via the Telgarsky sawtooth at logarithmic depth.
import Sundogcert.SawtoothApprox
-- Toward the general analytic gate: an ε-multiplication gate at log depth (polarization on x²).
import Sundogcert.MultiplyGate
-- Iterating the multiply gate into monomials x^d at the polynomial rate O(d·log 1/ε) (Cor 5.1).
import Sundogcert.MonomialEval
-- General polynomials Σ aᵢ xⁱ in the monomial basis at the polynomial rate (Cor 5.1, full).
import Sundogcert.PolyEval
-- The general-continuous capstone: every continuous f on [0,1] is ReLU-approximable (Weierstrass).
import Sundogcert.UniversalApprox
-- Slate-4 U-3: the analytic gate's certified op-count in the StraightLineCost ledger.
import Sundogcert.ApproxCost
-- Slate-4 U-3 follow-on (value core): the sawtooth's closed form = a flat sum of m chain-shared
-- iterated tents (why an O(m)-gate shared DAG suffices, vs. the exponential tree).
import Sundogcert.SawtoothShared
-- Slate-4 U-3 follow-on (the literal gate count): the explicit O(m)-gate shared sawtooth ReLU DAG
-- (compileWith reads a wire; the iterated-tent chain) — x² to ε at O(log 1/ε) GATES.
import Sundogcert.SawtoothDag
-- Slate-4 U-1a/b (multivariate cube lift): products of coordinates, then multivariate polynomials
-- Σ c·∏ xᵢ, as ReLU Net n on [0,1]ⁿ at the polynomial rate (constructive core).
import Sundogcert.MvMonomial
import Sundogcert.MvPolyEval
-- Slate-4 U-1c/d (cube capstone): every continuous f on [0,1]ⁿ is ReLU-approximable, via the
-- MvPolynomial→net bridge + multivariate Stone-Weierstrass.
import Sundogcert.MvUniversalApprox
-- Slate-4 U-2: extend the find/check ledger to approximation certificates (the a-posteriori
-- sampling bound — a finite cheap CHECK of a continuum bound, modulus the named carried input).
import Sundogcert.ApproxCert
-- The 3SAT ≤ 3DM ≤ X3C ≤ Decodes Karp reduction (machine-checked correctness).
import Sundogcert.MatchingNPHard
import Sundogcert.SATNPHard
import Sundogcert.VarWheel
import Sundogcert.ClauseGadget
import Sundogcert.SATReduction
import Sundogcert.ThreeDMReindex
import Sundogcert.SATReductionIncidence
import Sundogcert.SATReductionReverse
import Sundogcert.SATReductionForward
import Sundogcert.SATReductionMain
import Sundogcert.Tauroctony
import Sundogcert.Percival
-- Percival S4 general: best quantilizer is the untilted base for any n-point nonincreasing
-- court reward (suffix-average ≤ full average) + the general clean support-above separation.
import Sundogcert.PercivalGeneral
-- OR-5 classification core: the authority cap bounds the OUTGOING swing under any upstream
-- intervention (≤ 2κ, no internals assumption) and constrains INCOMING sensitivity not at all
-- (∀M ∃ raw map > M passing the cap) — the S1 cleanliness-law classification, two-sided.
import Sundogcert.PercivalCapClass
-- OR-1 keyed-composition MARGIN law over the S3 skeleton: the cap bound is exactly additive
-- (sound + achieved, profile-independent marginal) while the threshold court's value is additive
-- in NO per-agent recoding (three-profile pigeonhole) — composition is decided by the keying.
import Sundogcert.PercivalKeyedMargin
-- OR-4 the write-side ∞ cell: in S2's exact 2×2×2 CI model, do(U)-invariance factors through V
-- and pays the reliability edge ρ−β vs the U-follower, while dependence is decided by the 4-entry
-- interventional probe table — MEASURABLE ≠ ENFORCEABLE as one statement (Blackwell repair sheathed).
import Sundogcert.PercivalTargetCollapse
-- ME-3 audit-and-pay prices at the edge: a transfer keyed on the exact probe-table audit implements
-- the target safe point IFF t ≥ ρ−β (Bayes ceiling comp ≤ ρ + collapse + tight V-follower) —
-- incentive enforcement pays the structural write-price; reads do not discount enforcement.
import Sundogcert.PercivalAuditPay
-- ME-2 the node/edge typing law: a node-write (input+output surgery, policy-blind) enforces
-- do(U)-invariance for ALL policies IFF at every v it masks the input or voids the action —
-- every enforcer is a channel retreat, and pays the collapse; owning every node ≠ owning the edge.
import Sundogcert.PercivalNodeEdge
-- ME-5 the richer-joint witness: on the XOR synergy joint both single channels are worthless
-- (edge formula = 0) yet the safe-point write-price is 1/2 — the reliability-edge FORMULA is a
-- binary-symmetric-CI artifact/floor; the price survives as the value gap (local deficiency).
import Sundogcert.PercivalSynergy
import Sundogcert.AgenticTrace
import Sundogcert.DiscreteHolonomy
import Sundogcert.ContextDecay
import Sundogcert.CuspGerm
import Sundogcert.RetrievalCusp
import Sundogcert.HierarchyHolonomy
import Sundogcert.StructuralSlot
-- Parity barrier (toy half): a finite-order partial parity is not a sufficient statistic
-- for the full-history total parity. Sarnak/Chowla named as the imported wall (P-1).
import Sundogcert.ParityNoSufficientStat
-- The Order-Relative Resolution Law: the slate's one statement (a schema, not a scalar) that the
-- axes (search / pressure / repertoire / determination / find-check) instantiate (B).
import Sundogcert.OrderRelative
-- Two further grounded instance families: the determine/resist law's own home (spectral/moment,
-- order binary) and the algebraic-degree axis with the mode-vector on the real BoxSEL optimum.
import Sundogcert.OrderRelativeMoment
import Sundogcert.OrderRelativeAlgDegree
-- The topological/cohomological axis (torsion vs free) + the cohomological mode-vector.
import Sundogcert.OrderRelativeCohomology
-- The composition law: scalar order of a product class = lcm = the divisibility-lattice join.
import Sundogcert.OrderRelativeCompose
-- The composition boundary: join-homo iff cancellation-free (2nd negative + the general coproduct law).
import Sundogcert.OrderRelativeComposeLaw
-- The radical axis = multiplicative twin of cohomological (3rd positive: group-order axes are join-homo).
import Sundogcert.OrderRelativeRadicalCompose
-- The converse FAILS (idempotency obstruction): moment is join-homo but not a group order; + unified law.
import Sundogcert.OrderRelativeConverse
-- The search-reach negative machine-checked (the boundary's other negative; it inflates, not drops).
import Sundogcert.OrderRelativeSearchNeg
-- An approximation axis: exactness is order-relative (PL determine / x² resist); ε-approx collapses.
import Sundogcert.OrderRelativeApprox
-- The approximation axis GRADED by piece count (id 1 / ReLU 2 / x² ⊤) + a 2nd resist (eˣ).
import Sundogcert.OrderRelativeApproxGraded
-- A third determine rung: step2 = ReLU x + ReLU (x-1) at order 3 (the ladder climbs 1 < 2 < 3).
import Sundogcert.OrderRelativeApproxLadder
-- The general k-breakpoint family Σ ReLU(x-i) at order exactly k+1 (the ladder is unbounded).
import Sundogcert.OrderRelativeApproxLadderK
-- The moment axis is join-homomorphic under the independent sum (= convolution): the lone
-- analysis residual machine-checked (sum-integrable ⟹ both, via the product law + Fubini).
import Sundogcert.OrderRelativeMomentConv
-- The grading law abstracted: ord(product) = lcm of orders for ANY two monoids (+ to_additive
-- twin); the group-order axes (cohomological, radical) are instances of one lemma.
import Sundogcert.OrderRelativeGrading
-- The radical axis as a FULL instance: builds the ℝˣ/ℚˣ quotient, proves RadicalReaches = order of
-- [x] in it (the promoted docstring), so its composition is a literal instance of the grading law.
import Sundogcert.OrderRelativeRadicalQuotient
-- The n-ary grading law (ord of a tuple = Finset.lcm of coordinate orders) + the structure-theorem
-- mode-vector: scalar order of (1,…,1) in ⊕ ZMod dᵢ = lcm of the invariant factors.
import Sundogcert.OrderRelativeStructure
-- OR-2: the keyed-composition boundary instance — cap margins on the cancellation-free pole
-- (ℚ≥0 zerosumfree; the banked coproduct/grading laws verbatim at margin tuples) vs the court's
-- idempotent threshold readout (Bool ∨; idempotent_eq_one verbatim; the readout = the non-hom locus).
import Sundogcert.OrderRelativeKeyed
-- U-4: the definability rate — an explicit uniform piece-count modulus for ReLU nets, exposing the
-- witness inside net_hasPieceCover's `∃ k`; the checkable PL finiteness-modulus (o-minimal tameness
-- shadow), needing no o-minimal substrate (mathlib v4.30.0 has none).
import Sundogcert.DefinableRate
-- O-min ladder rung 1: o-minimality in dimension one via the finite-frontier characterization
-- (`Tame`); two structures machine-checked tame — the ReLU/semilinear boolean algebra (NetDef)
-- and quantifier-free semialgebraic sets (PolyDef, the one-variable shadow of Tarski). The next
-- walls (projection/Tarski–Seidenberg, monotonicity, cell decomposition) are named, not claimed.
import Sundogcert.OMinimalOne
-- The order-blind bag determines bracket DEPTH but not the STACK-TOP (`([` vs `[(` — same bag,
-- different top): the chat-v2 H2 crossover's label-structure half, the σ-bridge anchor. The
-- "model computes it" half stays empirical (the H2 probe receipt), exactly as ParityNoSufficientStat
-- fences Sarnak/Chowla.
import Sundogcert.SurfaceBag
-- OR-6 the graded window form: σ_surface(stack-top) = ∞ — for EVERY window order w there are
-- valid prefixes with identical ≤w-gram count vectors and different stack-tops (the context-swap
-- witness family P x P y P / P y P x P with the position involution); closes SurfaceBag's open hook.
import Sundogcert.SurfaceBagGraded
-- AT-6 anchor: amplitude washes, a rescaling readout does not — attenuation by any nonzero factor
-- preserves exact decodability (only the zero-limit shadow kills it), packaged with the in-tree
-- AC-resist/lattice-survive typing. The trajectory-average bridge stays a named import with a
-- measured boundary (the AT-6 receipt: wash-out needs a noise floor).
import Sundogcert.AveragingDecodability
-- O-min ladder R2-M/R2-Q: the Monotonicity Theorem PL instance (cut-free stretches are monotone
-- or antitone, within the U-4 piece budget) + the frontier modulus (level-set frontier ncard
-- ≤ 2|S|+1 via initial-segments-are-a-chain; net form ≤ 2·netPieceBound−1 = the U-4 bridge).
import Sundogcert.OMinimalRate
-- O-min ladder R2-N: the normal form — Tame ↔ finite union of points and open intervals
-- (max'-peeling induction; frontier-free preconnected windows cannot separate a set).
import Sundogcert.OMinimalNormalForm
-- O-min ladder R3-semilinear (1/2): the semilinear presentation class, dims 1–2 — {>,=}-cells,
-- constructive boolean closure (union/inter/de-Morgan complement), 1-D fragment lands in Tame.
import Sundogcert.Semilinear
-- O-min ladder R3-semilinear (2/2): Fourier–Motzkin — the projection axiom, dims 2 → 1: eliminate
-- y per cell (equality pin ⇒ substitute ×b²; else lower/upper split + division-free pairwise
-- comparisons + the explicit between-the-bounds witness); projections of semilinear sets are tame.
import Sundogcert.FourierMotzkin
-- O-min ladder R4-A: the abstract van den Dries structure (`OMinStructure`: booleans,
-- substitution-in-one-axiom, ∃-snoc projection, order/singleton atoms, `Tame` as the S₁ axiom) +
-- the definable calculus (rays/intervals; DefinableFun closed under composition; level sets tame)
-- + the capstone: dimension-one definables are EXACTLY the tame sets (via R2's normal form +
-- the shape lemma for open OrdConnected sets). Non-vacuity = R4-B (n-dim semilinear instance).
import Sundogcert.OMinimalStructure
-- O-min ladder R4-B1: the n-dimensional semilinear presentation class — coefficient-row atoms
-- ((∑ aᵢxᵢ)+c ≷ 0), cells/unions, and the constructive boolean closure ported from dims 2 with
-- the atom value abstracted (the one new fact: negating row+constant negates the value).
import Sundogcert.SemilinearN
-- O-min ladder R4-B3: n-dimensional Fourier–Motzkin — eliminate the last variable (front/last
-- split via Fin.sum_univ_castSucc; one shared linearity lemma serves pair atoms + both
-- substitution kinds; value lemmas restated with the front opaque; witness machinery imported
-- verbatim from the dims-2 module). Headline projSLN_toSet = the definable_proj axiom shape.
import Sundogcert.FourierMotzkinN
-- O-min ladder R4-B4: the assembled instance — semilinearStructure : OMinStructure, the first
-- machine-checked nontrivial o-minimal structure (classically: QE for the ordered ℝ-vector
-- space). Discharges R4-A's non-vacuity fence and R3's n-dim fence; R4-A's capstone and
-- tameness payoffs instantiate (semilinear_s1_eq_tame, semilinear_defFun_tame).
import Sundogcert.SemilinearStructure
-- O-min ladder R4-C0: the formula layer — definability by reflection (Fml: atoms = definable
-- sets pulled back along coordinate maps; ¬/∧/∃; ∨/→/∀ derived; ONE induction Fml.definable).
-- Kills the Monotonicity Theorem's plumbing cost-center; receipt = tame_right_inc (a D-set in
-- six lines of formula that costs ~100 lines raw).
import Sundogcert.OMinimalFormula
-- O-min ladder R4-C1a: toolkit riders — infinite tame sets contain intervals (normal-form
-- rider); the pointwise eventual-sign trichotomies (right + left: three tame comparison sets,
-- a frontier-avoiding window, preconnected_split, midpoint picks the sign) + sublevel gap-fill.
import Sundogcert.OMinimalTrichotomy
-- O-min ladder R4-C1b: the sign partition — six one-sided sign-class sets tame via two formula
-- templates; two-sided classes = intersections (locInc = rightAbove ∩ leftBelow, no new
-- formulas); headline sign_partition = a finite cut-set with ONE behavior class per gap.
import Sundogcert.OMinimalSignPartition
-- O-min ladder R4-C1c: the gluing engine — ONE sup-chaining lemma over an abstract transitive
-- relation (rel_propagate; no continuity, two-sided windows essential) instantiated three ways:
-- locInc everywhere ⇒ StrictMonoOn, locDec ⇒ StrictAntiOn, locConst ⇒ constant on the gap.
import Sundogcert.OMinimalGluing
-- O-min ladder R4-C1d: THE MONOTONICITY THEOREM — badSet finite (four eq-mixed window kills +
-- the two extremum combos by countability: strict neighbor-extrema inject into ℚ², Ioo is
-- uncountable [ℝ-specific; the general-RCF constant-or-injective route is the named
-- refinement]) + assembly: finite cut-set, constant/StrictMonoOn/StrictAntiOn per gap.
import Sundogcert.OMinimalMonotonicity
-- O-min ladder R4-C2a: the order-continuity bridge (no arithmetic atoms ⇒ ε-δ inexpressible;
-- ContinuousAt in pure order terms via nhds_basis_Ioo) + the usc/lsc split (two five-coordinate
-- formulas) ⇒ tame_discSet: the discontinuity set of a definable function is tame.
import Sundogcert.OMinimalContinuity
-- O-min ladder R4-D0: parametric slices are tame (the C0 slicing IOU); closure in order terms;
-- the fiber-frontier set Y = {(x,y) | y ∈ frontier(A_x)} is definable, and its fibers are
-- AUTOMATICALLY finite (fiber of Y = frontier of fiber of A; Tame = frontier-finite) — the
-- uniform-finiteness engine's input.
import Sundogcert.OMinimalSlice
-- O-min ladder R4-D1: the counting formulas — countSet A k = {x | fiber ≥ k points} is tame
-- via an Fml-valued recursion over the meta-natural k, powered by the new Fml.reindex (whole-
-- formula pullback along coordinate maps, ∃-threading via extendMap). Chain kit for D2:
-- decreasing chain, finset extraction/construction, and infinite_fiber_of_mem_all.
import Sundogcert.OMinimalCounting
-- O-min ladder R4-D2: the dichotomy kill (finite fibers + unbounded sizes => every counting
-- set contains an interval, by cardinality stabilization of the decreasing chain) and the
-- definable k-th point functions (BelowCount mirror, exact-rank IsNth unique+exists,
-- totalized nthFn with definable graph -- the Monotonicity Theorem's D3 input).
import Sundogcert.OMinimalPointFns
-- O-min ladder R4-D3: the k-curve extraction -- for every k, one interval carrying k
-- genuine (exact-rank, graphs-in-A), continuous, strictly ordered rank functions:
-- k pairwise disjoint definable curves (dichotomy interval + continuous Monotonicity
-- Theorem per rank + one finite-avoidance window over the union of cut-sets).
import Sundogcert.OMinimalCurves
-- O-min ladder R4-D4a: the normality layer (classical Finiteness-Lemma route; the "pile
-- wall" dissolved). Box-normality predicates, their definability (selection-continuity
-- formula at ambient 12 over a generated snoc battery), normal heights open per column,
-- +-/-infinity ray-normality tame -- the bad-set/beta machinery inputs for D4b-D4d.
import Sundogcert.OMinimalNormal
-- O-min ladder R4-D4b: the beta-machinery. Generic definable selector (selFn: any definable
-- functional relation totalizes to a DefinableFun, proved once) instantiated five times:
-- betaFn (least non-normal height, exists via IsClosed.csInf_mem + ray-normality bounds),
-- fiber max/min, and the beta fiber neighbors (betaFn's own graph fed back as an atom).
-- Plus the three tame bad sets. D4c's tube-kill inputs complete.
import Sundogcert.OMinimalBeta
-- O-min ladder R4-D4c: THE TUBE KILL -- the bad sets are FINITE. Ray kills (fiber-max/min
-- continuity caps a window with a constant => ray box) + the tube proper (interval of bad
-- parameters -> beta exists -> three tame-flag splits -> triple continuity shrink -> the
-- (c,d) tube between the fiber neighbors is A-free except the beta-graph -> (a*, beta a*)
-- is normal, contradicting beta = least non-normal height). abnormal_finite = D4d's input.
import Sundogcert.OMinimalBadFinite
-- O-min ladder R4-D4d: UNIFORM FINITENESS -- the Finiteness Lemma complete (vdD Ch.3 (1.7)
-- over the abstract OMinStructure). Count locally constant at fully-normal parameters
-- (min-peeling strips for >=, ray boxes + Heine-Borel leftover cover + thin-box injection
-- for <=); counting-set frontiers live in the finite abnormal set; the chain kill
-- (gap-pigeonhole + preconnected_split propagation) forbids unbounded fiber sizes.
import Sundogcert.OMinimalUniformFiniteness
-- O-min ladder R4-D5a: CDT2 opens -- the uniform frontier bound. uniform_finiteness applied
-- to D0's fiberFrontier (definable, automatically finite fibers): |frontier(A_x)| <= N for
-- EVERY definable A, no hypothesis. Rank enumeration of finite fibers (every point is the
-- rank of its below-count) + the tame exact-count base classes covering the line.
import Sundogcert.OMinimalFrontierBound
-- O-min ladder R4-D5b: the master refinement -- one bound N and ONE finite cut set C such
-- that on every C-avoiding interval: a single exact-count class, all N rank functions of
-- fiberFrontier continuous, and every structural test (graph/band/ray/full, both polarities
-- via the complement trick) constant. Tests tame via rank-graph atoms; constancy =
-- preconnected_split on frontier-free intervals. D5c's complete input.
import Sundogcert.OMinimalRefinement
-- O-min ladder R4-D5c: BAND TRIVIALITY -- the CDT2 core. Per-fiber dichotomies (open bands
-- between consecutive fiberFrontier ranks are frontier-free by rank enumeration + ordering,
-- so preconnected_split forces all-in/all-out; likewise both rays and the k=0 full fiber),
-- regions_cover (rays+graphs+bands exhaust the line, Nat.findGreatest), and the capstone
-- band_triviality: on every cut-avoiding interval, one class, continuous ordered ranks, and
-- every region UNIFORMLY in or out of A -- cell decomposition for R^2 in concrete form.
import Sundogcert.OMinimalBandTriviality
-- O-min ladder R4-D5d-1: the Cell2 packaging layer. Cell1/Cell2 datatypes + toSet +
-- WellFormed + IsCellDecomp (covers/pairwise/adapted/wellFormed); the sort-free baseCells
-- decomposition of the line from a finite cut set (points + adjacent gaps from a product
-- filter + outer rays) proved covering and pairwise disjoint; and the two-point ray/univ
-- uniformity upgrades that D5d-2's assembly needs for the unbounded base cells.
import Sundogcert.OMinimalCells
-- O-min ladder R4-D5d-2: CELL DECOMPOSITION FOR R^2 -- the arc's terminal theorem. Every
-- definable planar set admits a finite, covering, pairwise-disjoint, adapted, well-formed
-- cell decomposition (cell_decomposition; union form cell_decomposition_mem). Generic
-- per-base constructor (bandLow . graphs . bands . bandHigh from a uniform class +
-- selections) x per-base instantiations (fiber dichotomies at points, band_triviality on
-- gaps, two-point upgrades on rays/line) x flatMap over the baseCells partition.
import Sundogcert.OMinimalCellDecomp
