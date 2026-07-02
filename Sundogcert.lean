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
-- The order-blind bag determines bracket DEPTH but not the STACK-TOP (`([` vs `[(` — same bag,
-- different top): the chat-v2 H2 crossover's label-structure half, the σ-bridge anchor. The
-- "model computes it" half stays empirical (the H2 probe receipt), exactly as ParityNoSufficientStat
-- fences Sarnak/Chowla.
import Sundogcert.SurfaceBag
-- OR-6 the graded window form: σ_surface(stack-top) = ∞ — for EVERY window order w there are
-- valid prefixes with identical ≤w-gram count vectors and different stack-tops (the context-swap
-- witness family P x P y P / P y P x P with the position involution); closes SurfaceBag's open hook.
import Sundogcert.SurfaceBagGraded
