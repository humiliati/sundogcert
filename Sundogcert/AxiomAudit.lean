/-
# AxiomAudit — the build-enforced axiom-clean gate

This module makes the repository's "referee-free" promise *self-checking*.

Every headline theorem in this development is axiom-clean: `#print axioms <thm>`
reports exactly the three foundational axioms of Lean/mathlib —
`[propext, Classical.choice, Quot.sound]` — and nothing else. In particular there
is no `sorryAx` (which a `sorry` would introduce) and no axiom from
`native_decide` (`Lean.ofReduceBool`/`Lean.trustCompiler`).

Until now that fact was verified by a human reading the `#print axioms` output. Here
it is verified by the *build*: each headline result below is wrapped in
`#guard_msgs in #print axioms`, which pins the captured message to the exact
foundational triple. If a future edit introduces a `sorry`, a `native_decide`, or
any other extra axiom into one of these results, the captured message changes, the
`#guard_msgs` exact-match fails, and `lake build` FAILS. The promise can no longer
silently regress.

Each `#print axioms` command is placed on its own line at column 0 (not inline after
`#guard_msgs in`) so the mathlib whitespace style linter, which is active under a full
`lake build`, stays quiet and does not inject an extra captured message.

To extend the gate: add the headline name of any new load-bearing theorem with its
own `#guard_msgs in` / `#print axioms` block.
-/
import Sundogcert.Certificate
import Sundogcert.Scaling
import Sundogcert.Looseness
import Sundogcert.Degradation
import Sundogcert.CheckCost
import Sundogcert.ShadowDecay
import Sundogcert.ShadowDecayGeneral
import Sundogcert.ShadowDecayCauchy
import Sundogcert.HaloGeometry
import Sundogcert.FaradayAB
import Sundogcert.CertWall
import Sundogcert.DecodingNPHard
import Sundogcert.ShadowDecayLattice
import Sundogcert.SATNPHard
import Sundogcert.VarWheel
import Sundogcert.ClauseGadget
import Sundogcert.SATReduction
import Sundogcert.ThreeDMReindex
import Sundogcert.SATReductionReverse
import Sundogcert.SATReductionForward
import Sundogcert.SATReductionMain
import Sundogcert.AuditCost
import Sundogcert.UniformBlind
import Sundogcert.AgenticTrace
import Sundogcert.DiscreteHolonomy
import Sundogcert.ContextDecay
import Sundogcert.CuspGerm
import Sundogcert.RetrievalCusp
import Sundogcert.HierarchyHolonomy
import Sundogcert.StructuralSlot
import Sundogcert.CircuitNet
import Sundogcert.CancellationFree
import Sundogcert.DepthSeparation
import Sundogcert.RegionCount
import Sundogcert.FoldCancellation
import Sundogcert.PieceCover
import Sundogcert.RegionPoly
import Sundogcert.CancellationSpine
import Sundogcert.ExactRepr
import Sundogcert.GradedCancellation
import Sundogcert.AnalyticGate
import Sundogcert.SawtoothApprox
import Sundogcert.MultiplyGate
import Sundogcert.MonomialEval
import Sundogcert.PolyEval
import Sundogcert.UniversalApprox
import Sundogcert.ApproxCost
import Sundogcert.SawtoothShared
import Sundogcert.SawtoothDag
import Sundogcert.MvMonomial
import Sundogcert.MvPolyEval
import Sundogcert.MvUniversalApprox
import Sundogcert.ApproxCert
import Sundogcert.StraightLineCost
import Sundogcert.ShortestPathCert
import Sundogcert.Certifies
import Sundogcert.MaxFlowMinCut
import Sundogcert.MatchingCover
import Sundogcert.TwoSat
import Sundogcert.PrattCert
import Sundogcert.QueryGap
import Sundogcert.QueryGapCapacity
import Sundogcert.AbstractionCert
import Sundogcert.AbstractionQueryGap
import Sundogcert.ParityNoSufficientStat
import Sundogcert.OrderRelative
import Sundogcert.OrderRelativeMoment
import Sundogcert.OrderRelativeAlgDegree
import Sundogcert.OrderRelativeCohomology
import Sundogcert.OrderRelativeCompose
import Sundogcert.OrderRelativeComposeLaw
import Sundogcert.OrderRelativeRadicalCompose
import Sundogcert.OrderRelativeConverse
import Sundogcert.OrderRelativeSearchNeg
import Sundogcert.OrderRelativeApprox
import Sundogcert.OrderRelativeApproxGraded
import Sundogcert.OrderRelativeApproxLadder
import Sundogcert.OrderRelativeApproxLadderK
import Sundogcert.OrderRelativeMomentConv
import Sundogcert.OrderRelativeGrading
import Sundogcert.OrderRelativeRadicalQuotient
import Sundogcert.OrderRelativeStructure
import Sundogcert.DefinableRate
import Sundogcert.Percival
import Sundogcert.PercivalGeneral
import Sundogcert.PercivalCapClass
import Sundogcert.PercivalKeyedMargin
import Sundogcert.PercivalTargetCollapse
import Sundogcert.PercivalAuditPay
import Sundogcert.PercivalNodeEdge
import Sundogcert.PercivalSynergy
import Sundogcert.PercivalNoisyMargin
import Sundogcert.PercivalFixedPoint
import Sundogcert.PercivalBasin
import Sundogcert.OrderRelativeKeyed
import Sundogcert.SurfaceBag
import Sundogcert.SurfaceBagGraded
import Sundogcert.OMinimalOne
import Sundogcert.AveragingDecodability
import Sundogcert.OMinimalRate
import Sundogcert.OMinimalNormalForm
import Sundogcert.Semilinear
import Sundogcert.FourierMotzkin
import Sundogcert.OMinimalStructure
import Sundogcert.SemilinearN
import Sundogcert.FourierMotzkinN
import Sundogcert.SemilinearStructure
import Sundogcert.OMinimalFormula
import Sundogcert.OMinimalTrichotomy
import Sundogcert.OMinimalSignPartition
import Sundogcert.OMinimalGluing
import Sundogcert.OMinimalMonotonicity
import Sundogcert.OMinimalContinuity
import Sundogcert.OMinimalSlice
import Sundogcert.OMinimalCounting
import Sundogcert.OMinimalPointFns
import Sundogcert.OMinimalCurves
import Sundogcert.OMinimalNormal
import Sundogcert.OMinimalBeta
import Sundogcert.OMinimalBadFinite
import Sundogcert.OMinimalUniformFiniteness
import Sundogcert.OMinimalFrontierBound
import Sundogcert.OMinimalRefinement
import Sundogcert.OMinimalBandTriviality
import Sundogcert.OMinimalCells
import Sundogcert.OMinimalCellDecomp
import Sundogcert.PolySignPartition
import Sundogcert.PolyBranchTrees
import Sundogcert.PseudoRemainder
import Sundogcert.PolyDerivZones
import Sundogcert.SignDiagrams
import Sundogcert.DiagramNormalize

/-! ## Certificate — lossiness, accept/reject soundness, sound column-weight bound -/

/-- info: 'Sundog.Certificate.syndrome_independent_of_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.syndrome_independent_of_secret

/-- info: 'Sundog.Certificate.accept_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.accept_sound

/-- info: 'Sundog.Certificate.reject_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.reject_sound

/-- info: 'Sundog.Certificate.colWeightLb_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.colWeightLb_sound

/-- info: 'Sundog.Certificate.reject_sound_colweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.reject_sound_colweight

/-! ## Scaling — the projection-family scaling law -/

/-- info: 'Sundog.Certificate.Scaling.scaling_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.Scaling.scaling_law

/-! ## Looseness — basis-dependence collapse -/

/-- info: 'Sundog.Certificate.Looseness.looseness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.Looseness.looseness

/-! ## Degradation — the general column-weight ceiling -/

/-- info: 'Sundog.Certificate.Degradation.colWeightLb_le_card_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.Degradation.colWeightLb_le_card_div

/-! ## CheckCost — the linear check-cost theorem -/

/-- info: 'Sundog.Certificate.verifyCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.verifyCost_le

/-! ## StraightLineCost — shared op-count ledger for construction and checking -/

/-- info: 'Sundog.StraightLineCost.compileToDag_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StraightLineCost.compileToDag_cost_le

/-- info: 'Sundog.StraightLineCost.verifier_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StraightLineCost.verifier_cost_le

/-- info: 'Sundog.StraightLineCost.shared_cost_instances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StraightLineCost.shared_cost_instances

/-! ## CancellationFree -- the monotone fragment; the monotone-vs-general wall -/

/-- info: 'Sundog.CancellationFree.monotone_of_isMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CancellationFree.monotone_of_isMono

/-- info: 'Sundog.CancellationFree.abs_not_isMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CancellationFree.abs_not_isMono

/-- info: 'Sundog.CancellationFree.monotone_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CancellationFree.monotone_transfer

/-- info: 'Sundog.CancellationFree.decompile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CancellationFree.decompile_eval

/-! ## DepthSeparation -- exponential linear regions from linear tropical depth -/

/-- info: 'Sundog.DepthSeparation.iterTent_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DepthSeparation.iterTent_eval

/-- info: 'Sundog.DepthSeparation.iterTent_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DepthSeparation.iterTent_depth_le

/-- info: 'Sundog.DepthSeparation.tent_iterate_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DepthSeparation.tent_iterate_dyadic

/-! ## RegionCount -- linear regions as an exact tropical invariant -/

/-- info: 'Sundog.RegionCount.realize1_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionCount.realize1_compile

/-- info: 'Sundog.RegionCount.max_two_not_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionCount.max_two_not_affine

/-- info: 'Sundog.RegionCount.compiled_maxGate_not_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionCount.compiled_maxGate_not_affine

/-! ## FoldCancellation -- folding needs cancellation (N-1 sharp form) -/

/-- info: 'Sundog.FoldCancellation.isMono_no_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FoldCancellation.isMono_no_fold

/-- info: 'Sundog.FoldCancellation.isMono_not_iterTentFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FoldCancellation.isMono_not_iterTentFun

/-- info: 'Sundog.FoldCancellation.isMono_not_iterTent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FoldCancellation.isMono_not_iterTent

-- positive half (qualitative core): monotone circuits never fold at any level
/-- info: 'Sundog.FoldCancellation.isMono_realize1_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FoldCancellation.isMono_realize1_monotone

/-- info: 'Sundog.FoldCancellation.isMono_superlevel_isUpperSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FoldCancellation.isMono_superlevel_isUpperSet

/-- info: 'Sundog.FoldCancellation.tent_superlevel_not_isUpperSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FoldCancellation.tent_superlevel_not_isUpperSet

/-! ## PieceCover -- monotone composition adds pieces (N-1 quantitative) -/

/-- info: 'Sundog.PieceCover.hasPieceCover_comp_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PieceCover.hasPieceCover_comp_mono

/-- info: 'Sundog.PieceCover.hasPieceCover_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PieceCover.hasPieceCover_iterate

/-! ## RegionPoly -- cancellation-free circuits are convex; cut-based gate lemmas (N-1 lift) -/

/-- info: 'Sundog.RegionPoly.isMono_realize1_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.isMono_realize1_convexOn

/-- info: 'Sundog.RegionPoly.hasPieceCover_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.hasPieceCover_add

/-- info: 'Sundog.RegionPoly.hasPieceCover_max_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.hasPieceCover_max_line

/-- info: 'Sundog.RegionPoly.lineBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.lineBelow

/-- info: 'Sundog.RegionPoly.convex_eq_sup_lines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.convex_eq_sup_lines

/-- info: 'Sundog.RegionPoly.hasPieceCover_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.hasPieceCover_max

/-- info: 'Sundog.RegionPoly.isMono_hasPieceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RegionPoly.isMono_hasPieceCover

/-! ## CancellationSpine -- cancellation-free ⇒ uniformly tame (N-2 synthesis anchor) -/

/-- info: 'Sundog.CancellationSpine.isMono_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CancellationSpine.isMono_tame

/-! ## ExactRepr -- continuous-PL ⟹ exact ReLU net (S3-1, representability converse) -/

/-- info: 'Sundog.ExactRepr.convexCPL_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ExactRepr.convexCPL_realizable

/-- info: 'Sundog.ExactRepr.cpl_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ExactRepr.cpl_realizable

/-- info: 'Sundog.ExactRepr.net_hasPieceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ExactRepr.net_hasPieceCover

/-- info: 'Sundog.ExactRepr.cpl_iff_reluNet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ExactRepr.cpl_iff_reluNet

/-! ## GradedCancellation -- region count graded by a cancellation budget (S3-2) -/

/-- info: 'Sundog.GradedCancellation.cancelMax_eq_zero_of_isMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.GradedCancellation.cancelMax_eq_zero_of_isMono

/-- info: 'Sundog.GradedCancellation.hasPieceCover_graded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.GradedCancellation.hasPieceCover_graded

/-! ## AnalyticGate -- x² is ReLU-approximable to any ε on [0,1], with a proven bound (S3-4) -/

/-- info: 'Sundog.AnalyticGate.sqNet_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AnalyticGate.sqNet_approx

/-- info: 'Sundog.AnalyticGate.sq_eps_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AnalyticGate.sq_eps_approx

/-! ## SawtoothApprox -- the polylog rate: x² via the Telgarsky sawtooth at log depth (S3-4 hard) -/

/-- info: 'Sundog.SawtoothApprox.sq_sub_R_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothApprox.sq_sub_R_le

/-- info: 'Sundog.SawtoothApprox.Rcirc_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothApprox.Rcirc_depth

/-- info: 'Sundog.SawtoothApprox.sqNet_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothApprox.sqNet_approx

/-- info: 'Sundog.SawtoothApprox.sq_polylog_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothApprox.sq_polylog_approx

/-! ## MultiplyGate -- toward the general analytic gate: ε-multiplication at log depth -/

/-- info: 'Sundog.MultiplyGate.mult_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MultiplyGate.mult_approx

/-- info: 'Sundog.MultiplyGate.multTrop_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MultiplyGate.multTrop_depth

/-- info: 'Sundog.MultiplyGate.mult_polylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MultiplyGate.mult_polylog

/-! ## MonomialEval -- iterating the multiply gate into monomials x^d at the polynomial rate -/

/-- info: 'Sundog.MonomialEval.clamp01_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MonomialEval.clamp01_contract

/-- info: 'Sundog.MonomialEval.powTrop_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MonomialEval.powTrop_approx

/-- info: 'Sundog.MonomialEval.powTrop_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MonomialEval.powTrop_depth

/-- info: 'Sundog.MonomialEval.pow_poly_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MonomialEval.pow_poly_rate

/-! ## PolyEval -- general polynomials in the monomial basis at the polynomial rate (Cor 5.1) -/

/-- info: 'Sundog.PolyEval.polyTrop_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PolyEval.polyTrop_approx

/-- info: 'Sundog.PolyEval.polyTrop_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PolyEval.polyTrop_depth

/-- info: 'Sundog.PolyEval.poly_polylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PolyEval.poly_polylog

/-! ## UniversalApprox -- the general-continuous capstone (every continuous f is ReLU-approximable) -/

/-- info: 'Sundog.UniversalApprox.polyVal_coeffList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.UniversalApprox.polyVal_coeffList

/-- info: 'Sundog.UniversalApprox.polyEval_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.UniversalApprox.polyEval_approx

/-- info: 'Sundog.UniversalApprox.continuous_relu_approximable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.UniversalApprox.continuous_relu_approximable

/-! ## ApproxCost (Slate-4 U-3) -- the analytic gate's certified op-count in the cost ledger -/

/-- info: 'Sundog.ApproxCost.linesTrop_nodeCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ApproxCost.linesTrop_nodeCount

/-- info: 'Sundog.ApproxCost.analyticGate_dag_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ApproxCost.analyticGate_dag_cost

/-- info: 'Sundog.ApproxCost.analyticGate_cost_eps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ApproxCost.analyticGate_cost_eps

/-! ## SawtoothShared (U-3 follow-on) -- the sawtooth's closed form as a flat sum of iterated tents -/

/-- info: 'Sundog.SawtoothShared.Ssum_eq_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothShared.Ssum_eq_R

/-- info: 'Sundog.SawtoothShared.R_eq_iteratedTents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothShared.R_eq_iteratedTents

/-! ## SawtoothDag (U-3 follow-on) -- the explicit O(m)-gate shared sawtooth DAG (polylog gates) -/

/-- info: 'Sundog.SawtoothDag.compileWith_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothDag.compileWith_eval

/-- info: 'Sundog.SawtoothDag.sawBuild_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothDag.sawBuild_eval

/-- info: 'Sundog.SawtoothDag.sawBuild_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothDag.sawBuild_gate

/-- info: 'Sundog.SawtoothDag.sawDag_polylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SawtoothDag.sawDag_polylog

/-! ## MvMonomial / MvPolyEval (U-1a/b) -- multivariate monomials and polynomials as ReLU Net n -/

/-- info: 'Sundog.MvMonomial.prodTrop_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MvMonomial.prodTrop_approx

/-- info: 'Sundog.MvPolyEval.mvPolyTrop_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MvPolyEval.mvPolyTrop_approx

/-- info: 'Sundog.MvPolyEval.mv_poly_polylog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MvPolyEval.mv_poly_polylog

/-! ## MvUniversalApprox (U-1c/d) -- the multivariate cube capstone (universal approximation) -/

/-- info: 'Sundog.MvUniversalApprox.toTerms_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MvUniversalApprox.toTerms_eval

/-- info: 'Sundog.MvUniversalApprox.coordAlg_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MvUniversalApprox.coordAlg_dense

/-- info: 'Sundog.MvUniversalApprox.continuous_relu_approximable_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MvUniversalApprox.continuous_relu_approximable_cube

/-! ## ApproxCertLedger (U-2) -- approximation certificates in the find/check ledger -/

/-- info: 'Sundog.ApproxCertLedger.approx_from_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ApproxCertLedger.approx_from_samples

/-- info: 'Sundog.ApproxCertLedger.ApproxCert.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ApproxCertLedger.ApproxCert.sound

/-- info: 'Sundog.ApproxCertLedger.ApproxCert.cheap_check_certifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ApproxCertLedger.ApproxCert.cheap_check_certifies

/-! ## ShortestPathCert -- shortest-path optimality certificate (find/check ledger) -/

/-- info: 'Sundog.ShortestPathCert.feasible_le_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShortestPathCert.feasible_le_walk

/-- info: 'Sundog.ShortestPathCert.cert_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShortestPathCert.cert_isLeast

/-- info: 'Sundog.ShortestPathCert.sp_verifier_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShortestPathCert.sp_verifier_cost_le

/-! ## Certifies / MaxFlowMinCut -- LP-duality certificate theory; a cut certifies a flow (N-3) -/

/-- info: 'Sundog.Certifies.weakDuality_tight' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundog.Certifies.weakDuality_tight

/-- info: 'Sundog.MaxFlowMinCut.weak_duality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MaxFlowMinCut.weak_duality

/-- info: 'Sundog.MaxFlowMinCut.maxflow_mincut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MaxFlowMinCut.maxflow_mincut

/-- info: 'Sundog.MatchingCover.matching_le_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MatchingCover.matching_le_cover

/-- info: 'Sundog.MatchingCover.konig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.MatchingCover.konig

/-- info: 'Sundog.TwoSat.check_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TwoSat.check_correct

/-- info: 'Sundog.TwoSat.cert_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TwoSat.cert_sound

/-- info: 'Sundog.PrattCert.cert_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PrattCert.cert_sound

/-- info: 'Sundog.PrattCert.prime_iff_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.PrattCert.prime_iff_witness

/-! ## QueryGap -- the ledger's first PROVED (not imported) find/check gap (S3-3) -/

/-- info: 'Sundog.QueryGap.search_needs_n_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.QueryGap.search_needs_n_queries

/-- info: 'Sundog.QueryGap.checkTree_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.QueryGap.checkTree_eval

/-- info: 'Sundog.QueryGap.checkTree_depth' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.QueryGap.checkTree_depth

/-- info: 'Sundog.QueryGap.check_lt_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.QueryGap.check_lt_find

/-! ## QueryGapCapacity — the capacity-resistance certificate: the "third axis" (determinable yet find-resisting) with a NON-IMPORTED gap -/

/-- info: 'Sundog.QueryGapCapacity.capacity_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.QueryGapCapacity.capacity_certificate

/-! ## AbstractionCert — the find/check ledger's program-synthesis instance (FC-1) -/

/-- info: 'Sundog.AbstractionCert.verify_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AbstractionCert.verify_iff

/-- info: 'Sundog.AbstractionCert.verify_planted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AbstractionCert.verify_planted

/-- info: 'Sundog.AbstractionCert.train_underdetermines' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundog.AbstractionCert.train_underdetermines

/-- info: 'Sundog.AbstractionCert.cost_le' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundog.AbstractionCert.cost_le

/-! ## AbstractionQueryGap — the unconditional find/check separation for an abstraction family (FC-2) -/

/-- info: 'Sundog.AbstractionQueryGap.cbit_eq_verify' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.AbstractionQueryGap.cbit_eq_verify

/-- info: 'Sundog.AbstractionQueryGap.cvec_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AbstractionQueryGap.cvec_rule

/-- info: 'Sundog.AbstractionQueryGap.find_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AbstractionQueryGap.find_ge

/-- info: 'Sundog.AbstractionQueryGap.abstraction_check_lt_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AbstractionQueryGap.abstraction_check_lt_find

/-! ## ShadowDecay — Debye–Waller decay and discrete determination -/

/-- info: 'Sundog.ShadowDecay.debye_waller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecay.debye_waller

/-- info: 'Sundog.ShadowDecay.determination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecay.determination

/-! ## HaloGeometry — minimum-deviation stationarity and local minimum -/

/-- info: 'Sundog.HaloGeometry.min_deviation_stationary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.HaloGeometry.min_deviation_stationary

/-- info: 'Sundog.HaloGeometry.min_deviation_isLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.HaloGeometry.min_deviation_isLocalMin

/-! ## FaradayAB — gauge-circulation invariance and loop = flux -/

/-- info: 'Sundog.FaradayAB.gauge_circulation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FaradayAB.gauge_circulation_zero

/-- info: 'Sundog.FaradayAB.loop_integral_eq_flux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FaradayAB.loop_integral_eq_flux

/-! ## CertWall — row-equivalence invariance, no-tight-robust bound, tight⇒decodes -/

/-- info: 'Sundog.Certificate.CertWall.minCosetWeight_rowEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.CertWall.minCosetWeight_rowEquiv

/--
info: 'Sundog.Certificate.CertWall.colWeightLb_cannot_be_tight_basisRobust' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Sundog.Certificate.CertWall.colWeightLb_cannot_be_tight_basisRobust

/-- info: 'Sundog.Certificate.CertWall.tight_bound_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Certificate.CertWall.tight_bound_decodes

/-! ## ShadowDecayGeneral — the charFun determine/resist law (any probability measure) -/

/-- info: 'Sundog.ShadowDecayGeneral.shadow_decay_charFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayGeneral.shadow_decay_charFun

/-- info: 'Sundog.ShadowDecayGeneral.general_recovers_debye_waller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayGeneral.general_recovers_debye_waller

/-- info: 'Sundog.ShadowDecayGeneral.resistance_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayGeneral.resistance_general

/-- info: 'Sundog.ShadowDecayGeneral.gaussian_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayGeneral.gaussian_resists

/-- info: 'Sundog.ShadowDecayGeneral.determination_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayGeneral.determination_general

/-- info: 'Sundog.ShadowDecayGeneral.gaussian_resist_and_determine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayGeneral.gaussian_resist_and_determine

/-! ## ShadowDecayCauchy — the Cauchy population is the determine/resist separator -/

/-- info: 'Sundog.ShadowDecayCauchy.cauchy_charFun_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayCauchy.cauchy_charFun_tendsto_zero

/-- info: 'Sundog.ShadowDecayCauchy.cauchy_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayCauchy.cauchy_resists

/-- info: 'Sundog.ShadowDecayCauchy.cauchy_no_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayCauchy.cauchy_no_mean

/-- info: 'Sundog.ShadowDecayCauchy.cauchy_is_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayCauchy.cauchy_is_separator

/-- info: 'Sundog.ShadowDecayCauchy.resist_determine_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayCauchy.resist_determine_independent

/-! ## DecodingNPHard — EC3S→decoding (forward + backward both proved; iff unconditional) -/

/-- info: 'Sundog.DecodingNPHard.reduction_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DecodingNPHard.reduction_forward

/-- info: 'Sundog.DecodingNPHard.reduction_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DecodingNPHard.reduction_iff

/-! ## ShadowDecayLattice — AC resists (Riemann–Lebesgue), the lattice two-point survives -/

/-- info: 'Sundog.ShadowDecayLattice.absCont_charFun_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.absCont_charFun_tendsto_zero

/-- info: 'Sundog.ShadowDecayLattice.absCont_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.absCont_resists

/-- info: 'Sundog.ShadowDecayLattice.twoPoint_charFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.twoPoint_charFun

/-- info: 'Sundog.ShadowDecayLattice.twoPoint_does_not_resist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.twoPoint_does_not_resist

/-- info: 'Sundog.ShadowDecayLattice.twoPoint_shadow_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.twoPoint_shadow_survives

/-- info: 'Sundog.ShadowDecayLattice.resist_separates_ac_from_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.resist_separates_ac_from_lattice

/-- info: 'Sundog.ShadowDecayLattice.resist_orthogonal_to_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ShadowDecayLattice.resist_orthogonal_to_variance

/-! ## 3SAT ≤ 3DM ≤ X3C ≤ Decodes — the machine-checked Karp reduction correctness.

    Gadget cores (the wheel two-state engine, the clause polarity bridge), the index bridge and the
    data-layer chain-connect, both reduction directions, and the end-to-end headline.  Guarding the
    top-level `sat_iff_decodes` transitively protects the whole chain (its axiom set would change if
    any dependency regressed).  `litTipFree_iff_eval` is `[propext]` only — a genuine subset. -/

/-- info: 'Sundog.SATNPHard.ex_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SATNPHard.ex_sat

/-- info: 'Sundog.VarWheel.validCover_iff_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.VarWheel.validCover_iff_const

/-- info: 'Sundog.ClauseGadget.litTipFree_iff_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.ClauseGadget.litTipFree_iff_eval

/-- info: 'Sundog.SATReduction.reduce_chain_connects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SATReduction.reduce_chain_connects

/-- info: 'Sundog.ThreeDMReindex.threeDM_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ThreeDMReindex.threeDM_reindex

/-- info: 'Sundog.SATReductionReverse.reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SATReductionReverse.reverse

/-- info: 'Sundog.SATReductionForward.forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SATReductionForward.forward

/-- info: 'Sundog.SATReductionMain.sat_iff_threeDM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SATReductionMain.sat_iff_threeDM

/-- info: 'Sundog.SATReductionMain.sat_iff_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SATReductionMain.sat_iff_decodes

/-! ## AuditCost — audit asymmetry (HS7): sound cheap audit + ∀-verifier blindness -/

/-- info: 'Sundog.AuditCost.audit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AuditCost.audit_sound

/-- info: 'Sundog.AuditCost.auditCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AuditCost.auditCost_le

/-- info: 'Sundog.AuditCost.pooled_channel_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AuditCost.pooled_channel_blind

set_option linter.style.longLine false in
/-- info: 'Sundog.AuditCost.no_verifier_checks_perUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AuditCost.no_verifier_checks_perUnit

/-- info: 'Sundog.AuditCost.audit_asymmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AuditCost.audit_asymmetry

/-! ### UniformBlind — the uniformization blind point (∀-probe blindness at uniform pushforward) -/

/-- info: 'Sundog.UniformBlind.uniform_shift_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.UniformBlind.uniform_shift_blind

/-- info: 'Sundog.UniformBlind.verdict_count_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.UniformBlind.verdict_count_eq

/-- info: 'Sundog.UniformBlind.nonuniform_probe_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.UniformBlind.nonuniform_probe_exists

/-! ## CircuitNet — exact tropical-circuit → ReLU-network compilation -/

/-- info: 'Sundog.CircuitNet.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CircuitNet.compile_eval

/-- info: 'Sundog.CircuitNet.compile_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CircuitNet.compile_depth_le

set_option linter.style.longLine false in
/-- info: 'Sundog.CircuitNet.compileToDag_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CircuitNet.compileToDag_gate_count

/-- info: 'Sundog.CircuitNet.compileToDag_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CircuitNet.compileToDag_eval

/-- info: 'Sundog.CircuitNet.appendMax_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CircuitNet.appendMax_eval

set_option linter.style.longLine false in
/-- info: 'Sundog.CircuitNet.bellmanStep_compiles_exactly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CircuitNet.bellmanStep_compiles_exactly

/-! ## AgenticTrace -- first formal hooks for trace-governed agent search -/

/-- info: 'Sundog.AgenticTrace.rs_receipt_accept_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.rs_receipt_accept_safe

/-- info: 'Sundog.AgenticTrace.rs_receipt_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.rs_receipt_unique

/-- info: 'Sundog.AgenticTrace.trace_gated_noninterference' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.trace_gated_noninterference

/-- info: 'Sundog.AgenticTrace.branch_count_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.branch_count_le_budget

/-- info: 'Sundog.AgenticTrace.not_branch_count_gt_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.not_branch_count_gt_budget

/-! ### Decisive-source binding -- the H-I falsifier fix (content preservation) -/

/-- info: 'Sundog.AgenticTrace.decisive_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.decisive_kept

/-- info: 'Sundog.AgenticTrace.decisive_pruned_not_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.decisive_pruned_not_kept

set_option linter.style.longLine false in
/-- info: 'Sundog.AgenticTrace.decisive_receipt_safe_and_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.decisive_receipt_safe_and_preserving

/-! ### Decisive designation is necessarily external (the word under-determines it) -/

set_option linter.style.longLine false in
/-- info: 'Sundog.AgenticTrace.decisive_underdetermined_by_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.decisive_underdetermined_by_word

set_option linter.style.longLine false in
/-- info: 'Sundog.AgenticTrace.no_word_function_determines_decisive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AgenticTrace.no_word_function_determines_decisive

/-! ## DiscreteHolonomy -- finite gauge zero-out for closed trace loops -/

/-- info: 'Sundog.DiscreteHolonomy.sum_discreteDiff_eq_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DiscreteHolonomy.sum_discreteDiff_eq_endpoint

/-- info: 'Sundog.DiscreteHolonomy.gauge_sum_eq_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DiscreteHolonomy.gauge_sum_eq_endpoint

/-- info: 'Sundog.DiscreteHolonomy.closed_gauge_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DiscreteHolonomy.closed_gauge_sum_zero

/-- info: 'Sundog.DiscreteHolonomy.gauge_sum_path_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DiscreteHolonomy.gauge_sum_path_independent

-- ContextDecay: the fold-pair annihilation quarantine rule (H-II deductive core).
-- The runtime detector is scripts/foldpair_detector.py; these pin what an
-- annihilation receipt licenses, the way the AgenticTrace.decisive_* lemmas pinned
-- the H-I fix. All within the foundational triple (here a subset: no Classical.choice).

/-- info: 'Sundog.ContextDecay.decay_earned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ContextDecay.decay_earned

/-- info: 'Sundog.ContextDecay.foldfree_no_decay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ContextDecay.foldfree_no_decay

/-- info: 'Sundog.ContextDecay.stable_no_decay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ContextDecay.stable_no_decay

/-- info: 'Sundog.ContextDecay.decays_iff_foldpair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ContextDecay.decays_iff_foldpair

/-- info: 'Sundog.ContextDecay.annihilation_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ContextDecay.annihilation_budget

-- CuspGerm: the cubic fold-catastrophe germ x³−a·x realizes a ContextDecay annihilation
-- (fold count 2 for a>0, 0 for a<0). Grounds the abstract rule in the real germ, the
-- way AgenticTrace.decisive_* is grounded in RS agree/Polynomial. Real-analysis germ
-- (Real.sqrt, Set.ncard) ⇒ the full foundational triple, no sorryAx / native_decide.

/-- info: 'Sundog.CuspGerm.critCount_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CuspGerm.critCount_neg

/-- info: 'Sundog.CuspGerm.critCount_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CuspGerm.critCount_pos

/-- info: 'Sundog.CuspGerm.cubic_realizes_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CuspGerm.cubic_realizes_annihilation

/-- info: 'Sundog.CuspGerm.cubic_foldpair_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.CuspGerm.cubic_foldpair_witness

-- RetrievalCusp: the attractor-memory energy landscape V_a = x⁴/4 − a·x²/2 realizes a
-- ContextDecay annihilation (critical-point count 3 for a>0, 1 for a<0). The H-II
-- mapping step — narrows the import to "real retrieval ≈ this attractor model".

/-- info: 'Sundog.RetrievalCusp.critCountW_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RetrievalCusp.critCountW_neg

/-- info: 'Sundog.RetrievalCusp.critCountW_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RetrievalCusp.critCountW_pos

/-- info: 'Sundog.RetrievalCusp.memories_are_minima' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RetrievalCusp.memories_are_minima

/-- info: 'Sundog.RetrievalCusp.retrieval_realizes_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RetrievalCusp.retrieval_realizes_annihilation

/-- info: 'Sundog.RetrievalCusp.retrieval_foldpair_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.RetrievalCusp.retrieval_foldpair_witness

-- HierarchyHolonomy: the H-III injection-quarantine core. The rule fires exactly on a
-- hierarchy violation; the loop circulation provably cannot determine the hierarchy
-- (the gauge zero-out is the blind spot); the gradient/endpoint carries it. Mirrors the
-- H-II ContextDecay core; the runtime is scripts/hierarchy_holonomy_receipt.py.

/-- info: 'Sundog.HierarchyHolonomy.intact_iff_not_hijacked' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundog.HierarchyHolonomy.intact_iff_not_hijacked

/-- info: 'Sundog.HierarchyHolonomy.hijack_witness' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.HierarchyHolonomy.hijack_witness

/-- info: 'Sundog.HierarchyHolonomy.authority_gap_along_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.HierarchyHolonomy.authority_gap_along_path

/-- info: 'Sundog.HierarchyHolonomy.loopCirc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.HierarchyHolonomy.loopCirc_zero

/--
info: 'Sundog.HierarchyHolonomy.hierarchy_separates_what_loop_cannot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Sundog.HierarchyHolonomy.hierarchy_separates_what_loop_cannot

-- StructuralSlot: the H-IV line-free (cap-set) trace-bound core. A refusal is earned;
-- admission preserves the cap; the cap is bounded by the space (depth-independent); and a
-- count cannot determine line-freeness (the blind spot). Runtime: structural_slot_receipt.py.

/-- info: 'Sundog.StructuralSlot.refusal_earned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StructuralSlot.refusal_earned

/-- info: 'Sundog.StructuralSlot.admit_preserves_lineFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StructuralSlot.admit_preserves_lineFree

/-- info: 'Sundog.StructuralSlot.lineFree_card_le_univ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StructuralSlot.lineFree_card_le_univ

/-- info: 'Sundog.StructuralSlot.count_cannot_determine_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.StructuralSlot.count_cannot_determine_structure

/-! ## ParityNoSufficientStat — parity barrier (toy half): no finite-order sufficient stat -/

/-- info: 'Sundog.ParityNoSufficientStat.parity_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ParityNoSufficientStat.parity_split

/-- info: 'Sundog.ParityNoSufficientStat.partial_not_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ParityNoSufficientStat.partial_not_sufficient

/-- info: 'Sundog.ParityNoSufficientStat.suffStatOrder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.ParityNoSufficientStat.suffStatOrder_eq

/-! ## OrderRelative — the order-relative resolution law (the slate's one statement; schema, not scalar) -/

/-- info: 'Sundog.OrderRelative.budget_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.budget_monotone

/-- info: 'Sundog.OrderRelative.resolvable_iff_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.resolvable_iff_finite

/-- info: 'Sundog.OrderRelative.resists_iff_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.resists_iff_infinite

/-- info: 'Sundog.OrderRelative.parityProblem_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.parityProblem_ord

/-- info: 'Sundog.OrderRelative.resistPole_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.resistPole_resists

/-- info: 'Sundog.OrderRelative.order_is_schema_not_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.order_is_schema_not_scalar

/-! ### OrderRelative — second grounded axis (coordinate-locality) -/

/-- info: 'Sundog.OrderRelative.prefixSufficient_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.prefixSufficient_iff

/-- info: 'Sundog.OrderRelative.localityProblem_ord_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.localityProblem_ord_ne_top

/-- info: 'Sundog.OrderRelative.two_axes_and_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.two_axes_and_pole

/-! ### OrderRelative — third grounded axis (search reachability / rational denominator) -/

/-- info: 'Sundog.OrderRelative.rationalReachProblem_ord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.rationalReachProblem_ord

/-- info: 'Sundog.OrderRelative.irrationalReach_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.irrationalReach_resists

/-- info: 'Sundog.OrderRelative.search_resist_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.search_resist_sqrt_two

/-! ### OrderRelative — fourth axis (radical reach) + an honest mode-vector on √2 -/

/-- info: 'Sundog.OrderRelative.radicalReachSqrtTwo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.radicalReachSqrtTwo_iff

/-- info: 'Sundog.OrderRelative.sqrt_two_mode_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.sqrt_two_mode_vector

/-! ### OrderRelative — fifth axis (spectral / moment): determine/resist's home; order is binary -/

/-- info: 'Sundog.OrderRelative.Moment.cauchyMoment_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Moment.cauchyMoment_resists

/-- info: 'Sundog.OrderRelative.Moment.moment_gaussian_vs_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Moment.moment_gaussian_vs_cauchy

/-! ### OrderRelative — sixth axis (algebraic degree): the mode-vector on the real BoxSEL optimum -/

/-- info: 'Sundog.OrderRelative.AlgDegree.algDegReaches_boxOpt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.AlgDegree.algDegReaches_boxOpt_iff

/-- info: 'Sundog.OrderRelative.AlgDegree.boxOpt_mode_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.AlgDegree.boxOpt_mode_vector

/-! ### OrderRelative — seventh axis (topological / cohomological): determine ⟺ torsion, resist ⟺ free -/

/-- info: 'Sundog.OrderRelative.Cohomology.freeClass_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Cohomology.freeClass_resists

/-- info: 'Sundog.OrderRelative.Cohomology.torsion_vs_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Cohomology.torsion_vs_free

/-! ### OrderRelative — the cohomological mode-vector (scalar order is the lossy join of a vector) -/

/-- info: 'Sundog.OrderRelative.Cohomology.mixed_mode_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Cohomology.mixed_mode_vector

/-! ### OrderRelative — the composition law (scalar order of a product = lcm = divisibility join) -/

/-- info: 'Sundog.OrderRelative.Compose.compose_order_eq_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Compose.compose_order_eq_lcm

/-- info: 'Sundog.OrderRelative.Compose.compose_lcm_not_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Compose.compose_lcm_not_max

/-! ### OrderRelative — the composition boundary: join-homo iff the product is cancellation-free -/

/-- info: 'Sundog.OrderRelative.ComposeLaw.algDeg_not_join_under_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ComposeLaw.algDeg_not_join_under_mul

/-- info: 'Sundog.OrderRelative.ComposeLaw.annihilates_prod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ComposeLaw.annihilates_prod

/-- info: 'Sundog.OrderRelative.ComposeLaw.within_group_cancels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ComposeLaw.within_group_cancels

/-! ### OrderRelative — the radical axis (multiplicative twin; join-homo axes = group-order axes) -/

/-- info: 'Sundog.OrderRelative.RadicalCompose.mul_annihilates_prod' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.RadicalCompose.mul_annihilates_prod

/-- info: 'Sundog.OrderRelative.RadicalCompose.radical_cancel_sqrt2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.RadicalCompose.radical_cancel_sqrt2

/-! ### OrderRelative — the converse fails (idempotency obstruction) + the unified coproduct law -/

/-- info: 'Sundog.OrderRelative.Converse.idempotent_eq_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Converse.idempotent_eq_one

/-- info: 'Sundog.OrderRelative.Converse.moment_idempotent_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Converse.moment_idempotent_nontrivial

/-- info: 'Sundog.OrderRelative.Converse.converse_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Converse.converse_fails

/-- info: 'Sundog.OrderRelative.Converse.coproduct_pow_eq_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Converse.coproduct_pow_eq_one

/-- info: 'Sundog.OrderRelative.Converse.coproduct_nsmul_eq_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Converse.coproduct_nsmul_eq_zero

/-! ### OrderRelative — the search-reach negative, machine-checked (the boundary's 2nd negative) -/

/-- info: 'Sundog.OrderRelative.SearchNeg.search_not_join_under_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.SearchNeg.search_not_join_under_mul

/-! ### OrderRelative — the approximation axis (exactness is order-relative; ε-approx collapses) -/

/-- info: 'Sundog.OrderRelative.Approx.sq_no_pieceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Approx.sq_no_pieceCover

/-- info: 'Sundog.OrderRelative.Approx.sq_not_exactly_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Approx.sq_not_exactly_net

/-- info: 'Sundog.OrderRelative.Approx.exact_determine_vs_resist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Approx.exact_determine_vs_resist

/-- info: 'Sundog.OrderRelative.Approx.approx_axis_collapses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Approx.approx_axis_collapses

/-! ### OrderRelative — the approximation axis GRADED (piece count) + a 2nd resist (eˣ) -/

/-- info: 'Sundog.OrderRelative.ApproxGraded.graded_exactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxGraded.graded_exactness

/-- info: 'Sundog.OrderRelative.ApproxGraded.exp_no_pieceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxGraded.exp_no_pieceCover

/-- info: 'Sundog.OrderRelative.ApproxGraded.exp_not_exactly_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxGraded.exp_not_exactly_net

/-! ### OrderRelative — the approximation ladder's third rung (step2 at order 3, 1 < 2 < 3) -/

/-- info: 'Sundog.OrderRelative.ApproxLadder.step2_hasPieceCover_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadder.step2_hasPieceCover_iff

/-- info: 'Sundog.OrderRelative.ApproxLadder.step2_not_pieceCover_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadder.step2_not_pieceCover_two

/-- info: 'Sundog.OrderRelative.ApproxLadder.ladder3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadder.ladder3

/-! ### OrderRelative — the general k-breakpoint rung (Σ ReLU(x-i) at order k+1, unbounded ladder) -/

/-- info: 'Sundog.OrderRelative.ApproxLadderK.sumRelu_hasPieceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadderK.sumRelu_hasPieceCover

/-- info: 'Sundog.OrderRelative.ApproxLadderK.sumRelu_bend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadderK.sumRelu_bend

/-- info: 'Sundog.OrderRelative.ApproxLadderK.sumRelu_not_pieceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadderK.sumRelu_not_pieceCover

/--
info: 'Sundog.OrderRelative.ApproxLadderK.sumRelu_hasPieceCover_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadderK.sumRelu_hasPieceCover_iff

/-- info: 'Sundog.OrderRelative.ApproxLadderK.sumRelu_order_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadderK.sumRelu_order_eq

/-- info: 'Sundog.OrderRelative.ApproxLadderK.ladderK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.ApproxLadderK.ladderK

/-! ### OrderRelative — the moment axis is join-homo under convolution (the analysis residual) -/

/-- info: 'Sundog.OrderRelative.MomentConv.indepFun_integrable_add_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.MomentConv.indepFun_integrable_add_iff

/-! ### OrderRelative — the grading law abstracted (ord(product) = lcm; axes as instances) -/

/-- info: 'Sundog.OrderRelative.Grading.orderOf_prod_eq_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Grading.orderOf_prod_eq_lcm

/-- info: 'Sundog.OrderRelative.Grading.addOrderOf_prod_eq_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Grading.addOrderOf_prod_eq_lcm

/-- info: 'Sundog.OrderRelative.Grading.cohomological_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Grading.cohomological_compose

/-! ### OrderRelative — the radical axis as a full instance (the ℝˣ/ℚˣ quotient model) -/

/-- info: 'Sundog.OrderRelative.RadicalQuotient.radicalReaches_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.RadicalQuotient.radicalReaches_iff

/-- info: 'Sundog.OrderRelative.RadicalQuotient.rad_pow_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.RadicalQuotient.rad_pow_eq_one_iff

/-- info: 'Sundog.OrderRelative.RadicalQuotient.radical_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.RadicalQuotient.radical_compose

/-! ### OrderRelative — the n-ary grading law + the structure-theorem mode-vector -/

/-- info: 'Sundog.OrderRelative.Structure.orderOf_pi_eq_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Structure.orderOf_pi_eq_lcm

/-- info: 'Sundog.OrderRelative.Structure.addOrderOf_pi_eq_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Structure.addOrderOf_pi_eq_lcm

/-- info: 'Sundog.OrderRelative.Structure.structure_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Structure.structure_order

/-- info: 'Sundog.OrderRelative.Structure.structure_mode_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Structure.structure_mode_vector

/-! ### DefinableRate (U-4) — the explicit uniform piece-count modulus (PL finiteness-modulus) -/

set_option linter.style.longLine false in
/-- info: 'Sundog.DefinableRate.net_pieceBound_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DefinableRate.net_pieceBound_cover

set_option linter.style.longLine false in
/-- info: 'Sundog.DefinableRate.sqNet_definable_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.DefinableRate.sqNet_definable_rate

/-! ### OMinimalOne (o-min ladder rung 1) — dimension-one o-minimality, two tame structures -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalOne.affineAway_levelSet_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalOne.affineAway_levelSet_tame

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalOne.netDef_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalOne.netDef_tame

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalOne.polyDef_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalOne.polyDef_tame

/-! ### Percival — finite court-separation anchor -/

/-- info: 'Sundogcert.Percival.best_quantilizer_is_base_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.best_quantilizer_is_base_three

/-- info: 'Sundogcert.Percival.clean_support_above_separation_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.clean_support_above_separation_three

/-! ### PercivalGeneral — general court-separation anchors (S4: n-point best-quantilizer-is-base + clean separation) -/

/-- info: 'Sundogcert.Percival.upper_tail_mul_le_base_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.upper_tail_mul_le_base_mul

/-- info: 'Sundogcert.Percival.best_quantilizer_is_base_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.best_quantilizer_is_base_general

/-- info: 'Sundogcert.Percival.clean_support_above_separation_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.clean_support_above_separation_general

/-! ### PercivalCapClass — the Sov_opt classification (OR-5 Leg A: outgoing bounded ∀ interventions, incoming unconstrained) -/

/-- info: 'Sundogcert.Percival.cap_sov_le_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.cap_sov_le_kappa

/-- info: 'Sundogcert.Percival.cap_bounds_outgoing_swing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.cap_bounds_outgoing_swing

/-- info: 'Sundogcert.Percival.cap_ignores_incoming_sensitivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.cap_ignores_incoming_sensitivity

/-! ### PercivalKeyedMargin — the keyed-composition margin law (OR-1: cap bound exactly additive, court value additive in no recoding) -/

/-- info: 'Sundogcert.Percival.cap_bound_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.cap_bound_additive

/-- info: 'Sundogcert.Percival.cap_bound_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.cap_bound_tight

/-- info: 'Sundogcert.Percival.cap_marginal_profile_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.cap_marginal_profile_independent

/-- info: 'Sundogcert.Percival.pivotal_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.pivotal_threshold

/-- info: 'Sundogcert.Percival.coalition_flips' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.coalition_flips

/-- info: 'Sundogcert.Percival.court_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.court_not_product

/-- info: 'Sundogcert.Percival.court_value_not_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.court_value_not_additive

/-- info: 'Sundogcert.Percival.keyed_margin_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.keyed_margin_law

/-! ### PercivalTargetCollapse — the OR-4 write-side ∞ cell (collapse + priced write + probe read) -/

/-- info: 'Sundogcert.Percival.dou_invariant_factors' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.dou_invariant_factors

/-- info: 'Sundogcert.Percival.dou_comp_le_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.dou_comp_le_beta

/-- info: 'Sundogcert.Percival.followU_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.followU_comp

/-- info: 'Sundogcert.Percival.target_write_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.target_write_resists

/-- info: 'Sundogcert.Percival.dependsU_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.dependsU_probe

/-- info: 'Sundogcert.Percival.measurable_ne_enforceable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.measurable_ne_enforceable

/-! ### PercivalAuditPay — ME-3: audit-and-pay implements the safe point iff t ≥ ρ−β -/

/-- info: 'Sundogcert.Percival.followV_invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.followV_invariant

/-- info: 'Sundogcert.Percival.comp_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.comp_le_rho

/-- info: 'Sundogcert.Percival.audit_pay_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.audit_pay_implements

/-- info: 'Sundogcert.Percival.audit_pay_underpays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.audit_pay_underpays

/-- info: 'Sundogcert.Percival.audit_and_pay_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.audit_and_pay_iff

/-! ### PercivalNodeEdge — ME-2: every node-write enforcing the edge is a channel retreat -/

/-- info: 'Sundogcert.Percival.owned_node_writable' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.owned_node_writable

/-- info: 'Sundogcert.Percival.node_write_enforces_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.node_write_enforces_iff

/-- info: 'Sundogcert.Percival.node_write_enforce_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.node_write_enforce_price

/-- info: 'Sundogcert.Percival.node_edge_typing_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.node_edge_typing_law

/-! ### PercivalSynergy — ME-5: the XOR joint where the edge formula reads 0 but the price is 1/2 -/

/-- info: 'Sundogcert.Percival.xor_vonly_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.xor_vonly_half

/-- info: 'Sundogcert.Percival.xor_full_attains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.xor_full_attains

/-- info: 'Sundogcert.Percival.xor_invariant_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.xor_invariant_le_half

/-- info: 'Sundogcert.Percival.synergy_edge_formula_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.synergy_edge_formula_fails

/-! ### PercivalNoisyMargin — Track-C v3: crispness is pairing (zero-coverage noise-invariance + bounded-noise recovery + unpaired fragility) -/

/-- info: 'Sundogcert.Percival.zero_coverage_margin_noise_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.zero_coverage_margin_noise_invariant

/-- info: 'Sundogcert.Percival.zero_coverage_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.zero_coverage_capture

/-- info: 'Sundogcert.Percival.bounded_noise_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.bounded_noise_recovery

/-- info: 'Sundogcert.Percival.unpaired_flip_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.unpaired_flip_witness

/-! ### PercivalFixedPoint — Track-C v4: the Angle-4 fixed-point gate (deploy-correct chain: corrigible/wirehead/wandering regimes) -/

/-- info: 'Sundogcert.Percival.Chain.round_miss_falls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.round_miss_falls

/-- info: 'Sundogcert.Percival.Chain.round_miss_noninverted_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.round_miss_noninverted_recovers

/-- info: 'Sundogcert.Percival.Chain.round_hit_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.round_hit_recovers

/-- info: 'Sundogcert.Percival.Chain.corrigible_absorbing' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.corrigible_absorbing

/-- info: 'Sundogcert.Percival.Chain.fall_without_coverage' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.fall_without_coverage

/-- info: 'Sundogcert.Percival.Chain.wirehead_absorbing' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.wirehead_absorbing

/-- info: 'Sundogcert.Percival.Chain.grace_exits_wirehead' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.grace_exits_wirehead

/-- info: 'Sundogcert.Percival.Chain.global_convergence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.global_convergence

/-- info: 'Sundogcert.Percival.Chain.capture_global' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.capture_global

/-- info: 'Sundogcert.Percival.Chain.wandering_period_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Chain.wandering_period_two

/-! ### PercivalBasin — LP-4: the corrigibility basin over ARBITRARY hypothesis space (breadth governed by coverage, not preference-neighbourhood) -/

/-- info: 'Sundogcert.Percival.Basin.basin_empty_without_self_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Basin.basin_empty_without_self_coverage

/-- info: 'Sundogcert.Percival.Basin.basin_univ_full_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundogcert.Percival.Basin.basin_univ_full_coverage

/-! ### OrderRelativeKeyed — the OR-2 boundary instance (cancellation-free margins vs idempotent readout) -/

/-- info: 'Sundog.OrderRelative.Keyed.margin_zerosumfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.margin_zerosumfree

/-- info: 'Sundog.OrderRelative.Keyed.margin_torsion_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.margin_torsion_free

/-- info: 'Sundog.OrderRelative.Keyed.cap_margins_coproduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.cap_margins_coproduct

/-- info: 'Sundog.OrderRelative.Keyed.cap_margin_order_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.cap_margin_order_join

/-- info: 'Sundog.OrderRelative.Keyed.court_readout_idempotent' does not depend on any axioms -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.court_readout_idempotent

/-- info: 'Sundog.OrderRelative.Keyed.court_readout_not_group_order' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.court_readout_not_group_order

/-- info: 'Sundog.OrderRelative.Keyed.threshold_readout_not_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.threshold_readout_not_hom

/-- info: 'Sundog.OrderRelative.Keyed.keyed_boundary_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OrderRelative.Keyed.keyed_boundary_instance

/-! ### SurfaceBag — the order-blind bag: depth determined, stack-top resists (H2/σ-bridge anchor) -/

/-- info: 'Sundog.SurfaceBag.bagSufficient_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SurfaceBag.bagSufficient_depth

/-- info: 'Sundog.SurfaceBag.not_bagSufficient_stackTop' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SurfaceBag.not_bagSufficient_stackTop

/-- info: 'Sundog.SurfaceBag.bag_determines_depth_not_stackTop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SurfaceBag.bag_determines_depth_not_stackTop

/-! ### SurfaceBagGraded — OR-6: the stack-top resists EVERY window (σ_surface = ∞) -/

/-- info: 'Sundog.SurfaceBag.Graded.window_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SurfaceBag.Graded.window_swap

/-- info: 'Sundog.SurfaceBag.Graded.wcount_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SurfaceBag.Graded.wcount_eq

/-- info: 'Sundog.SurfaceBag.Graded.stackTop_resists_every_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SurfaceBag.Graded.stackTop_resists_every_window

/-! ### AveragingDecodability — amplitude washes, the rescaling readout does not (AT-6 anchor) -/

/-- info: 'Sundog.AveragingDecodability.decodable_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AveragingDecodability.decodable_mul_iff

/-- info: 'Sundog.AveragingDecodability.zero_shadow_not_decodable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AveragingDecodability.zero_shadow_not_decodable

/--
info: 'Sundog.AveragingDecodability.amplitude_washes_readout_does_not' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Sundog.AveragingDecodability.amplitude_washes_readout_does_not

/-- info: 'Sundog.AveragingDecodability.averaging_types_shadows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.AveragingDecodability.averaging_types_shadows

/-! ### OMinimalRate (o-min ladder R2-M/R2-Q) — monotonicity instance + the frontier modulus -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalRate.net_mono_or_anti_between_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalRate.net_mono_or_anti_between_cuts

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalRate.affineAway_levelSet_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalRate.affineAway_levelSet_ncard

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalRate.net_levelSet_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalRate.net_levelSet_ncard

/-! ### OMinimalNormalForm (o-min ladder R2-N) — Tame ↔ points ∪ open intervals -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalNormalForm.tame_iff_normalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalNormalForm.tame_iff_normalForm

/-! ### Semilinear (o-min ladder R3-semilinear 1/2) — boolean closure + the 1-D tame landing -/

set_option linter.style.longLine false in
/-- info: 'Sundog.Semilinear.slCompl₂_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Semilinear.slCompl₂_holds

set_option linter.style.longLine false in
/-- info: 'Sundog.Semilinear.slHolds₁_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.Semilinear.slHolds₁_tame

/-! ### FourierMotzkin (o-min ladder R3-semilinear 2/2) — the projection axiom, dims 2 → 1 -/

set_option linter.style.longLine false in
/-- info: 'Sundog.FourierMotzkin.projSL_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FourierMotzkin.projSL_correct

set_option linter.style.longLine false in
/-- info: 'Sundog.FourierMotzkin.proj_semilinear_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FourierMotzkin.proj_semilinear_tame

/-! ### OMinimalStructure (o-min ladder R4-A) — the abstract structure + definable calculus -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.OMinStructure.DefinableFun.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.OMinStructure.DefinableFun.comp

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.isOpen_ordConnected_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.isOpen_ordConnected_shape

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.s1_eq_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.s1_eq_tame

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.defFun_tame_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.defFun_tame_level

/-! ### SemilinearN (o-min ladder R4-B1) — n-dim semilinear syntax + boolean closure -/

set_option linter.style.longLine false in
/-- info: 'Sundog.SemilinearN.slInterN_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SemilinearN.slInterN_holds

set_option linter.style.longLine false in
/-- info: 'Sundog.SemilinearN.slComplN_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SemilinearN.slComplN_holds

set_option linter.style.longLine false in
/-- info: 'Sundog.SemilinearN.substSLN_toSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SemilinearN.substSLN_toSet

/-! ### FourierMotzkinN (o-min ladder R4-B3) — eliminate the last variable, n dims -/

set_option linter.style.longLine false in
/-- info: 'Sundog.FourierMotzkinN.projCellN_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FourierMotzkinN.projCellN_correct

set_option linter.style.longLine false in
/-- info: 'Sundog.FourierMotzkinN.projSLN_toSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.FourierMotzkinN.projSLN_toSet

/-! ### SemilinearStructure (o-min ladder R4-B4) — the first machine-checked o-min structure -/

set_option linter.style.longLine false in
/-- info: 'Sundog.SemilinearInstance.semilinearStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SemilinearInstance.semilinearStructure

set_option linter.style.longLine false in
/-- info: 'Sundog.SemilinearInstance.semilinear_s1_eq_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SemilinearInstance.semilinear_s1_eq_tame

set_option linter.style.longLine false in
/-- info: 'Sundog.SemilinearInstance.semilinear_defFun_tame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.SemilinearInstance.semilinear_defFun_tame

/-! ### OMinimalFormula (o-min ladder R4-C0) — the formula layer (definability by reflection) -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.Fml.definable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.Fml.definable

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.Fml.tame_right_inc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.Fml.tame_right_inc

/-! ### OMinimalTrichotomy (o-min ladder R4-C1a) — interval-in-infinite + eventual signs -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_infinite_contains_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_infinite_contains_Ioo

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.eventual_right_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.eventual_right_sign

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.eventual_left_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.eventual_left_sign

/-! ### OMinimalSignPartition (o-min ladder R4-C1b) — one behavior class per gap -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.sign_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.sign_partition

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.right_sign_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.right_sign_cover

/-! ### OMinimalGluing (o-min ladder R4-C1c) — local behavior globalizes, no continuity -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.rel_propagate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.rel_propagate

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.strictMonoOn_of_locInc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.strictMonoOn_of_locInc

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.eqOn_of_locConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.eqOn_of_locConst

/-! ### OMinimalMonotonicity (o-min ladder R4-C1d) — THE MONOTONICITY THEOREM -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.badSet_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.badSet_finite

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.monotonicity_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.monotonicity_theorem

/-! ### OMinimalContinuity (o-min ladder R4-C2a) — order bridge + tame discontinuity set -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.continuousAt_iff_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.continuousAt_iff_order

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_discSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_discSet

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_image

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.strictMonoOn_exists_continuityPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.strictMonoOn_exists_continuityPt

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.discSet_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.discSet_finite

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.monotonicity_theorem_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.monotonicity_theorem_continuous

/-! ### OMinimalSlice (o-min ladder R4-D0) — slices + the fiber-frontier set -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_slice

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.definable_fiberFrontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.definable_fiberFrontier

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.fiberFrontier_fiber_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.fiberFrontier_fiber_finite

/-! ### OMinimalCounting (o-min ladder R4-D1) — reindex + the tame counting sets -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.Fml.eval_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.Fml.eval_reindex

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_countSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_countSet

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.infinite_fiber_of_mem_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.infinite_fiber_of_mem_all

/-! ### OMinimalPointFns (o-min ladder R4-D2) — the dichotomy kill + definable rank functions -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.exists_interval_in_countSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.exists_interval_in_countSet

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.isNth_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.isNth_exists

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.definableFun_nthFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.definableFun_nthFn

/-! ### OMinimalCurves (o-min ladder R4-D3) — the k-curve extraction -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.isNth_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.isNth_lt

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.isNth_exists_of_mem_countSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.isNth_exists_of_mem_countSet

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.exists_k_ordered_curves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.exists_k_ordered_curves

/-! ### OMinimalNormal (o-min ladder R4-D4a) — the normality layer -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.definable_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.definable_normal

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.normal_slice_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.normal_slice_isOpen

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_normalTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_normalTop

/-! ### OMinimalBeta (o-min ladder R4-D4b) — the β-machinery -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.definableFun_selFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.definableFun_selFn

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.definableFun_betaFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.definableFun_betaFn

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_badFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_badFin

/-! ### OMinimalBadFinite (o-min ladder R4-D4c) — the tube kill: bad sets are finite -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.notNormalTop_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.notNormalTop_finite

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.badFin_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.badFin_finite

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.abnormal_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.abnormal_finite

/-! ### OMinimalUniformFiniteness (o-min ladder R4-D4d) — THE FINITENESS LEMMA -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.count_locally_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.count_locally_constant

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.uniform_finiteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.uniform_finiteness

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.exists_empty_countSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.exists_empty_countSet

/-! ### OMinimalFrontierBound (o-min ladder R4-D5a) — the uniform frontier bound -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.frontier_ncard_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.frontier_ncard_bound

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.ranks_enumerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.ranks_enumerate

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.frontier_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.frontier_partition

/-! ### OMinimalRefinement (o-min ladder R4-D5b) — the master refinement -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_bandIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_bandIn

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.tame_const_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.tame_const_on

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.master_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.master_refinement

/-! ### OMinimalBandTriviality (o-min ladder R4-D5c) — the CDT₂ core -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.band_dichotomy_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.band_dichotomy_fiber

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.regions_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.regions_cover

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.band_triviality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.band_triviality

/-! ### OMinimalCells (o-min ladder R4-D5d-1) — the Cell₂ packaging layer -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.baseCells_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.baseCells_covers

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.baseCells_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.baseCells_pairwise

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.univ_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.univ_uniform

/-! ### OMinimalCellDecomp (o-min ladder R4-D5d-2) — CELL DECOMPOSITION FOR ℝ² -/

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.cell_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.cell_decomposition

set_option linter.style.longLine false in
/-- info: 'Sundog.OMinimalAbstract.cell_decomposition_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.OMinimalAbstract.cell_decomposition_mem

/-! ### PolySignPartition (TS-QE, TS-1) — the univariate sign partition -/

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.poly_sign_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.poly_sign_constant

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.family_sign_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.family_sign_partition

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.family_sign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.family_sign_eq

/-! ### PolyBranchTrees (TS-QE, TS-2a) — the parametric branch machinery -/

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.spec_eval_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.spec_eval_cons

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.resolve_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.resolve_spec

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.spec_natDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.spec_natDegree_eq

/-! ### PseudoRemainder (TS-QE, TS-2b) — pseudo-division and the sign transfer -/

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.pseudoModExp_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.pseudoModExp_identity

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.emod_eval_at_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.emod_eval_at_root

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.sign_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.sign_transfer

/-! ### PolyDerivZones (TS-QE, TS-2c) — between-roots signs via monotonicity -/

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.spec_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.spec_derivative

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.strictMonoOn_sign_zones' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.strictMonoOn_sign_zones

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.deriv_free_sign_zones' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.deriv_free_sign_zones

/-! ### SignDiagrams (TS-QE, TS-2d-1) — the summit's base camp -/

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.exists_diagram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.exists_diagram

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.elim_of_diagramPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.elim_of_diagramPartition

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.diagramPartition_of_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.diagramPartition_of_constants

/-! ### DiagramNormalize (TS-QE, TS-2d-2a) — padding removal -/

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.dropPadding_paddingFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.dropPadding_paddingFree

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.realizes_dropPadding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.realizes_dropPadding

set_option linter.style.longLine false in
/-- info: 'Sundog.TarskiQE.realizes_samples_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Sundog.TarskiQE.realizes_samples_root
