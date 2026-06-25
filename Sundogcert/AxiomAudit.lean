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
import Sundogcert.AgenticTrace

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
