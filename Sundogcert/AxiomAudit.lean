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

To extend the gate: add the headline name of any new load-bearing theorem with its
own `#guard_msgs in #print axioms` block.

Note: `Sundogcert.ShadowDecayGeneral` is intentionally NOT imported/guarded here —
it is concurrent, owner-gated work.
-/
import Sundogcert.Certificate
import Sundogcert.Scaling
import Sundogcert.Looseness
import Sundogcert.Degradation
import Sundogcert.CheckCost
import Sundogcert.ShadowDecay
import Sundogcert.HaloGeometry
import Sundogcert.FaradayAB
import Sundogcert.CertWall

/-! ## Certificate — lossiness, accept/reject soundness, sound column-weight bound -/

/-- info: 'Sundog.Certificate.syndrome_independent_of_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.syndrome_independent_of_secret

/-- info: 'Sundog.Certificate.accept_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.accept_sound

/-- info: 'Sundog.Certificate.reject_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.reject_sound

/-- info: 'Sundog.Certificate.colWeightLb_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.colWeightLb_sound

/-- info: 'Sundog.Certificate.reject_sound_colweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.reject_sound_colweight

/-! ## Scaling — the projection-family scaling law -/

/-- info: 'Sundog.Certificate.Scaling.scaling_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.Scaling.scaling_law

/-! ## Looseness — basis-dependence collapse -/

/-- info: 'Sundog.Certificate.Looseness.looseness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.Looseness.looseness

/-! ## Degradation — the general column-weight ceiling -/

/-- info: 'Sundog.Certificate.Degradation.colWeightLb_le_card_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.Degradation.colWeightLb_le_card_div

/-! ## CheckCost — the linear check-cost theorem -/

/-- info: 'Sundog.Certificate.verifyCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.verifyCost_le

/-! ## ShadowDecay — Debye–Waller decay and discrete determination -/

/-- info: 'Sundog.ShadowDecay.debye_waller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.ShadowDecay.debye_waller

/-- info: 'Sundog.ShadowDecay.determination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.ShadowDecay.determination

/-! ## HaloGeometry — minimum-deviation stationarity and local minimum -/

/-- info: 'Sundog.HaloGeometry.min_deviation_stationary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.HaloGeometry.min_deviation_stationary

/-- info: 'Sundog.HaloGeometry.min_deviation_isLocalMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.HaloGeometry.min_deviation_isLocalMin

/-! ## FaradayAB — gauge-circulation invariance and loop = flux -/

/-- info: 'Sundog.FaradayAB.gauge_circulation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.FaradayAB.gauge_circulation_zero

/-- info: 'Sundog.FaradayAB.loop_integral_eq_flux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.FaradayAB.loop_integral_eq_flux

/-! ## CertWall — row-equivalence invariance, no-tight-robust bound, tight⇒decodes -/

/-- info: 'Sundog.Certificate.CertWall.minCosetWeight_rowEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.CertWall.minCosetWeight_rowEquiv

/--
info: 'Sundog.Certificate.CertWall.colWeightLb_cannot_be_tight_basisRobust' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Sundog.Certificate.CertWall.colWeightLb_cannot_be_tight_basisRobust

/-- info: 'Sundog.Certificate.CertWall.tight_bound_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Sundog.Certificate.CertWall.tight_bound_decodes
