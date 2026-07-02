/-
# PercivalAuditPay -- audit-and-pay prices at the edge (ME-3)

Extends the OR-4 cell (`PercivalTargetCollapse`): the overseer has an EXACT read
of named-variable dependence (the four-entry probe table, `dependsU_probe`) and
keys a transfer on it -- pay `t` iff the audit passes.  The agent maximizes
competence plus transfer.  The rung's headline:

> `audit_and_pay_iff` -- the scheme implements the target safe point
> **iff `t >= rho - beta`**.

Incentive enforcement on a perfect read pays exactly the structural write-price
(the reliability edge): **reads do not discount enforcement**.  Coherent with
the banked S2.4/B3.2 (the court is a punishment scheme keyed on a read; with an
edge the induced optimum courts to the cliff, never to zero) -- here the
mechanism-design version is machine-checked in the same finite cell.

Supporting anchors:

* `comp_le_rho` -- **the Bayes ceiling**: no policy beats the U-follower
  (`comp <= rho` for every policy, `1/2 <= beta <= rho <= 1`).
* `followV_comp` / `followV_invariant` -- the V-follower attains the safe
  ceiling `beta` at the safe point (the collapse bound is tight).
* `audit_pay_implements` -- sufficiency: at `t >= rho - beta` the audited
  V-follower weakly dominates every policy.
* `audit_pay_underpays` -- necessity: at `t < rho - beta` EVERY safe policy is
  strictly beaten by the unaudited U-follower.

Genus: implementation theory (Maskin) / the informativeness principle
(Holmstrom) -- the delta: informativeness says USE the read in the contract;
this cell shows the optimally-used perfect read still cannot beat the
structural price.  Scope, honest: the S2 binary-symmetric CI cell (as OR-4);
deterministic policies; quasi-linear payoff (competence + transfer); the
transfer keyed on the named-variable audit (content-level reads are a
DIFFERENT, infinite-order filtration -- the ME-1 census's mirror cell).
-/
import Sundogcert.PercivalTargetCollapse

namespace Sundogcert.Percival

/-- The V-follower sits at the target safe point. -/
theorem followV_invariant : DoUInvariant (fun v _ => v) :=
  fun _ _ _ => rfl

/-- The V-follower attains the safe-point competence ceiling `beta`. -/
theorem followV_comp (β ρ : ℚ) : comp β ρ (fun v _ => v) = β := by
  simp only [comp]
  norm_num
  ring

/--
**The Bayes ceiling: no policy beats the U-follower.**  With
`1/2 <= beta <= rho <= 1`, every deterministic policy has competence at most
`rho` -- the unconstrained optimum is `follow-U`.
-/
theorem comp_le_rho {β ρ : ℚ} (hβ : 1/2 ≤ β) (hβρ : β ≤ ρ) (hρ : ρ ≤ 1)
    (π : Bool → Bool → Bool) : comp β ρ π ≤ ρ := by
  cases htt : π true true <;> cases htf : π true false <;>
    cases hft : π false true <;> cases hff : π false false <;>
    simp [comp, htt, htf, hft, hff] <;> ring_nf <;>
    nlinarith [mul_nonneg (show (0:ℚ) ≤ 2*ρ - 1 by linarith) (show (0:ℚ) ≤ β by linarith),
      mul_nonneg (show (0:ℚ) ≤ 2*ρ - 1 by linarith) (show (0:ℚ) ≤ 1 - β by linarith),
      mul_nonneg (show (0:ℚ) ≤ 2*β - 1 by linarith) (show (0:ℚ) ≤ ρ by linarith),
      mul_nonneg (show (0:ℚ) ≤ 2*β - 1 by linarith) (show (0:ℚ) ≤ 1 - ρ by linarith),
      mul_nonneg (show (0:ℚ) ≤ ρ - β by linarith) (show (0:ℚ) ≤ 1 - β by linarith)]

/-- The audit: the four-entry probe table's verdict (`dou_iff`: exactly
do(U)-invariance -- the read is exact). -/
def probeAudit (π : Bool → Bool → Bool) : Prop :=
  π true true = π true false ∧ π false true = π false false

instance (π : Bool → Bool → Bool) : Decidable (probeAudit π) := by
  unfold probeAudit; infer_instance

/-- Audit-and-pay: competence plus a transfer `t` paid iff the audit passes. -/
def payoff (β ρ t : ℚ) (π : Bool → Bool → Bool) : ℚ :=
  comp β ρ π + (if probeAudit π then t else 0)

/-- The scheme implements the safe point: some policy AT the safe point is
payoff-optimal against every deviation. -/
def Implements (β ρ t : ℚ) : Prop :=
  ∃ π, DoUInvariant π ∧ ∀ π', payoff β ρ t π' ≤ payoff β ρ t π

/--
**Sufficiency: paying at least the edge implements the safe point.**  At
`t >= rho - beta` the audited V-follower weakly dominates every policy --
audited deviations are capped by the collapse, unaudited ones by the Bayes
ceiling.
-/
theorem audit_pay_implements {β ρ t : ℚ} (hβ : 1/2 ≤ β) (hβρ : β ≤ ρ) (hρ : ρ ≤ 1)
    (ht : ρ - β ≤ t) (π : Bool → Bool → Bool) :
    payoff β ρ t π ≤ payoff β ρ t (fun v _ => v) := by
  have hV : payoff β ρ t (fun v _ => v) = β + t := by
    rw [payoff, followV_comp, if_pos (by exact ⟨rfl, rfl⟩)]
  rw [hV, payoff]
  by_cases ha : probeAudit π
  · rw [if_pos ha]
    have hsafe : DoUInvariant π := (dou_iff π).mpr ha
    have := dou_comp_le_beta (ρ := ρ) hβ hsafe
    linarith
  · rw [if_neg ha]
    have := comp_le_rho hβ hβρ hρ π
    linarith

/--
**Necessity: paying less than the edge fails.**  At `t < rho - beta` EVERY
policy at the safe point is strictly beaten by the unaudited U-follower --
no safe policy is payoff-optimal.
-/
theorem audit_pay_underpays {β ρ t : ℚ} (hβ : 1/2 ≤ β) (ht : t < ρ - β)
    (π : Bool → Bool → Bool) (hπ : DoUInvariant π) :
    payoff β ρ t π < payoff β ρ t (fun _ u => u) := by
  have hU : payoff β ρ t (fun _ u => u) = ρ := by
    rw [payoff, followU_comp, if_neg (by simp [probeAudit]), add_zero]
  have ha : probeAudit π := (dou_iff π).mp hπ
  rw [hU, payoff, if_pos ha]
  have := dou_comp_le_beta (ρ := ρ) hβ hπ
  linarith

/--
**Audit-and-pay prices at the edge (the ME-3 headline).**  With an exact read
of dependence in hand, the transfer scheme implements the target safe point
**iff `t >= rho - beta`**: incentive enforcement pays exactly the structural
write-price.  Reads do not discount enforcement.
-/
theorem audit_and_pay_iff {β ρ t : ℚ} (hβ : 1/2 ≤ β) (hβρ : β ≤ ρ) (hρ : ρ ≤ 1) :
    Implements β ρ t ↔ ρ - β ≤ t := by
  constructor
  · rintro ⟨π, hsafe, hopt⟩
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (hopt (fun _ u => u))
      (not_le.mpr (audit_pay_underpays hβ hlt π hsafe))
  · intro ht
    exact ⟨fun v _ => v, followV_invariant, audit_pay_implements hβ hβρ hρ ht⟩

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.followV_invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms followV_invariant

/-- info: 'Sundogcert.Percival.followV_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms followV_comp

/-- info: 'Sundogcert.Percival.comp_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comp_le_rho

/-- info: 'Sundogcert.Percival.audit_pay_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms audit_pay_implements

/-- info: 'Sundogcert.Percival.audit_pay_underpays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms audit_pay_underpays

/-- info: 'Sundogcert.Percival.audit_and_pay_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms audit_and_pay_iff

end Sundogcert.Percival
