/-
# PercivalTargetCollapse -- the write-side infinity cell (OR-4)

Machine-checks S2's 2x2x2 collapse anchor in the OR-3 bridge idiom: the target
channel's safe point (`c = 0` = do(U)-invariance) is READABLE by finitely many
interventional probes but every write reaching it pays the reliability edge --
the `MEASURABLE != ENFORCEABLE` witness as one Lean statement.

The model is S2's binary-symmetric CI joint, exactly: ground truth `G` uniform
on `Bool`; legit channel `V` with `P(V = G) = beta`; proxy `U` with
`P(U = G) = rho`; `V, U` conditionally independent given `G`.  A policy is
`pi : V -> U -> Bool`; competence is `P(pi(V,U) = G)`, written as the explicit
eight-cell rational sum (`comp`).

* `dou_invariant_factors` -- do(U)-invariance factors the policy through `V`
  (the `IsSufficient`-idiom face of "in-channel target enforcement collapses
  to masking").
* `dou_comp_le_beta` -- **the collapse**: every do(U)-invariant policy has
  competence <= beta (only the V-follower attains it; S2.1/S2.2).
* `followU_comp` -- the U-follower collects exactly rho.
* `target_write_resists` -- **the priced write**: every policy at the target
  safe point sits at least `rho - beta` below the U-optimum -- the reliability
  edge `max(beta,rho) - beta`, carried EXACTLY by the finite cell.
* `dependsU_probe` -- **the read side**: named-variable proxy-dependence is
  decided by the four-entry interventional probe table (two comparisons) --
  sigma_read is finite, order <= 4 probes.
* `measurable_ne_enforceable` -- the packaged witness: dependence readable by
  probes AND the safe point writable only at the edge's price.

**Blackwell repair disposition (pre-registered in OR-4): SHEATHED.**  The
falsifier was "bare factorization cannot express the price term"; in the finite
cell the price IS expressed exactly (`followU_comp` minus the collapse ceiling
= `rho - beta`), so the enrichment to the Blackwell order is not needed at this
tier.  It stays pre-registered for richer joints, where S2's own
binary-symmetric caveat lives.

Scope, honest: the binary-symmetric CI joint (S2's caveat inherited);
named-variable dependence only (S2.3's content-level split is not modeled);
single-agent; exact rational probabilities, no dynamics.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival

/-- do(U)-invariance: the action is unchanged under every intervention on the
proxy input -- the target channel's safe point (`c = 0`), named-variable form. -/
def DoUInvariant (π : Bool → Bool → Bool) : Prop :=
  ∀ v u u', π v u = π v u'

/-- Interventional proxy-dependence (named-variable `c > 0`). -/
def DependsU (π : Bool → Bool → Bool) : Prop :=
  ¬ DoUInvariant π

/-- Competence `P(pi(V,U) = G)` in the S2 model, as the explicit eight-cell sum:
`G` uniform, `P(V = G) = beta`, `P(U = G) = rho`, conditional independence. -/
def comp (β ρ : ℚ) (π : Bool → Bool → Bool) : ℚ :=
  (1/2) * β * ρ * (if π true true = true then 1 else 0)
    + (1/2) * β * (1 - ρ) * (if π true false = true then 1 else 0)
    + (1/2) * (1 - β) * ρ * (if π false true = true then 1 else 0)
    + (1/2) * (1 - β) * (1 - ρ) * (if π false false = true then 1 else 0)
    + (1/2) * β * ρ * (if π false false = false then 1 else 0)
    + (1/2) * β * (1 - ρ) * (if π false true = false then 1 else 0)
    + (1/2) * (1 - β) * ρ * (if π true false = false then 1 else 0)
    + (1/2) * (1 - β) * (1 - ρ) * (if π true true = false then 1 else 0)

/--
**do(U)-invariance factors through `V`.**  A policy at the target safe point is
a function of the legit channel alone -- the `IsSufficient`-idiom face of the
S2 collapse: in-channel target enforcement is behaviorally a `V`-only policy.
-/
theorem dou_invariant_factors {π : Bool → Bool → Bool} (h : DoUInvariant π) :
    ∃ f : Bool → Bool, ∀ v u, π v u = f v :=
  ⟨fun v => π v true, fun v u => h v u true⟩

/--
**The collapse: every do(U)-invariant policy has competence at most `beta`.**
Only the canonical V-follower attains it; the `rho - beta` gap above is
unreachable at the safe point (S2.1/S2.2, the data-processing bound).
-/
theorem dou_comp_le_beta {β ρ : ℚ} (hβ : 1/2 ≤ β) {π : Bool → Bool → Bool}
    (h : DoUInvariant π) : comp β ρ π ≤ β := by
  obtain ⟨f, hf⟩ := dou_invariant_factors h
  simp only [comp, hf]
  cases hft : f true <;> cases hff : f false <;>
    simp [hft, hff] <;> ring_nf <;> linarith

/-- The U-follower collects exactly `rho`. -/
theorem followU_comp (β ρ : ℚ) : comp β ρ (fun _ u => u) = ρ := by
  simp only [comp]
  norm_num
  ring

/--
**The priced write (the write-side infinity cell).**  Every policy at the
target safe point sits at least `rho - beta` below the U-optimum: the
reliability edge, carried exactly by the finite cell.  (Meaningful when
`beta < rho`; stated for all `rho`.)
-/
theorem target_write_resists {β ρ : ℚ} (hβ : 1/2 ≤ β) {π : Bool → Bool → Bool}
    (h : DoUInvariant π) :
    comp β ρ π + (ρ - β) ≤ comp β ρ (fun _ u => u) := by
  rw [followU_comp]
  have := dou_comp_le_beta (ρ := ρ) hβ h
  linarith

/-- do(U)-invariance is decided by two probe comparisons. -/
theorem dou_iff (π : Bool → Bool → Bool) :
    DoUInvariant π ↔ π true true = π true false ∧ π false true = π false false := by
  constructor
  · intro h
    exact ⟨h true true false, h false true false⟩
  · rintro ⟨h1, h2⟩ v u u'
    cases v <;> cases u <;> cases u' <;> simp [h1, h2]

/--
**The read side: proxy-dependence is decided by the four-entry interventional
probe table.**  Named-variable `c > 0` holds iff one of two probe comparisons
fires -- `sigma_read` is finite (at most four interventional evaluations).
-/
theorem dependsU_probe (π : Bool → Bool → Bool) :
    DependsU π ↔ π true true ≠ π true false ∨ π false true ≠ π false false := by
  rw [DependsU, dou_iff, not_and_or]

/--
**MEASURABLE != ENFORCEABLE, packaged (the OR-3 witness as one statement).**
In the S2 cell with a genuine reliability edge (`beta < rho`): proxy-dependence
is readable by the finite probe table, and every write reaching the target safe
point pays at least the edge.
-/
theorem measurable_ne_enforceable {β ρ : ℚ} (hβ : 1/2 ≤ β) (hρ : β < ρ) :
    (∀ π : Bool → Bool → Bool,
        DependsU π ↔ π true true ≠ π true false ∨ π false true ≠ π false false)
    ∧ (∀ π : Bool → Bool → Bool, DoUInvariant π →
        comp β ρ π + (ρ - β) ≤ comp β ρ (fun _ u => u))
    ∧ 0 < ρ - β :=
  ⟨dependsU_probe, fun _ h => target_write_resists hβ h, by linarith⟩

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.dou_invariant_factors' does not depend on any axioms -/
#guard_msgs in
#print axioms dou_invariant_factors

/-- info: 'Sundogcert.Percival.dou_comp_le_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dou_comp_le_beta

/-- info: 'Sundogcert.Percival.followU_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms followU_comp

/-- info: 'Sundogcert.Percival.target_write_resists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_write_resists

/-- info: 'Sundogcert.Percival.dependsU_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dependsU_probe

/-- info: 'Sundogcert.Percival.measurable_ne_enforceable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms measurable_ne_enforceable

end Sundogcert.Percival
