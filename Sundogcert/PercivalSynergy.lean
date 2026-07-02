/-
# PercivalSynergy -- the richer-joint witness: the edge formula is a floor (ME-5)

OR-4 sheathed the Blackwell repair because in the binary-symmetric CI cell the
write-price is expressed exactly by the reliability-edge formula
`max(beta, rho) - beta`.  This module unsheathes the repair's motivating case:
a joint where the formula UNDERSTATES the price maximally.

**The synergy joint:** `G = V xor U` with `V, U` uniform.  Machine-checked:

* `xor_vonly_half` / `xor_uonly_half` -- each single channel is individually
  WORTHLESS: every V-only policy and every U-only policy has competence exactly
  `1/2` (chance).  So the reliability-edge formula reads
  `max(1/2, 1/2) - 1/2 = 0`.
* `xor_full_attains` -- the XOR policy collects `1`: the two channels are
  jointly perfect.
* `xor_invariant_le_half` -- the collapse at the target safe point: every
  do(U)-invariant policy is capped at `1/2` (the factoring lemma
  `dou_invariant_factors` is model-independent and reused as-is).
* `synergy_edge_formula_fails` -- the package: the write-price
  (unconstrained optimum minus safe-point ceiling) is `1 - 1/2 = 1/2` while the
  edge formula reads `0`.

Together with the general two-line monotonicity fact (price = value(V,U) -
value(V) >= value(U) - value(V), and >= 0), recorded in the ME-5 receipt: **the
CI cell is the FLOOR -- richer joints only make enforcing the edge condition
MORE expensive than the reliability-edge formula says.  The price survives as
the value gap (a local Blackwell deficiency); the edge FORMULA was a CI
artifact.**

Scope, honest: one explicit joint over the Bool cell; deterministic policies;
the general price-vs-deficiency landscape is the computed sweep's job
(`scripts/orderrelative-me5-priced-quadrant.mjs`), not this module's.
-/
import Sundogcert.PercivalTargetCollapse

namespace Sundogcert.Percival

/-- Competence under an arbitrary 8-cell joint `w g v u` (the probability that
the policy's guess equals `G`), as the explicit sum. -/
def compJ (w : Bool → Bool → Bool → ℚ) (π : Bool → Bool → Bool) : ℚ :=
  w true true true * (if π true true = true then 1 else 0)
    + w true true false * (if π true false = true then 1 else 0)
    + w true false true * (if π false true = true then 1 else 0)
    + w true false false * (if π false false = true then 1 else 0)
    + w false true true * (if π true true = false then 1 else 0)
    + w false true false * (if π true false = false then 1 else 0)
    + w false false true * (if π false true = false then 1 else 0)
    + w false false false * (if π false false = false then 1 else 0)

/-- The synergy joint: `G = V xor U`, `V, U` uniform -- each channel alone is
independent of `G`; together they determine it. -/
def xorJoint (g v u : Bool) : ℚ :=
  if g = xor v u then 1/4 else 0

/-- **Every V-only policy is at chance on the synergy joint.** -/
theorem xor_vonly_half (f : Bool → Bool) :
    compJ xorJoint (fun v _ => f v) = 1/2 := by
  cases hft : f true <;> cases hff : f false <;>
    simp [compJ, xorJoint, hft, hff] <;> norm_num

/-- **Every U-only policy is at chance on the synergy joint.** -/
theorem xor_uonly_half (f : Bool → Bool) :
    compJ xorJoint (fun _ u => f u) = 1/2 := by
  cases hft : f true <;> cases hff : f false <;>
    simp [compJ, xorJoint, hft, hff] <;> norm_num

/-- **The XOR policy collects everything.** -/
theorem xor_full_attains : compJ xorJoint (fun v u => xor v u) = 1 := by
  simp [compJ, xorJoint]
  norm_num

/-- **The collapse at the synergy joint:** every do(U)-invariant policy is
capped at chance (the model-independent factoring + `xor_vonly_half`). -/
theorem xor_invariant_le_half {π : Bool → Bool → Bool} (h : DoUInvariant π) :
    compJ xorJoint π ≤ 1/2 := by
  obtain ⟨f, hf⟩ := dou_invariant_factors h
  have : compJ xorJoint π = compJ xorJoint (fun v _ => f v) := by
    simp only [compJ, hf]
  rw [this, xor_vonly_half]

/--
**The edge formula fails on synergy; the price survives (the ME-5 witness).**
On the XOR joint: both single channels are worthless (the reliability-edge
formula reads `max(1/2,1/2) - 1/2 = 0`), the unconstrained optimum collects
`1`, and every policy at the target safe point is capped at `1/2` -- the
write-price is `1/2`, not `0`.  The CI formula was a floor, not the law.
-/
theorem synergy_edge_formula_fails :
    (∀ f : Bool → Bool, compJ xorJoint (fun v _ => f v) = 1/2)
    ∧ (∀ f : Bool → Bool, compJ xorJoint (fun _ u => f u) = 1/2)
    ∧ compJ xorJoint (fun v u => xor v u) = 1
    ∧ (∀ π, DoUInvariant π → compJ xorJoint π + 1/2 ≤ compJ xorJoint (fun v u => xor v u)) := by
  refine ⟨xor_vonly_half, xor_uonly_half, xor_full_attains, fun π h => ?_⟩
  rw [xor_full_attains]
  have := xor_invariant_le_half h
  linarith

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.xor_vonly_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xor_vonly_half

/-- info: 'Sundogcert.Percival.xor_uonly_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xor_uonly_half

/-- info: 'Sundogcert.Percival.xor_full_attains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xor_full_attains

/-- info: 'Sundogcert.Percival.xor_invariant_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xor_invariant_le_half

/-- info: 'Sundogcert.Percival.synergy_edge_formula_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms synergy_edge_formula_fails

end Sundogcert.Percival
