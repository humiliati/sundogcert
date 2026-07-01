/-
# OrderRelative — the radical axis as a FULL instance (the `ℝˣ/ℚˣ` quotient model)

The grading abstraction (`OrderRelativeGrading`) made the cohomological axis a literal instance of
`orderOf_prod_eq_lcm` but left the radical axis "connected by note": its order was defined by the
bespoke predicate `RadicalReaches x k := ∃ m ∈ [1,k], x^m ∈ ℚ`, and the docstring *asserted* this is
"the order of `[x]` in `ℝˣ/ℚˣ`" without building that group. This module builds it.

- **The group** `RadGroup = ℝˣ ⧸ ℚˣ`: the rational units `ratSub` are given an explicit carrier
  `{u | ∃ q : ℚ, (q:ℝ) = u}`, so membership *is* the rationality condition; `ℝˣ` is abelian so the
  subgroup is normal.
- **The bridge** (`radicalReaches_iff`): `RadicalReaches x k ↔ ∃ m ∈ [1,k], (rad x)^m = 1` for
  `x ≠ 0` — the docstring claim, now machine-checked. (Stated as the `∃ m ∈ [1,k]` predicate, not
  `orderOf ≤ k`, since `orderOf = 0` encodes infinite order — the convention `RadicalReaches` uses.)
- **The full instance** (`radical_compose`): the radical order is join-homomorphic under the
  coproduct `RadGroup × RadGroup` — one line from `orderOf_prod_eq_lcm`. The radical axis is now a
  literal instance, exactly like the cohomological one.
-/
import Sundogcert.OrderRelativeGrading
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Sundog.OrderRelative.RadicalQuotient

open Sundog.OrderRelative

/-- The rational units inside `ℝˣ`, as a subgroup with explicit carrier (membership *is*
rationality of the value). -/
def ratSub : Subgroup ℝˣ where
  carrier := {u | ∃ q : ℚ, (q : ℝ) = (u : ℝ)}
  one_mem' := ⟨1, by norm_num⟩
  mul_mem' := by
    rintro a b ⟨qa, ha⟩ ⟨qb, hb⟩
    exact ⟨qa * qb, by rw [Units.val_mul, ← ha, ← hb, Rat.cast_mul]⟩
  inv_mem' := by
    rintro a ⟨q, hq⟩
    exact ⟨q⁻¹, by rw [Rat.cast_inv, hq, ← Units.val_inv_eq_inv_val]⟩

/-- Membership in the rational subgroup *is* the rationality of the value. -/
theorem mem_ratSub {u : ℝˣ} : u ∈ ratSub ↔ ∃ q : ℚ, (q : ℝ) = (u : ℝ) := Iff.rfl

/-- `ℝˣ` is abelian, so the rational subgroup is normal. -/
instance : ratSub.Normal :=
  ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [h]; exact hn⟩

/-- The radical-order group `ℝˣ / ℚˣ`. -/
abbrev RadGroup := ℝˣ ⧸ ratSub

/-- The class of a nonzero real in `ℝˣ / ℚˣ`. -/
noncomputable def rad (x : ℝ) (hx : x ≠ 0) : RadGroup := QuotientGroup.mk (Units.mk0 x hx)

/-- **The bridge, one exponent.** `[x]^m = 1` in `ℝˣ/ℚˣ` iff `x^m` is rational. -/
theorem rad_pow_eq_one_iff (x : ℝ) (hx : x ≠ 0) (m : ℕ) :
    (rad x hx) ^ m = 1 ↔ ∃ q : ℚ, x ^ m = (q : ℝ) := by
  have hval : (((Units.mk0 x hx) ^ m : ℝˣ) : ℝ) = x ^ m := by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  have e : (rad x hx) ^ m = QuotientGroup.mk ((Units.mk0 x hx) ^ m) :=
    (map_pow (QuotientGroup.mk' ratSub) (Units.mk0 x hx) m).symm
  rw [e, QuotientGroup.eq_one_iff, mem_ratSub, hval]
  exact ⟨fun ⟨q, h⟩ => ⟨q, h.symm⟩, fun ⟨q, h⟩ => ⟨q, h.symm⟩⟩

/-- **The bridge (the promoted docstring claim).** The radical-reach order of a nonzero real is the
order of its class in `ℝˣ / ℚˣ`: `RadicalReaches x k ↔ ∃ m ∈ [1,k], (rad x)^m = 1`. -/
theorem radicalReaches_iff (x : ℝ) (hx : x ≠ 0) (k : ℕ) :
    RadicalReaches x k ↔ ∃ m, 1 ≤ m ∧ m ≤ k ∧ (rad x hx) ^ m = 1 := by
  refine exists_congr fun m => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [rad_pow_eq_one_iff]

/-- **The radical axis as a full instance.** Its order is join-homomorphic under the coproduct
`RadGroup × RadGroup` — one line from the abstract grading law `orderOf_prod_eq_lcm`. -/
theorem radical_compose (u v : ℝˣ) :
    orderOf ((QuotientGroup.mk u, QuotientGroup.mk v) : RadGroup × RadGroup)
      = Nat.lcm (orderOf (QuotientGroup.mk u : RadGroup)) (orderOf (QuotientGroup.mk v : RadGroup)) :=
  Grading.orderOf_prod_eq_lcm _ _

end Sundog.OrderRelative.RadicalQuotient
