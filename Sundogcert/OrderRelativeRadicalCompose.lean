/-
# OrderRelative — the radical axis is the multiplicative twin of cohomological (third positive)

The radical-reach order of `x` is the least `m` with `xᵐ ∈ ℚ` — equivalently the order of `[x]` in
the multiplicative quotient group `ℝˣ/ℚˣ`. So radical-reach is a **group-order axis**, the
multiplicative twin of the cohomological (additive-order) axis. Like cohomological, it is
join-homomorphic on the **coproduct** (independent generators) and cancels within the group.

- **Coproduct join (general): `mul_annihilates_prod`** — the multiplicative twin of
  `ComposeLaw.annihilates_prod`: `(x,y)ʲ = 1 ↔ xʲ = 1 ∧ yʲ = 1`. Independent radical classes (e.g.
  `√2, √3`, whose product `√6` keeps order 2 = `lcm(2,2)`) compose by the join.
- **Within-group cancellation: `radical_cancel_sqrt2`** — `√2` has radical order 2, but the
  dependent product `√2 · √2 = 2` has radical order 1: the order DROPS below the join, like
  `1 + 1 = 0` in `ZMod 2`.

This sharpens the boundary characterization: **the join-homomorphic axes are exactly the group-order
axes** (cohomological additive, radical multiplicative); the non-group axes (algebraic-degree under
`×`, search-reach) are the negatives.
-/
import Sundogcert.OrderRelative

namespace Sundog.OrderRelative.RadicalCompose

open Sundog.OrderRelative

/-- **The multiplicative coproduct factorizes (the radical axis's join law).** Multiplicative twin
of `ComposeLaw.annihilates_prod`: `(x, y) ^ j = 1 ↔ x ^ j = 1 ∧ y ^ j = 1`, for all `x, y` in any
two groups. The radical-reach order is the order of `[x]` in `ℝˣ/ℚˣ`, so its coproduct (independent
surds) factorizes the same way — radical is the multiplicative twin of the cohomological axis. -/
theorem mul_annihilates_prod {G H : Type*} [Group G] [Group H] (x : G) (y : H) (j : ℕ) :
    (x, y) ^ j = 1 ↔ x ^ j = 1 ∧ y ^ j = 1 := by
  simp [Prod.ext_iff]

/-- **Within-group cancellation in the radical group.** `√2` has radical order 2, but the dependent
product `√2 · √2 = 2` has radical order 1 — multiplying dependent surds cancels (the order drops
below the join), exactly as `1 + 1 = 0` cancels in `ZMod 2`. The coproduct (independent surds) does
not cancel: that is the positive half (`mul_annihilates_prod`). -/
theorem radical_cancel_sqrt2 :
    Real.sqrt 2 * Real.sqrt 2 = 2
      ∧ RadicalReaches (2 : ℝ) 1
      ∧ ¬ RadicalReaches (Real.sqrt 2) 1 := by
  refine ⟨Real.mul_self_sqrt (by norm_num), ⟨1, le_refl 1, le_refl 1, 2, by norm_num⟩, ?_⟩
  rintro ⟨m, hm1, hm1', q, hq⟩
  interval_cases m
  simp only [pow_one] at hq
  exact (irrational_sqrt_two ⟨q, hq.symm⟩).elim

end Sundog.OrderRelative.RadicalCompose
