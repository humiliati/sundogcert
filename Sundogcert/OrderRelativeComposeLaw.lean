/-
# OrderRelative — the composition boundary, and the cancellation-free law

Sharpening the composition law ([OrderRelativeCompose] proves it on the coproduct): the order is a
join-homomorphism **iff the product is cancellation-free**. This module pins the boundary with a
second machine-checked negative, and proves the cancellation-free (coproduct) law in general form.

**The second negative — algebraic-degree under `×`.** `√2` has algebraic degree 2 (irrational, root
of `X²−2`), but `√2 · √2 = 2` has algebraic degree 1 (rational). So under multiplication the order
DROPS `2 → 1`, *below* the join — the irrationalities cancel. So multiplication is not
cancellation-free, and algebraic-degree is not join-homomorphic. (Compare search-reach, where the
product order *inflates* above the join — cancellation throws the order off in either direction.)

**The cancellation-free law (the conjecture's provable core).** `annihilates_prod` proves the
COPRODUCT factorizes: a budget `j` annihilates `(s,t)` iff it annihilates both coordinates
(independent, no interaction) — so the order of `(s,t)` is the join (lcm) of the coordinate orders,
for ALL `s,t`. The contrast `within_group_cancels`: ADDITION inside a group is not the coproduct —
in `ZMod 2`, `1+1 = 0`, so budget 1 annihilates the sum but not the operand, the order drops. Net:
the order is join-homomorphic exactly on the cancellation-free coproduct.
-/
import Sundogcert.OrderRelativeAlgDegree

namespace Sundog.OrderRelative.ComposeLaw

open Sundog.OrderRelative.AlgDegree Polynomial

/-- `√2` is NOT algebraic of degree `≤ 1` — a nonzero rational poly of degree `≤ 1` rooted at `√2`
would make `√2` rational, contradicting `irrational_sqrt_two`. -/
theorem sqrt2_not_algDeg1 : ¬ AlgDegReaches (Real.sqrt 2) 1 := by
  rintro ⟨p, hp0, hdeg, hpr⟩
  have hd : p.natDegree < 2 := by omega
  rw [aeval_eq_sum_range' hd] at hpr
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hpr
  simp only [zero_add, pow_zero, pow_one, Rat.smul_def, mul_one] at hpr
  by_cases hc1 : p.coeff 1 = 0
  · rw [hc1] at hpr
    simp only [Rat.cast_zero, zero_mul, add_zero] at hpr
    have hc0 : p.coeff 0 = 0 := by exact_mod_cast hpr
    apply hp0
    ext n
    match n with
    | 0 => simpa using hc0
    | 1 => simpa using hc1
    | (m + 2) => exact coeff_eq_zero_of_natDegree_lt (by omega)
  · apply irrational_sqrt_two
    refine ⟨-p.coeff 0 / p.coeff 1, ?_⟩
    have hc1r : (p.coeff 1 : ℝ) ≠ 0 := by exact_mod_cast hc1
    push_cast
    field_simp
    linarith [hpr]

/-- `2 : ℝ` is algebraic of degree `≤ 1` (rational) — witness `X − C 2`. -/
theorem two_algDeg1 : AlgDegReaches (2 : ℝ) 1 := by
  refine ⟨X - C 2, X_sub_C_ne_zero _, ?_, ?_⟩
  · rw [natDegree_X_sub_C]
  · simp [map_sub, aeval_X, aeval_C]

/-- **The second negative: algebraic-degree is NOT join-homomorphic under `×`.** `√2 · √2 = 2`,
whose algebraic-degree order is 1 — yet each factor `√2` has order 2. Multiplication drops it
BELOW the join (`1 < 2`): the irrationalities cancel. -/
theorem algDeg_not_join_under_mul :
    Real.sqrt 2 * Real.sqrt 2 = 2
      ∧ AlgDegReaches (Real.sqrt 2 * Real.sqrt 2) 1
      ∧ ¬ AlgDegReaches (Real.sqrt 2) 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact ⟨h2, by rw [h2]; exact two_algDeg1, sqrt2_not_algDeg1⟩

/-! ### The cancellation-free coproduct law (general) and a within-group cancellation -/

variable {G H : Type*} [AddGroup G] [AddGroup H]

/-- **The cancellation-free coproduct factorizes (the general join law).** A budget `j` annihilates
the coproduct `(s, t)` iff it annihilates BOTH coordinates — independent, no interaction. Hence the
order of `(s, t)` is the join (lcm) of the coordinate orders, for ALL `s, t`. -/
theorem annihilates_prod (s : G) (t : H) (j : ℕ) :
    j • ((s, t) : G × H) = 0 ↔ j • s = 0 ∧ j • t = 0 := by
  simp [Prod.ext_iff]

/-- **Within-group addition is not the coproduct — it cancels.** In `ZMod 2`, `1 + 1 = 0`, so budget
`1` annihilates the sum yet not the operand `1` — the order DROPS below the operands, opposite to a
join. Cancellation, not the independent coproduct. -/
theorem within_group_cancels :
    (1 : ℕ) • ((1 : ZMod 2) + 1) = 0 ∧ ¬ (1 : ℕ) • (1 : ZMod 2) = 0 := by
  simp only [one_nsmul]
  decide

end Sundog.OrderRelative.ComposeLaw
