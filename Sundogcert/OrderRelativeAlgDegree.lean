/-
# OrderRelative — an algebraic-degree axis, and the BoxSEL optimum's mode-vector

A sixth instance family for the Order-Relative Resolution Law: the order is the **degree of the
minimal rational polynomial** with the target as a root: rational → 1, quadratic irrational → 2,
…, transcendental → `⊤`.

Its payoff is the mode-vector on the lane's *real* optimum. The value `(9+√17)/32` is a root of
`16 x² − 9 x + 1` (algebraic of degree 2) yet irrational, so its **algebraic-degree order is 2**
(finite) while its **search/denominator order is `⊤`**. One object, two divergent orders across
two grounded axes: degree-2-simple but denominator-unreachable — reachable by analysis, not by
naive search, machine-checked on the actual optimum.
-/
import Sundogcert.OrderRelative

namespace Sundog.OrderRelative.AlgDegree

open Sundog.OrderRelative Polynomial

/-- `x` is a root of a nonzero rational polynomial of degree `≤ k` (algebraic). -/
def AlgDegReaches (x : ℝ) (k : ℕ) : Prop :=
  ∃ p : ℚ[X], p ≠ 0 ∧ p.natDegree ≤ k ∧ (aeval x p : ℝ) = 0

/-- The BoxSEL optimum `(9 + √17)/32`. -/
noncomputable def boxOpt : ℝ := (9 + Real.sqrt 17) / 32

/-- The optimum is irrational: if `(9+√17)/32` were rational, so would `√17` be. -/
theorem boxOpt_irrational : Irrational boxOpt := by
  have hirr : Irrational (Real.sqrt 17) := by
    have h17 : Nat.Prime 17 := by norm_num
    simpa using h17.irrational_sqrt
  rintro ⟨q, hq⟩
  apply hirr
  refine ⟨32 * q - 9, ?_⟩
  have hq' : 32 * (q : ℝ) = 9 + Real.sqrt 17 := by
    rw [hq]; simp only [boxOpt]; ring
  push_cast
  linarith [hq']

/-- The optimum is a root of the rational quadratic `16 x² − 9 x + 1`. -/
theorem boxOpt_root : 16 * boxOpt ^ 2 - 9 * boxOpt + 1 = 0 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hid : 16 * boxOpt ^ 2 - 9 * boxOpt + 1 = (Real.sqrt 17 ^ 2 - 17) / 64 := by
    simp only [boxOpt]; ring
  rw [hid, hs]; norm_num

/-- The degree-2 witness polynomial `16 X² − 9 X + 1 ∈ ℚ[X]`. -/
noncomputable def witness : ℚ[X] := 16 * X ^ 2 - 9 * X + 1

theorem witness_aeval : (aeval boxOpt witness : ℝ) = 0 := by
  simp only [witness, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, aeval_X]
  exact boxOpt_root

theorem witness_natDegree : witness.natDegree = 2 := by
  unfold witness; compute_degree!

theorem witness_ne_zero : witness ≠ 0 := by
  intro h
  have hd := witness_natDegree
  rw [h, natDegree_zero] at hd
  omega

/-- **The optimum has algebraic-degree order exactly 2.** Reverse: `16X²−9X+1` realises it.
Forward: a nonzero rational polynomial of degree `≤ 1` with `boxOpt` as a root would make `boxOpt`
rational (degree-0 has no root; degree-1 has its root in `ℚ`), contradicting irrationality. -/
theorem algDegReaches_boxOpt_iff (k : ℕ) : AlgDegReaches boxOpt k ↔ 2 ≤ k := by
  constructor
  · rintro ⟨p, hp0, hdeg, hpr⟩
    by_contra hlt
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
    · apply boxOpt_irrational
      refine ⟨-p.coeff 0 / p.coeff 1, ?_⟩
      have hc1r : (p.coeff 1 : ℝ) ≠ 0 := by exact_mod_cast hc1
      push_cast
      field_simp
      linarith [hpr]
  · intro hk
    exact ⟨witness, witness_ne_zero, by rw [witness_natDegree]; omega, witness_aeval⟩

/-- **The algebraic-degree instance** for the optimum: order = 2. -/
noncomputable def algDegProblem : Problem where
  Target := Unit
  ord _ := 2
  Resolves k _ := AlgDegReaches boxOpt k
  resolves_iff k _ := by
    rw [algDegReaches_boxOpt_iff]
    exact_mod_cast Iff.rfl

/-- **The mode-vector on the real BoxSEL optimum.** `(9+√17)/32` carries two divergent orders
across two grounded axes: **algebraic-degree order 2** (a root of `16X²−9X+1`) yet
**search/denominator order `⊤`** (irrational). Degree-2-simple but denominator-unreachable —
reachable by analysis, not by naive search, on the lane's actual optimum. -/
theorem boxOpt_mode_vector :
    (irrationalReachProblem boxOpt boxOpt_irrational).ord () = ⊤
      ∧ algDegProblem.ord () = (2 : ℕ∞) :=
  ⟨rfl, rfl⟩

end Sundog.OrderRelative.AlgDegree
