/-
# Percival -- finite court-separation anchor

This module pins the B1 "court coordination" result to the smallest useful
finite model.  Three base-support points are ordered by increasing courting
pressure:

* `r0`: low courting pressure,
* `r1`: middle courting pressure,
* `r2`: high courting pressure.

The upper-tail quantilizer family keeps the high-courting tail.  For a
nonincreasing court reward (`r0 >= r1 >= r2`), the full base distribution
(`q = 1`) weakly dominates the stricter upper tails.  If the whole base support
is beyond the court cliff, all three base rewards are zero; an un-targeted point
at zero courting with positive reward strictly beats the entire quantilizer
family.

The point is intentionally modest: this is a finite/discrete anchor for the
conditional separation, not a provenance theorem about whether a real base
distribution lies past the cliff.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival

/-! ## Three-point upper-tail quantilizers -/

/-- The `q = 1` member: the full base average over three support points. -/
def baseAvg3 (r0 r1 r2 : ℚ) : ℚ :=
  (r0 + r1 + r2) / 3

/-- The two-point upper-tail member: keep the middle and high courting points. -/
def upperTail2Avg (r1 r2 : ℚ) : ℚ :=
  (r1 + r2) / 2

/-- The one-point upper-tail member: keep only the highest courting point. -/
def upperTail1Avg (r2 : ℚ) : ℚ :=
  r2

/--
The one-point high-courting tail cannot beat the full base average when reward is
nonincreasing along the courting coordinate.
-/
theorem upper_tail_one_le_baseAvg3 {r0 r1 r2 : ℚ}
    (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) :
    upperTail1Avg r2 ≤ baseAvg3 r0 r1 r2 := by
  unfold upperTail1Avg baseAvg3
  linarith

/--
The two-point high-courting tail cannot beat the full base average when reward is
nonincreasing along the courting coordinate.
-/
theorem upper_tail_two_le_baseAvg3 {r0 r1 r2 : ℚ}
    (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) :
    upperTail2Avg r1 r2 ≤ baseAvg3 r0 r1 r2 := by
  unfold upperTail2Avg baseAvg3
  linarith

/--
**Best quantilizer is `q = 1`, finite anchor.**  In the three-point upper-tail
family, if court reward is nonincreasing in courting pressure, neither stricter
tail improves on the raw base distribution.
-/
theorem best_quantilizer_is_base_three {r0 r1 r2 : ℚ}
    (h01 : r1 ≤ r0) (h12 : r2 ≤ r1) :
    upperTail1Avg r2 ≤ baseAvg3 r0 r1 r2 ∧
      upperTail2Avg r1 r2 ≤ baseAvg3 r0 r1 r2 ∧
        baseAvg3 r0 r1 r2 ≤ baseAvg3 r0 r1 r2 := by
  exact
    ⟨upper_tail_one_le_baseAvg3 h01 h12,
      upper_tail_two_le_baseAvg3 h01 h12,
      le_rfl⟩

/-! ## Clean support-above separation -/

/--
**Clean support-above separation, finite anchor.**  If every base-support point is
past the court cliff, every upper-tail quantilizer collects zero; any un-targeted
policy with positive court reward strictly beats the whole family.  The finite
maximum is the discrete version of `sup_q Rbar(q) = 0 < R(0)`.
-/
theorem clean_support_above_separation_three {untargeted : ℚ}
    (hpos : 0 < untargeted) :
    max (upperTail1Avg 0)
        (max (upperTail2Avg 0 0) (baseAvg3 0 0 0)) < untargeted := by
  simp [upperTail1Avg, upperTail2Avg, baseAvg3, hpos]

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.best_quantilizer_is_base_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms best_quantilizer_is_base_three

/-- info: 'Sundogcert.Percival.clean_support_above_separation_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clean_support_above_separation_three

end Sundogcert.Percival
