/-
# OrderRelative — the search-reach negative, machine-checked (the boundary's other negative)

Completes the 2-negative side of the composition boundary. Search-reach is not join-homomorphic
under multiplication, and it fails by **inflating** (the opposite of algebraic-degree, which drops):
`½` has search-reach order 2 (least rational-denominator budget reaching it), but `½ · ½ = ¼` has
order 4 — the product order EXCEEDS the factor order, overshooting any join (`≤ max` would be 2).
-/
import Sundogcert.OrderRelative

namespace Sundog.OrderRelative.SearchNeg

/-- **The search-reach negative: not join-homomorphic under `×`, and it INFLATES.** `½` reaches at
budget 2, but the product `½ · ½ = ¼` does NOT reach at budget 2 (its least denominator is 4) — the
product order exceeds the factor order, overshooting any join. (Contrast algebraic-degree, which
falls *below* the join.) -/
theorem search_not_join_under_mul :
    DenomReaches (1/2 : ℝ) 2
      ∧ (1/2 : ℝ) * (1/2) = 1/4
      ∧ ¬ DenomReaches ((1/2 : ℝ) * (1/2)) 2 := by
  refine ⟨⟨1/2, by norm_num, by norm_num⟩, by norm_num, ?_⟩
  rw [show (1/2 : ℝ) * (1/2) = 1/4 by norm_num]
  rintro ⟨q, hden, hq⟩
  rw [show (1/4 : ℝ) = ((1/4 : ℚ) : ℝ) by norm_num] at hq
  have hq4 : q = 1/4 := by exact_mod_cast hq
  rw [hq4] at hden
  norm_num at hden

end Sundog.OrderRelative.SearchNeg
