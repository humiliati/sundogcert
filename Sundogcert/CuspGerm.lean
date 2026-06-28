import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Sundogcert.ContextDecay

/-!
# Cusp germ grounding — the cubic realizes a `ContextDecay` annihilation (H-II)

`ContextDecay` pins what a fold-pair annihilation *receipt* licenses on the abstract
fold-count family (`List ℕ`). This module grounds that abstraction in the actual
catastrophe germ, the way `AgenticTrace.decisive_*` is grounded in the RS
`agree`/`Polynomial` structure: it shows the canonical fold-catastrophe score curve

  `f_a(x) = x³ − a·x`

really does produce the abstract drop-by-two. Its folds (interior extrema) are the
critical points — the real roots of the derivative `f_a'(x) = 3x² − a`:

  * `a > 0` → two critical points `±√(a/3)` (a genuine fold pair: a max and a min);
  * `a < 0` → none (`3x² − a > 0` everywhere, the curve is monotone).

So as the control `a` crosses zero the fold count drops `2 → 0` — exactly a
`ContextDecay.Decays` event. The cusp point `a = 0` itself is the degenerate
annihilation locus (the pair has merged into an inflection); the annihilation is
witnessed strictly between `a₁ > 0` and `a₀ < 0`, so we never lean on `a = 0`.

This grounds, but does not subsume, the named imported wall: it formalizes that the
*germ* realizes the abstract rule. It does not claim a vector memory *is* this germ —
that mapping remains the import.
-/

namespace Sundog.CuspGerm

open Sundog.ContextDecay

/-- Critical points of the cusp-germ score curve `f_a(x) = x³ − a·x`: the reals where
the derivative `3x² − a` vanishes. Away from the cusp point `a = 0` these are exactly
the folds (strict interior extrema) of `f_a`. -/
def critSet (a : ℝ) : Set ℝ := {x | 3 * x ^ 2 - a = 0}

/-- The fold count of the cubic germ at parameter `a` (number of critical points). -/
noncomputable def critCount (a : ℝ) : ℕ := (critSet a).ncard

theorem mem_critSet {a x : ℝ} : x ∈ critSet a ↔ 3 * x ^ 2 - a = 0 := Iff.rfl

/-- For `a < 0` the germ is **fold-free**: `3x² − a > 0` everywhere, no critical
points — the monotone, `accept` side of the annihilation. -/
theorem critSet_neg {a : ℝ} (ha : a < 0) : critSet a = ∅ := by
  ext x
  simp only [mem_critSet, Set.mem_empty_iff_false, iff_false]
  intro hx
  nlinarith [sq_nonneg x]

theorem critCount_neg {a : ℝ} (ha : a < 0) : critCount a = 0 := by
  unfold critCount
  rw [critSet_neg ha, Set.ncard_empty]

/-- For `a > 0` the germ has a **fold pair**: the two critical points `±√(a/3)`. -/
theorem critSet_pos {a : ℝ} (ha : 0 < a) :
    critSet a = {Real.sqrt (a / 3), -Real.sqrt (a / 3)} := by
  have h3 : (0 : ℝ) ≤ a / 3 := by positivity
  set r := Real.sqrt (a / 3) with hr
  have hr2 : r ^ 2 = a / 3 := Real.sq_sqrt h3
  ext x
  simp only [mem_critSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hx2 : x ^ 2 = r ^ 2 := by rw [hr2]; linarith
    have hfac : (x - r) * (x + r) = 0 := by linear_combination hx2
    rcases mul_eq_zero.mp hfac with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> linear_combination 3 * hr2

theorem critCount_pos {a : ℝ} (ha : 0 < a) : critCount a = 2 := by
  unfold critCount
  rw [critSet_pos ha]
  have hr_pos : 0 < Real.sqrt (a / 3) := Real.sqrt_pos.mpr (by positivity)
  have hne : Real.sqrt (a / 3) ≠ -Real.sqrt (a / 3) := by
    intro h; linarith [hr_pos]
  exact Set.ncard_pair hne

/-- **Grounding — the cusp germ realizes a `ContextDecay` annihilation.** For any
`a₀ < 0 < a₁`, the fold-count family `[critCount a₁, critCount a₀] = [2, 0]` is a
`ContextDecay.Decays` event: the canonical fold-catastrophe germ produces exactly the
abstract drop-by-two the quarantine rule keys on, so the abstract rule is not vacuous.
This is the analog of grounding `decisive_*` in the RS `agree`/`Polynomial` structure. -/
theorem cubic_realizes_annihilation {a₀ a₁ : ℝ} (h0 : a₀ < 0) (h1 : 0 < a₁) :
    Decays [critCount a₁, critCount a₀] := by
  rw [critCount_pos h1, critCount_neg h0]
  exact ⟨[], 2, 0, [], rfl, rfl⟩

/-- Read through the `ContextDecay` headline: the germ's fold-count family exhibits a
genuine fold pair (≥ 2 folds) annihilating. -/
theorem cubic_foldpair_witness {a₀ a₁ : ℝ} (h0 : a₀ < 0) (h1 : 0 < a₁) :
    ∃ l a b r, [critCount a₁, critCount a₀] = l ++ a :: b :: r ∧ 2 ≤ a ∧ a = b + 2 :=
  decays_iff_foldpair.mp (cubic_realizes_annihilation h0 h1)

end Sundog.CuspGerm

-- Axiom audit (real-analysis germ ⇒ expect the full foundational triple).
#print axioms Sundog.CuspGerm.critCount_neg
#print axioms Sundog.CuspGerm.critCount_pos
#print axioms Sundog.CuspGerm.cubic_realizes_annihilation
#print axioms Sundog.CuspGerm.cubic_foldpair_witness
