/-
# PercivalGeneral -- general court-separation anchors (S4)

Generalizes the finite 3-point anchors in `Sundogcert/Percival.lean` to arbitrary
finite support. The base is an unweighted list of court rewards listed in
NONINCREASING order along the courting coordinate (lowest courting first, so the
upper courting tail is a suffix `l.drop k`). The `q`-quantilizer family takes upper
courting tails; un-targeting sits at zero courting.

Main results:

* `upper_tail_mul_le_base_mul` -- cross-multiplied: no upper tail beats the full
  base average when reward is nonincreasing in courting (best quantilizer is the
  untilted base, general form).
* `best_quantilizer_is_base_general` -- the same in average/division form.
* `clean_support_above_separation_general` -- if every base-support reward is zero
  (the whole support is past the court cliff), every tail average is strictly
  beaten by any positive un-targeted reward.

Scope, honest: unweighted lists = uniform base weights. The weighted/continuous
forms are computed receipts (`scripts/percival-s4-counterproductivity-general.mjs`
in the sundog repo); the court dynamics that make the hypotheses apply live in the
computed models, not here.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival

/-- Every element of `t` is at most `h`, so the sum is at most `length * h`. -/
private theorem sum_le_length_mul {h : ℚ} :
    ∀ (t : List ℚ), (∀ x ∈ t, x ≤ h) → t.sum ≤ (t.length : ℚ) * h := by
  intro t
  induction t with
  | nil => intro _; simp
  | cons x xs ih =>
    intro hb
    have hx : x ≤ h := hb x (List.mem_cons_self ..)
    have ihh := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons]
    push_cast
    nlinarith [hx, ihh]

/--
Cross-sum double counting: if every element of `d` is dominated by every element
of `t`, then `d.sum * t.length ≤ t.sum * d.length`.
-/
private theorem cross_sum_le :
    ∀ (t d : List ℚ), (∀ a ∈ t, ∀ b ∈ d, b ≤ a) →
      d.sum * (t.length : ℚ) ≤ t.sum * ((d.length : ℚ)) := by
  intro t
  induction t with
  | nil => intro d _; simp
  | cons a t ih =>
    intro d hc
    have ha : ∀ b ∈ d, b ≤ a := hc a (List.mem_cons_self ..)
    have iht := ih d (fun x hx b hb => hc x (List.mem_cons_of_mem _ hx) b hb)
    have hda : d.sum ≤ (d.length : ℚ) * a := sum_le_length_mul d ha
    simp only [List.sum_cons, List.length_cons]
    push_cast
    nlinarith [iht, hda]

/--
**Best quantilizer is the base -- general, cross-multiplied.** For a court reward
listed nonincreasing along the courting order, no upper courting tail (`l.drop k`)
beats the full base on average: `tailSum * baseLen ≤ baseSum * tailLen`.
-/
theorem upper_tail_mul_le_base_mul (l : List ℚ) (hl : l.Pairwise (· ≥ ·)) (k : ℕ) :
    (l.drop k).sum * (l.length : ℚ) ≤ l.sum * ((l.drop k).length : ℚ) := by
  have hsplit : l.take k ++ l.drop k = l := List.take_append_drop k l
  have hpw : List.Pairwise (· ≥ ·) (l.take k ++ l.drop k) := by
    rw [hsplit]; exact hl
  rw [List.pairwise_append] at hpw
  have hcross : ∀ a ∈ l.take k, ∀ b ∈ l.drop k, b ≤ a :=
    fun a ha b hb => hpw.2.2 a ha b hb
  have key := cross_sum_le (l.take k) (l.drop k) hcross
  have hlenN : (l.take k).length + (l.drop k).length = l.length := by
    rw [← List.length_append, hsplit]
  have hsumQ : (l.take k).sum + (l.drop k).sum = l.sum := by
    rw [← List.sum_append, hsplit]
  have hlenQ : ((l.take k).length : ℚ) + ((l.drop k).length : ℚ) = (l.length : ℚ) := by
    exact_mod_cast hlenN
  rw [← hsumQ, ← hlenQ]
  nlinarith [key]

/--
**Best quantilizer is the base -- general, average form.** No nonempty upper
courting tail has a higher average court reward than the untilted base.
-/
theorem best_quantilizer_is_base_general (l : List ℚ) (hl : l.Pairwise (· ≥ ·)) (k : ℕ)
    (hne : l.drop k ≠ []) :
    (l.drop k).sum / ((l.drop k).length : ℚ) ≤ l.sum / (l.length : ℚ) := by
  have hdpos : (0 : ℚ) < ((l.drop k).length : ℚ) := by
    exact_mod_cast List.length_pos_of_ne_nil hne
  have hlne : l ≠ [] := fun h => hne (by simp [h])
  have hlpos : (0 : ℚ) < (l.length : ℚ) := by
    exact_mod_cast List.length_pos_of_ne_nil hlne
  rw [div_le_div_iff₀ hdpos hlpos]
  exact upper_tail_mul_le_base_mul l hl k

/--
**Clean support-above separation -- general.** If every base-support reward is
zero (the whole support is past the court cliff), every upper-tail quantilizer
average is `0`, strictly below any positive un-targeted reward. (Holds for the
empty tail too, since `0 / 0 = 0` in `ℚ`.)
-/
theorem clean_support_above_separation_general (l : List ℚ) (hzero : ∀ r ∈ l, r = 0)
    {untargeted : ℚ} (hpos : 0 < untargeted) (k : ℕ) :
    (l.drop k).sum / ((l.drop k).length : ℚ) < untargeted := by
  have hz : (l.drop k).sum = 0 :=
    List.sum_eq_zero fun x hx => hzero x (List.mem_of_mem_drop hx)
  rw [hz, zero_div]
  exact hpos

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.upper_tail_mul_le_base_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upper_tail_mul_le_base_mul

/-- info: 'Sundogcert.Percival.best_quantilizer_is_base_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms best_quantilizer_is_base_general

/-- info: 'Sundogcert.Percival.clean_support_above_separation_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clean_support_above_separation_general

end Sundogcert.Percival
