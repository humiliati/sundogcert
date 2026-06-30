/-
# OrderRelative — a third determine rung (order 3): the ladder climbs

The graded exactness order ([OrderRelativeApproxGraded]) has `id` at order 1 and `ReLU` at order 2.
This adds the third rung: `step2 x = ReLU x + ReLU (x-1)` — two breakpoints (at `0` and `1`), three
affine pieces (slopes `0, 1, 2`), so **exactness-order exactly 3**. The determine side genuinely
climbs `1 < 2 < 3` with explicit witnesses, not just two isolated points.

The lower bound (`¬ HasPieceCover step2 2`) is a clean two-interval pigeonhole: the disjoint windows
around `0` and `1` each need a cut, but a 2-piece cover has only one. (The general `k`-breakpoint
family `Σ ReLU(x-i)` at order `k+1` is the natural extrapolation — same shape, a `k`-fold
pigeonhole.)
-/
import Sundogcert.OrderRelativeApproxGraded

namespace Sundog.OrderRelative.ApproxLadder

open Sundog.OrderRelative Sundog.PieceCover Sundog.OrderRelative.ApproxGraded

/-- `step2 x = ReLU x + ReLU (x-1)` — two breakpoints, three pieces. -/
def step2 : ℝ → ℝ := fun x => max x 0 + max (x - 1) 0

theorem step2_neg {x : ℝ} (h : x ≤ 0) : step2 x = 0 := by
  show max x 0 + max (x - 1) 0 = 0
  rw [max_eq_right h, max_eq_right (by linarith)]; ring

theorem step2_mid {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : step2 x = x := by
  show max x 0 + max (x - 1) 0 = x
  rw [max_eq_left h0, max_eq_right (by linarith)]; ring

theorem step2_pos {x : ℝ} (h : 1 ≤ x) : step2 x = 2 * x - 1 := by
  show max x 0 + max (x - 1) 0 = 2 * x - 1
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring

/-- `step2` is affine on every interval whose interior avoids `{0, 1}` (three regions). -/
theorem step2_affineAway : AffineAway step2 {0, 1} := by
  intro a b _ hmiss
  have h0 : (0 : ℝ) ∉ Set.Ioo a b := hmiss 0 (by simp)
  have h1 : (1 : ℝ) ∉ Set.Ioo a b := hmiss 1 (by simp)
  simp only [Set.mem_Ioo, not_and_or, not_lt] at h0 h1
  rcases h0 with ha0 | hb0
  · rcases h1 with ha1 | hb1
    · exact ⟨2, -1, fun x hx => by rw [step2_pos (le_trans ha1 hx.1)]; ring⟩
    · exact ⟨1, 0, fun x hx => by rw [step2_mid (le_trans ha0 hx.1) (le_trans hx.2 hb1)]; ring⟩
  · exact ⟨0, 0, fun x hx => by rw [step2_neg (le_trans hx.2 hb0)]; ring⟩

/-- `step2` is not covered by 2 affine pieces: the disjoint windows around `0` and `1` each need a
cut, but a 2-piece cover supplies only one. -/
theorem step2_not_pieceCover_two : ¬ HasPieceCover step2 2 := by
  rintro ⟨S, hcard, haff⟩
  by_cases hA : ∃ s ∈ S, s ∈ Set.Ioo (-1/2 : ℝ) (1/2)
  · obtain ⟨s0, hs0S, hs0⟩ := hA
    by_cases hB : ∃ s ∈ S, s ∈ Set.Ioo (1/2 : ℝ) (3/2)
    · obtain ⟨s1, hs1S, hs1⟩ := hB
      have hne : s0 ≠ s1 := ne_of_lt (by linarith [hs0.2, hs1.1])
      have : 1 < S.card := Finset.one_lt_card.mpr ⟨s0, hs0S, s1, hs1S, hne⟩
      omega
    · push_neg at hB
      obtain ⟨p, q, hpq⟩ := haff (1/2) (3/2) (by norm_num) hB
      have e1 := hpq (1/2) (by constructor <;> norm_num)
      have e2 := hpq 1 (by constructor <;> norm_num)
      have e3 := hpq (3/2) (by constructor <;> norm_num)
      rw [step2_mid (by norm_num) (by norm_num)] at e1
      rw [step2_pos (by norm_num)] at e2
      rw [step2_pos (by norm_num)] at e3
      nlinarith [e1, e2, e3]
  · push_neg at hA
    obtain ⟨p, q, hpq⟩ := haff (-1/2) (1/2) (by norm_num) hA
    have e1 := hpq (-1/2) (by constructor <;> norm_num)
    have e2 := hpq 0 (by constructor <;> norm_num)
    have e3 := hpq (1/2) (by constructor <;> norm_num)
    rw [step2_neg (by norm_num)] at e1
    rw [step2_neg (by norm_num)] at e2
    rw [step2_mid (by norm_num) (by norm_num)] at e3
    nlinarith [e1, e2, e3]

/-- `step2` is covered by `k` affine pieces iff `3 ≤ k` (two breakpoints). -/
theorem step2_hasPieceCover_iff (k : ℕ) : HasPieceCover step2 k ↔ 3 ≤ k := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    exact step2_not_pieceCover_two (hasPieceCover_mono_le h (by omega))
  · intro hk
    refine hasPieceCover_mono_le ⟨{0, 1}, ?_, step2_affineAway⟩ hk
    rw [Finset.card_pair (show (0:ℝ) ≠ 1 by norm_num)]

/-- **DETERMINE, order 3: `step2`** — three affine pieces. -/
def step2_pieceProblem : Problem where
  Target := Unit
  ord _ := 3
  Resolves k _ := HasPieceCover step2 k
  resolves_iff k _ := by rw [step2_hasPieceCover_iff]; exact_mod_cast Iff.rfl

/-- **The determine ladder climbs: `1 < 2 < 3`** — `id`, `ReLU`, `step2`, explicit witnesses at each
exactness-order. -/
theorem ladder3 :
    id_pieceProblem.ord () = 1 ∧ relu_pieceProblem.ord () = 2 ∧ step2_pieceProblem.ord () = 3 :=
  ⟨rfl, rfl, rfl⟩

end Sundog.OrderRelative.ApproxLadder
