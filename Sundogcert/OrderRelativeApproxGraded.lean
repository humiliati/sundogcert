/-
# OrderRelative — the approximation axis, GRADED, and a second resist witness

Two continuations of the approximation axis ([OrderRelativeApprox]).

**Graded exactness order.** Instead of the binary "is it a net?", grade by **piece count**:
`ord f =` the least `k` with `HasPieceCover f k` (`f` covered by `≤ k` affine pieces), `⊤` if none.
This is genuinely graded — `id` has order 1 (one affine piece), `ReLU` has order 2 (one breakpoint),
`x²` has order `⊤` (no finite cover). So the determine side is a real ladder `1 < 2 < ⋯`, not a flat
"finite", with the same earned resist pole on top.

**Second resist witness.** `eˣ` joins `x²` on the resist pole — a *transcendental* function, not a
polynomial, showing the resist is generic to curvature, not special to `x²`. `exp_no_pieceCover` is
earned by strict convexity (`strictConvexOn_exp`): on any gap interval `eˣ` would be affine, but
strict convexity makes the midpoint value strictly below the chord.
-/
import Sundogcert.OrderRelativeApprox
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Sundog.OrderRelative.ApproxGraded

open Sundog.OrderRelative Sundog.PieceCover Sundog.ExactRepr Sundog.CircuitNet Sundog.RegionCount
open Sundog.OrderRelative.Approx

/-! ### Graded by piece count -/

/-- `id` is covered by `k` affine pieces iff `1 ≤ k` (it is a single affine piece). -/
theorem id_hasPieceCover_iff (k : ℕ) : HasPieceCover (fun x : ℝ => x) k ↔ 1 ≤ k := by
  constructor
  · rintro ⟨S, hcard, _⟩; omega
  · intro hk
    exact ⟨∅, by simpa using hk, fun a b _ _ => ⟨1, 0, fun x _ => by ring⟩⟩

/-- **DETERMINE, order 1: `id`** — a single affine piece. -/
def id_pieceProblem : Problem where
  Target := Unit
  ord _ := 1
  Resolves k _ := HasPieceCover (fun x : ℝ => x) k
  resolves_iff k _ := by rw [id_hasPieceCover_iff]; exact_mod_cast Iff.rfl

/-- The ReLU function `max x 0`. -/
def relu : ℝ → ℝ := fun x => max x 0

/-- `ReLU` is not a single affine piece (it bends at `0`). -/
theorem relu_not_affine : ¬ AffineAway relu ∅ := by
  rintro h
  obtain ⟨p, q, hpq⟩ := h (-1) 1 (by norm_num) (by simp)
  have e1 : relu (-1) = p * (-1) + q := hpq (-1) (Set.mem_Icc.mpr ⟨le_refl _, by norm_num⟩)
  have e2 : relu 0 = p * 0 + q := hpq 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have e3 : relu 1 = p * 1 + q := hpq 1 (Set.mem_Icc.mpr ⟨by norm_num, le_refl _⟩)
  rw [show relu (-1) = 0 from max_eq_right (by norm_num)] at e1
  rw [show relu 0 = 0 from max_self 0] at e2
  rw [show relu 1 = 1 from max_eq_left (by norm_num)] at e3
  nlinarith [e1, e2, e3]

/-- `ReLU` is affine on every interval whose interior avoids `0`. -/
theorem relu_affineAway : AffineAway relu {0} := by
  intro a b _ hmiss
  have h0 : (0 : ℝ) ∉ Set.Ioo a b := hmiss 0 (by simp)
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at h0
  rcases h0 with ha | hb
  · exact ⟨1, 0, fun x hx => by
      have : 0 ≤ x := le_trans ha hx.1
      show max x 0 = 1 * x + 0; rw [max_eq_left this]; ring⟩
  · exact ⟨0, 0, fun x hx => by
      have : x ≤ 0 := le_trans hx.2 hb
      show max x 0 = 0 * x + 0; rw [max_eq_right this]; ring⟩

/-- `ReLU` is covered by `k` affine pieces iff `2 ≤ k` (one breakpoint). -/
theorem relu_hasPieceCover_iff (k : ℕ) : HasPieceCover relu k ↔ 2 ≤ k := by
  constructor
  · rintro ⟨S, hcard, haff⟩
    by_contra hlt
    rw [not_le] at hlt
    interval_cases k
    · omega
    · have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [hS] at haff; exact relu_not_affine haff
  · intro hk
    exact hasPieceCover_mono_le ⟨{0}, by simp, relu_affineAway⟩ hk

/-- **DETERMINE, order 2: `ReLU`** — two affine pieces. -/
def relu_pieceProblem : Problem where
  Target := Unit
  ord _ := 2
  Resolves k _ := HasPieceCover relu k
  resolves_iff k _ := by rw [relu_hasPieceCover_iff]; exact_mod_cast Iff.rfl

/-- **The exactness order is GRADED.** `id` order 1, `ReLU` order 2, `x²` order `⊤` (no cover) — a
real ladder `1 < 2 < ⊤`, not a flat "finite vs ⊤". -/
theorem graded_exactness :
    id_pieceProblem.ord () = 1 ∧ relu_pieceProblem.ord () = 2
      ∧ ¬ ∃ k, HasPieceCover (fun x : ℝ => x ^ 2) k :=
  ⟨rfl, rfl, sq_no_pieceCover⟩

/-! ### A second resist witness: `eˣ` (transcendental) -/

/-- **`eˣ` has no finite piece cover** — the second earned resist pole, transcendental. Any finite
cut set leaves a gap interval where `eˣ` would be affine, but strict convexity puts the midpoint
strictly below the chord. -/
theorem exp_no_pieceCover : ¬ ∃ k, HasPieceCover Real.exp k := by
  rintro ⟨k, S, _, hAff⟩
  obtain ⟨M, hM⟩ := S.bddAbove
  have hmiss : ∀ s ∈ S, s ∉ Set.Ioo (M + 1) (M + 2) := by
    intro s hs hsio
    exact absurd hsio.1 (by have := hM (Finset.mem_coe.mpr hs); linarith)
  obtain ⟨p, q, hpq⟩ := hAff (M + 1) (M + 2) (by linarith) hmiss
  have e1 : Real.exp (M + 1) = p * (M + 1) + q :=
    hpq (M + 1) (Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩)
  have e2 : Real.exp (M + 2) = p * (M + 2) + q :=
    hpq (M + 2) (Set.mem_Icc.mpr ⟨by linarith, le_refl _⟩)
  have e3 : Real.exp (M + 3 / 2) = p * (M + 3 / 2) + q :=
    hpq (M + 3 / 2) (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (M + 1)) (Set.mem_univ (M + 2))
    (ne_of_lt (by linarith)) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at hconv
  rw [show (1/2) * (M + 1) + (1/2) * (M + 2) = M + 3 / 2 from by ring] at hconv
  rw [e1, e2, e3] at hconv
  nlinarith [hconv]

/-- **`eˣ` is not exactly any ReLU net** — the second resist, transcendental. -/
theorem exp_not_exactly_net : ¬ ExactlyNet Real.exp := by
  rintro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := net_hasPieceCover g
  rw [hg] at hk
  exact exp_no_pieceCover ⟨k, hk⟩

end Sundog.OrderRelative.ApproxGraded
