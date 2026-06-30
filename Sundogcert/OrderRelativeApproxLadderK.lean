/-
# OrderRelative — the general k-breakpoint determine rung (order k+1)

Generalizes the ladder (`id` 1, `ReLU` 2, `step2` 3) to all `k`:
`sumRelu k = Σ_{i<k} ReLU(x-(i+1))` has `k` breakpoints (at `1,…,k`), `k+1` affine pieces
(slopes `0,1,…,k`), so **exactness-order exactly k+1**. The determine side is an unbounded ladder.

- **Upper** (`sumRelu_hasPieceCover`): cut set `{1,…,k}` (card `k`), via `AffineAway` additivity
  (`affineAway_add`) folded over the sum.
- **Lower** (`sumRelu_not_pieceCover`): a `k`-fold pigeonhole — the disjoint windows around each
  breakpoint each force a cut (`sumRelu` bends there, `sumRelu_bend`, a one-term second
  difference), so any cover needs `≥ k` cuts, i.e. `≥ k+1` pieces.
-/
import Sundogcert.OrderRelativeApproxGraded

namespace Sundog.OrderRelative.ApproxLadderK

open Sundog.OrderRelative Sundog.PieceCover

/-- `Σ_{i<k} ReLU(x - (i+1))` — `k` breakpoints at `1, …, k`. -/
noncomputable def sumRelu (k : ℕ) : ℝ → ℝ := fun x => ∑ i ∈ Finset.range k, max (x - (i + 1 : ℝ)) 0

/-- `AffineAway` is closed under addition: cuts unite. -/
theorem affineAway_add {f g : ℝ → ℝ} {S T : Finset ℝ}
    (hf : AffineAway f S) (hg : AffineAway g T) :
    AffineAway (fun x => f x + g x) (S ∪ T) := by
  intro a b hab hmiss
  obtain ⟨pf, qf, hpf⟩ := hf a b hab (fun s hs => hmiss s (Finset.mem_union_left T hs))
  obtain ⟨pg, qg, hpg⟩ := hg a b hab (fun s hs => hmiss s (Finset.mem_union_right S hs))
  exact ⟨pf + pg, qf + qg, fun x hx => by
    change f x + g x = (pf + pg) * x + (qf + qg)
    rw [hpf x hx, hpg x hx]; ring⟩

/-- A single shifted ReLU is affine off its breakpoint `c`. -/
theorem relu_shift_affineAway (c : ℝ) : AffineAway (fun x => max (x - c) 0) {c} := by
  intro a b _ hmiss
  have hc : c ∉ Set.Ioo a b := hmiss c (by simp)
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hc
  rcases hc with ha | hb
  · exact ⟨1, -c, fun x hx => by
      have : 0 ≤ x - c := by have := hx.1; linarith
      show max (x - c) 0 = 1 * x + -c; rw [max_eq_left this]; ring⟩
  · exact ⟨0, 0, fun x hx => by
      have : x - c ≤ 0 := by have := hx.2; linarith
      show max (x - c) 0 = 0 * x + 0; rw [max_eq_right this]; ring⟩

/-- `sumRelu k` is affine off `{1, …, k}`. -/
theorem sumRelu_affineAway (k : ℕ) :
    AffineAway (sumRelu k) ((Finset.range k).image (fun i : ℕ => (i : ℝ) + 1)) := by
  induction k with
  | zero => intro a b _ _; exact ⟨0, 0, fun x _ => by simp [sumRelu]⟩
  | succ k ih =>
    have hsplit : sumRelu (k + 1) = fun x => sumRelu k x + max (x - ((k : ℝ) + 1)) 0 := by
      funext x; simp [sumRelu, Finset.sum_range_succ]
    have hset : (Finset.range (k + 1)).image (fun i : ℕ => (i : ℝ) + 1)
        = (Finset.range k).image (fun i : ℕ => (i : ℝ) + 1) ∪ {(k : ℝ) + 1} := by
      rw [Finset.range_add_one, Finset.image_insert, Finset.insert_eq, Finset.union_comm]
    rw [hsplit, hset]
    exact affineAway_add ih (relu_shift_affineAway ((k : ℝ) + 1))

/-- **Upper bound: `sumRelu k` is covered by `k+1` affine pieces.** -/
theorem sumRelu_hasPieceCover (k : ℕ) : HasPieceCover (sumRelu k) (k + 1) := by
  refine ⟨(Finset.range k).image (fun i : ℕ => (i : ℝ) + 1), ?_, sumRelu_affineAway k⟩
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

/-- `sumRelu k` **bends** at each integer breakpoint `j ∈ {1,…,k}`: the second difference (spacing
`1/2`) is `1/2 ≠ 0`. It is a *one-term* sum — only the `j`-th ReLU is crossed. -/
theorem sumRelu_bend {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    sumRelu k ((j : ℝ) + 1/2) + sumRelu k ((j : ℝ) - 1/2) - 2 * sumRelu k (j : ℝ) = 1/2 := by
  have hcombine : sumRelu k ((j : ℝ) + 1/2) + sumRelu k ((j : ℝ) - 1/2) - 2 * sumRelu k (j : ℝ)
      = ∑ i ∈ Finset.range k,
          (max (((j : ℝ) + 1/2) - ((i : ℝ) + 1)) 0 + max (((j : ℝ) - 1/2) - ((i : ℝ) + 1)) 0
            - 2 * max ((j : ℝ) - ((i : ℝ) + 1)) 0) := by
    simp only [sumRelu, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hmem : (j - 1) ∈ Finset.range k := Finset.mem_range.2 (by omega)
  have hother : ∀ i ∈ Finset.range k, i ≠ j - 1 →
      (max (((j : ℝ) + 1/2) - ((i : ℝ) + 1)) 0 + max (((j : ℝ) - 1/2) - ((i : ℝ) + 1)) 0
        - 2 * max ((j : ℝ) - ((i : ℝ) + 1)) 0) = 0 := by
    intro i _ hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hreal : (i : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast (show i + 2 ≤ j by omega)
      rw [max_eq_left (show (0:ℝ) ≤ ((j : ℝ) + 1/2) - ((i : ℝ) + 1) by linarith),
          max_eq_left (show (0:ℝ) ≤ ((j : ℝ) - 1/2) - ((i : ℝ) + 1) by linarith),
          max_eq_left (show (0:ℝ) ≤ (j : ℝ) - ((i : ℝ) + 1) by linarith)]
      ring
    · have hreal : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j ≤ i by omega)
      rw [max_eq_right (show ((j : ℝ) + 1/2) - ((i : ℝ) + 1) ≤ 0 by linarith),
          max_eq_right (show ((j : ℝ) - 1/2) - ((i : ℝ) + 1) ≤ 0 by linarith),
          max_eq_right (show (j : ℝ) - ((i : ℝ) + 1) ≤ 0 by linarith)]
      ring
  rw [hcombine, Finset.sum_eq_single_of_mem (j - 1) hmem hother]
  have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by rw [Nat.cast_sub hj]; push_cast; ring
  rw [hcast,
      max_eq_left (show (0:ℝ) ≤ ((j : ℝ) + 1/2) - (j : ℝ) by linarith),
      max_eq_right (show ((j : ℝ) - 1/2) - (j : ℝ) ≤ 0 by linarith),
      max_eq_right (show (j : ℝ) - (j : ℝ) ≤ 0 by linarith)]
  ring

/-- **Lower bound: `k` cuts are forced.** The disjoint windows `(j-½, j+½)` around the `k`
breakpoints each meet any cover's cut set (`sumRelu` bends there), so it has `≥ k` cuts — i.e.
`≥ k+1` pieces. A `k`-fold pigeonhole (`InjOn` over `{1,…,k}`). -/
theorem sumRelu_not_pieceCover {k : ℕ} (hk : 1 ≤ k) : ¬ HasPieceCover (sumRelu k) k := by
  rintro ⟨S, hcard, haff⟩
  have key : ∀ j ∈ Finset.Icc 1 k, ∃ s ∈ S, s ∈ Set.Ioo ((j : ℝ) - 1/2) ((j : ℝ) + 1/2) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    by_contra hno
    push_neg at hno
    have hle : (j : ℝ) - 1/2 ≤ (j : ℝ) + 1/2 := by linarith
    obtain ⟨p, q, hpq⟩ := haff ((j : ℝ) - 1/2) ((j : ℝ) + 1/2) hle hno
    have h1 := hpq ((j : ℝ) - 1/2) (Set.mem_Icc.2 ⟨le_refl _, by linarith⟩)
    have h2 := hpq (j : ℝ) (Set.mem_Icc.2 ⟨by linarith, by linarith⟩)
    have h3 := hpq ((j : ℝ) + 1/2) (Set.mem_Icc.2 ⟨by linarith, le_refl _⟩)
    have hbend := sumRelu_bend hj.1 hj.2
    rw [h1, h2, h3] at hbend
    have hzero : (p * ((j : ℝ) + 1/2) + q) + (p * ((j : ℝ) - 1/2) + q) - 2 * (p * (j : ℝ) + q)
        = 0 := by ring
    linarith [hbend, hzero]
  classical
  let g : ℕ → ℝ := fun j => if hj : j ∈ Finset.Icc 1 k then (key j hj).choose else 0
  have hgS : ∀ j ∈ Finset.Icc 1 k, g j ∈ S := by
    intro j hj
    have hgj : g j = (key j hj).choose := dif_pos hj
    rw [hgj]; exact (key j hj).choose_spec.1
  have hgW : ∀ j ∈ Finset.Icc 1 k, g j ∈ Set.Ioo ((j : ℝ) - 1/2) ((j : ℝ) + 1/2) := by
    intro j hj
    have hgj : g j = (key j hj).choose := dif_pos hj
    rw [hgj]; exact (key j hj).choose_spec.2
  have hinj : Set.InjOn g (Finset.Icc 1 k) := by
    intro a ha b hb hab
    have ha' := Finset.mem_coe.1 ha
    have hb' := Finset.mem_coe.1 hb
    by_contra hne
    have hwa := hgW a ha'
    have hwb := hgW b hb'
    rw [Set.mem_Ioo] at hwa hwb
    rw [hab] at hwa
    rcases Nat.lt_or_ge a b with h | h
    · have : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (show a + 1 ≤ b by omega)
      linarith [hwa.2, hwb.1]
    · have : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast (show b + 1 ≤ a by omega)
      linarith [hwa.1, hwb.2]
  have hmaps : Set.MapsTo g ↑(Finset.Icc 1 k) ↑S :=
    fun x hx => Finset.mem_coe.2 (hgS x (Finset.mem_coe.1 hx))
  have hcardle := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Nat.card_Icc] at hcardle
  omega

/-- **`sumRelu k` has exactness-order exactly `k+1`** (for `k ≥ 1`). -/
theorem sumRelu_hasPieceCover_iff {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    HasPieceCover (sumRelu k) m ↔ k + 1 ≤ m := by
  constructor
  · intro h
    by_contra hlt
    exact sumRelu_not_pieceCover hk (hasPieceCover_mono_le h (by omega))
  · exact fun h => hasPieceCover_mono_le (sumRelu_hasPieceCover k) h

/-- The general-`k` determine rung as an Order-Relative `Problem` (order `k+1`). -/
def sumRelu_pieceProblem (k : ℕ) (hk : 1 ≤ k) : Problem where
  Target := Unit
  ord _ := ((k + 1 : ℕ) : ℕ∞)
  Resolves m _ := HasPieceCover (sumRelu k) m
  resolves_iff m _ := by rw [sumRelu_hasPieceCover_iff hk]; exact_mod_cast Iff.rfl

/-- **The determine side is an unbounded ladder.** Every `k ≥ 1` is realized: `sumRelu k` is covered
by `k+1` affine pieces but not by `k`, so its exactness-order is exactly `k+1`. The ladder
(`id` 1, `ReLU` 2, `step2` 3, …) climbs without bound. -/
theorem sumRelu_order_eq (k : ℕ) (hk : 1 ≤ k) :
    HasPieceCover (sumRelu k) (k + 1) ∧ ¬ HasPieceCover (sumRelu k) k :=
  ⟨sumRelu_hasPieceCover k, sumRelu_not_pieceCover hk⟩

/-- The order of the general-`k` rung is exactly `k+1`. -/
theorem ladderK (k : ℕ) (hk : 1 ≤ k) :
    (sumRelu_pieceProblem k hk).ord () = ((k + 1 : ℕ) : ℕ∞) := rfl

end Sundog.OrderRelative.ApproxLadderK
