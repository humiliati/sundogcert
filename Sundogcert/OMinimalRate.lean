/-
# O-min ladder R2-M + R2-Q: the monotonicity instance and the frontier modulus.

Rung 2 of the o-minimality ladder, on the rung-1 base (`OMinimalOne`).

**R2-M (monotonicity theorem, PL instance).** On every cut-free stretch a 1-D ReLU net is
monotone or antitone — the dimension-one Monotonicity Theorem instantiated on the semilinear
structure, with the cut budget carried explicitly (`S.card + 1 ≤ netPieceBound g`). Pure algebra
off `AffineAway` (an affine piece is monotone or antitone by the sign of its slope); no
derivatives. *Honest fence:* this is the per-stretch instance; the global decomposition into
maximal stretches is the normal-form module's business.

**R2-Q (the frontier modulus).** Rung 1 proved the level-set frontier *finite* by injecting it
into `S ∪ powerset S` — a `2^|S|` bound, fine for finiteness, vacuous as a rate. The sharpening:
the image of `x ↦ S.filter (· < x)` consists only of **initial segments**, which form a `⊆`-chain,
and `Finset.card` is injective on a chain (`eq_of_subset_of_card_le`) — so there are at most
`|S| + 1` fibers, one frontier point each, plus at most `|S|` cut points:

  `(frontier {x | f x = c}).ncard ≤ 2·|S| + 1`   (exact `S`-form)

Corollaries: `≤ 2·netPieceBound g − 1` for net level and superlevel sets — U-4's **definability
(piece) modulus bounds the o-minimality (frontier) modulus**, one graded story, inheriting the
representation-dependence fence (linear for additive circuits, `2^d` for folding) unchanged.
The boolean propagation (`frontier_compl_ncard`, `frontier_union_ncard_le`) grades the whole
`NetDef` algebra. The pre-registered falsifier `RATE_NOT_TIGHTER` (the chain argument fails to
close, leaving `|S| + 2^|S|`) did **not** fire.
-/
import Sundogcert.OMinimalOne

namespace Sundog.OMinimalRate

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.ExactRepr
  Sundog.DefinableRate Sundog.OMinimalOne

/-! ### R2-M — the monotonicity instance -/

/-- An affine stretch is monotone or antitone (sign of the slope; no derivatives needed). -/
theorem affineAway_mono_or_anti {f : ℝ → ℝ} {S : Finset ℝ} (hAff : AffineAway f S)
    {a b : ℝ} (hab : a ≤ b) (hmiss : ∀ s ∈ S, s ∉ Set.Ioo a b) :
    MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b) := by
  obtain ⟨p, q, hpq⟩ := hAff a b hab hmiss
  rcases le_or_gt 0 p with hp | hp
  · left
    intro x hx y hy hxy
    rw [hpq x hx, hpq y hy]
    have := mul_le_mul_of_nonneg_left hxy hp
    linarith
  · right
    intro x hx y hy hxy
    rw [hpq x hx, hpq y hy]
    have := mul_le_mul_of_nonpos_left hxy hp.le
    linarith

/-- **The Monotonicity Theorem, PL instance (R2-M).** Every 1-D ReLU net is monotone or antitone
on every cut-free stretch of an explicit cut set within the U-4 piece budget
(`S.card + 1 ≤ netPieceBound g`). -/
theorem net_mono_or_anti_between_cuts (g : Net 1) :
    ∃ S : Finset ℝ, S.card + 1 ≤ netPieceBound g ∧ ∀ a b : ℝ, a ≤ b →
      (∀ s ∈ S, s ∉ Set.Ioo a b) →
      MonotoneOn (realize1N g) (Set.Icc a b) ∨ AntitoneOn (realize1N g) (Set.Icc a b) := by
  obtain ⟨S, hcard, hAff⟩ := net_pieceBound_cover g
  exact ⟨S, hcard, fun a b hab hmiss => affineAway_mono_or_anti hAff hab hmiss⟩

/-! ### R2-Q — the frontier modulus -/

/-- **The frontier modulus, exact `S`-form (R2-Q core).** A continuous function affine away from
the cut set `S` has at most `2·|S| + 1` frontier points on any level set: `|S|` cuts, plus at most
one frontier point per **initial segment** of cuts (the fiber map `x ↦ S.filter (· < x)` is
injective off the cuts by rung 1's `fiber_aux`, and its image is a `⊆`-chain, so `Finset.card` is
injective on it — at most `|S| + 1` fibers, not `2^|S|`). -/
theorem affineAway_levelSet_ncard {f : ℝ → ℝ} {S : Finset ℝ}
    (hf : Continuous f) (hAff : AffineAway f S) (c : ℝ) :
    (frontier {x | f x = c}).ncard ≤ 2 * S.card + 1 := by
  classical
  have hFin : (frontier {t : ℝ | f t = c}).Finite := affineAway_levelSet_tame hf hAff c
  -- (1) rung 1: the fiber map is injective off the cuts
  have hinj : Set.InjOn (fun x => S.filter (· < x))
      (frontier {t : ℝ | f t = c} \ ↑S) := by
    intro x hx y hy hEq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact fiber_aux hf hAff hx.1 hy.1 (fun hyS => hy.2 (Finset.mem_coe.mpr hyS)) hEq h
    · exact fiber_aux hf hAff hy.1 hx.1 (fun hxS => hx.2 (Finset.mem_coe.mpr hxS)) hEq.symm h
  -- (2) the image is a ⊆-chain (initial segments are nested)
  have hchain : ∀ T₁ ∈ (fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S),
      ∀ T₂ ∈ (fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S),
      T₁ ⊆ T₂ ∨ T₂ ⊆ T₁ := by
    rintro _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩
    rcases le_total x y with h | h
    · refine Or.inl fun t ht => ?_
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, lt_of_lt_of_le ht.2 h⟩
    · refine Or.inr fun t ht => ?_
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨ht.1, lt_of_lt_of_le ht.2 h⟩
  -- (3) card is injective on a chain
  have hcinj : Set.InjOn Finset.card
      ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S)) := by
    intro T₁ hT₁ T₂ hT₂ hcard
    rcases hchain T₁ hT₁ T₂ hT₂ with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq hcard.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq hcard)).symm
  -- (4) count: off-cut frontier points ↦ fibers ↦ cards ∈ [0, |S|]
  have h1 : (frontier {t : ℝ | f t = c} \ ↑S).ncard
      = ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S)).ncard :=
    hinj.ncard_image.symm
  have h2 : ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S)).ncard
      = (Finset.card ''
          ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S))).ncard :=
    hcinj.ncard_image.symm
  have h3 : Finset.card '' ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S))
      ⊆ ↑(Finset.range (S.card + 1)) := by
    rintro _ ⟨T, ⟨x, _, rfl⟩, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Finset.card_filter_le _ _)
  have h4 : (frontier {t : ℝ | f t = c} \ ↑S).ncard ≤ S.card + 1 := by
    rw [h1, h2]
    calc (Finset.card ''
          ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S))).ncard
        ≤ (↑(Finset.range (S.card + 1)) : Set ℕ).ncard :=
          Set.ncard_le_ncard h3 (Finset.finite_toSet _)
      _ = S.card + 1 := by rw [Set.ncard_coe_finset, Finset.card_range]
  -- (5) frontier ⊆ (frontier \ S) ∪ S; add up
  have hcover : frontier {t : ℝ | f t = c}
      ⊆ (frontier {t : ℝ | f t = c} \ ↑S) ∪ ↑S := by
    intro x hx
    by_cases h : x ∈ (S : Set ℝ)
    · exact Set.mem_union_right _ h
    · exact Set.mem_union_left _ ⟨hx, h⟩
  calc (frontier {t : ℝ | f t = c}).ncard
      ≤ ((frontier {t : ℝ | f t = c} \ ↑S) ∪ ↑S).ncard :=
        Set.ncard_le_ncard hcover ((hFin.diff).union S.finite_toSet)
    _ ≤ (frontier {t : ℝ | f t = c} \ ↑S).ncard + (↑S : Set ℝ).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (S.card + 1) + S.card := by
        have := Set.ncard_coe_finset S
        omega
    _ = 2 * S.card + 1 := by ring

/-- The superlevel frontier inherits the modulus (it sits inside the level frontier). -/
theorem affineAway_superlevel_ncard {f : ℝ → ℝ} {S : Finset ℝ}
    (hf : Continuous f) (hAff : AffineAway f S) (c : ℝ) :
    (frontier {x | c < f x}).ncard ≤ 2 * S.card + 1 :=
  le_trans
    (Set.ncard_le_ncard (frontier_superlevel_subset hf c) (affineAway_levelSet_tame hf hAff c))
    (affineAway_levelSet_ncard hf hAff c)

/-- **The U-4 bridge (R2-Q headline).** The definability (piece) modulus bounds the o-minimality
(frontier) modulus: every level set of a 1-D ReLU net has at most `2·netPieceBound g − 1`
frontier points. Inherits U-4's representation-dependence fence unchanged. -/
theorem net_levelSet_ncard (g : Net 1) (c : ℝ) :
    (frontier {x | realize1N g x = c}).ncard ≤ 2 * netPieceBound g - 1 := by
  obtain ⟨S, hcard, hAff⟩ := net_pieceBound_cover g
  have h := affineAway_levelSet_ncard (net_continuous g) hAff c
  omega

/-- The superlevel version of the U-4 bridge. -/
theorem net_superlevel_ncard (g : Net 1) (c : ℝ) :
    (frontier {x | c < realize1N g x}).ncard ≤ 2 * netPieceBound g - 1 := by
  obtain ⟨S, hcard, hAff⟩ := net_pieceBound_cover g
  have h := affineAway_superlevel_ncard (net_continuous g) hAff c
  omega

/-! ### The boolean propagation — grading the whole definable algebra -/

/-- Complement preserves the frontier modulus exactly. -/
theorem frontier_compl_ncard (s : Set ℝ) : (frontier sᶜ).ncard = (frontier s).ncard := by
  rw [frontier_compl]

/-- Union adds frontier moduli (for tame sets). With `frontier_compl_ncard`, every `NetDef` set
inherits an explicit frontier bound from the moduli of its generators. -/
theorem frontier_union_ncard_le {s t : Set ℝ} (hs : Tame s) (ht : Tame t) :
    (frontier (s ∪ t)).ncard ≤ (frontier s).ncard + (frontier t).ncard :=
  le_trans
    (Set.ncard_le_ncard
      ((frontier_union_subset s t).trans
        (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right))
      (hs.union ht))
    (Set.ncard_union_le _ _)

end Sundog.OMinimalRate
