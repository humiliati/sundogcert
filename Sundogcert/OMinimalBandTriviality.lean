/-
# O-min lane R4-D5c: band triviality — the CDT₂ core.

Over every piece of the master refinement, `A` is a union of cells:

- **The per-fiber dichotomies** (`band_dichotomy_fiber`, ray and full versions): between
  consecutive rank values of `fiberFrontier A` the open band contains no frontier point of
  the fiber (rank enumeration + rank ordering), so `preconnected_split` forces the band
  entirely inside or entirely outside `A_x`; likewise below rank 0, above rank `k−1`, and
  — in the frontier-free class `k = 0` — the whole fiber.
- **`regions_cover`** — rays, graphs, and bands cover the line for each fiber
  (`Nat.findGreatest` on the largest rank below the target), so the dichotomies exhaust
  the fiber.
- **`band_triviality` (the capstone)** — one bound `N`, one cut set `C`: on every
  `C`-avoiding interval, a single class `k ≤ N`, the `k` rank functions continuous and
  strictly ordered, and every region — each rank graph, each open band, both rays, and the
  `k = 0` full fiber — is **uniformly** in `A` or out of `A` across the whole interval
  (D5b's constancy turns the per-fiber dichotomies into per-piece selections).

Together: `A ∩ (I × ℝ)` is exactly the union of the selected graphs and bands over `I` —
cell decomposition for `ℝ²` in concrete form. Packaging into a `Cell₂` structure is D5d
(owner-gated shape).
-/
import Sundogcert.OMinimalRefinement

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalNormalForm Sundog.OMinimalAbstract.Fml

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### Rank realization and ordering on a class -/

/-- On the `k`-class, every rank below `k` is realized by its rank function. -/
theorem rank_isNth (hA : S.Definable A) {x : ℝ} {k j : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) (hj : j < k) :
    IsNth (fiberFrontier A) j x (nthFn (fiberFrontier A) j x) :=
  nthFn_isNth (isNth_exists_of_mem_countSet (fiberFrontier_fiber_finite hA x) hx.1 hj)

/-- Rank values are monotone in the index on the `k`-class. -/
theorem rank_le_rank (hA : S.Definable A) {x : ℝ} {k i j : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) (hij : i ≤ j) (hj : j < k) :
    nthFn (fiberFrontier A) i x ≤ nthFn (fiberFrontier A) j x := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact (isNth_lt hlt (rank_isNth hA hx (by omega)) (rank_isNth hA hx hj)).le

/-! ### Frontier-free regions, per fiber -/

private theorem mem_rank_of_frontier (hA : S.Definable A) {x : ℝ} {k : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) {y : ℝ}
    (hyfr : y ∈ frontier {z : ℝ | pairFn x z ∈ A}) :
    ∃ j < k, y = nthFn (fiberFrontier A) j x := by
  have hfin := fiberFrontier_fiber_finite hA x
  have hk : {z : ℝ | pairFn x z ∈ fiberFrontier A}.ncard = k :=
    (mem_exactSet_iff hfin).mp hx
  have hymem : pairFn x y ∈ fiberFrontier A := by
    have := (fiberFrontier_fiber_eq A x).symm ▸ hyfr
    exact this
  obtain ⟨j, hj, hjeq⟩ := (ranks_enumerate hfin).mp hymem
  rw [hk] at hj
  exact ⟨j, hj, hjeq⟩

private theorem band_frontier_free (hA : S.Definable A) {x : ℝ} {k j : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) (hj : j + 1 < k) :
    ∀ y ∈ Set.Ioo (nthFn (fiberFrontier A) j x) (nthFn (fiberFrontier A) (j+1) x),
      y ∉ frontier {z : ℝ | pairFn x z ∈ A} := by
  intro y hy hyfr
  obtain ⟨j', hj', hjeq⟩ := mem_rank_of_frontier hA hx hyfr
  rcases le_or_gt j' j with hle | hgt
  · have hle' := rank_le_rank hA hx hle (by omega)
    rw [hjeq] at hy
    exact absurd hy.1 (not_lt.mpr hle')
  · have hle' := rank_le_rank hA hx (by omega : j + 1 ≤ j') hj'
    rw [hjeq] at hy
    exact absurd hy.2 (not_lt.mpr hle')

private theorem rayLow_frontier_free (hA : S.Definable A) {x : ℝ} {k : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) :
    ∀ y ∈ Set.Iio (nthFn (fiberFrontier A) 0 x),
      y ∉ frontier {z : ℝ | pairFn x z ∈ A} := by
  intro y hy hyfr
  obtain ⟨j', hj', hjeq⟩ := mem_rank_of_frontier hA hx hyfr
  have hle' := rank_le_rank hA hx (Nat.zero_le j') hj'
  rw [hjeq] at hy
  exact absurd hy (not_lt.mpr hle')

private theorem rayHigh_frontier_free (hA : S.Definable A) {x : ℝ} {k : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) (hk : 0 < k) :
    ∀ y ∈ Set.Ioi (nthFn (fiberFrontier A) (k-1) x),
      y ∉ frontier {z : ℝ | pairFn x z ∈ A} := by
  intro y hy hyfr
  obtain ⟨j', hj', hjeq⟩ := mem_rank_of_frontier hA hx hyfr
  have hle' := rank_le_rank hA hx (by omega : j' ≤ k - 1) (by omega)
  rw [hjeq] at hy
  exact absurd hy (not_lt.mpr hle')

private theorem all_frontier_free (hA : S.Definable A) {x : ℝ}
    (hx : x ∈ exactSet (fiberFrontier A) 0) :
    ∀ y : ℝ, y ∉ frontier {z : ℝ | pairFn x z ∈ A} := by
  intro y hyfr
  obtain ⟨j', hj', -⟩ := mem_rank_of_frontier hA hx hyfr
  omega

/-! ### The per-fiber dichotomies -/

/-- **Band dichotomy**: between consecutive ranks, the fiber is all-in or all-out. -/
theorem band_dichotomy_fiber (hA : S.Definable A) {x : ℝ} {k j : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) (hj : j + 1 < k) :
    (∀ y : ℝ, (nthFn (fiberFrontier A) j x < y ∧ y < nthFn (fiberFrontier A) (j+1) x) →
      pairFn x y ∈ A) ∨
    (∀ y : ℝ, (nthFn (fiberFrontier A) j x < y ∧ y < nthFn (fiberFrontier A) (j+1) x) →
      pairFn x y ∉ A) := by
  rcases preconnected_split isPreconnected_Ioo (band_frontier_free hA hx hj)
    with h | h
  · exact Or.inl fun y hy => h ⟨hy.1, hy.2⟩
  · exact Or.inr fun y hy hyA =>
      Set.eq_empty_iff_forall_notMem.mp h y ⟨⟨hy.1, hy.2⟩, hyA⟩

theorem rayLow_dichotomy_fiber (hA : S.Definable A) {x : ℝ} {k : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) :
    (∀ y : ℝ, y < nthFn (fiberFrontier A) 0 x → pairFn x y ∈ A) ∨
    (∀ y : ℝ, y < nthFn (fiberFrontier A) 0 x → pairFn x y ∉ A) := by
  rcases preconnected_split isPreconnected_Iio (rayLow_frontier_free hA hx)
    with h | h
  · exact Or.inl fun y hy => h hy
  · exact Or.inr fun y hy hyA =>
      Set.eq_empty_iff_forall_notMem.mp h y ⟨hy, hyA⟩

theorem rayHigh_dichotomy_fiber (hA : S.Definable A) {x : ℝ} {k : ℕ}
    (hx : x ∈ exactSet (fiberFrontier A) k) (hk : 0 < k) :
    (∀ y : ℝ, nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∈ A) ∨
    (∀ y : ℝ, nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∉ A) := by
  rcases preconnected_split isPreconnected_Ioi (rayHigh_frontier_free hA hx hk)
    with h | h
  · exact Or.inl fun y hy => h hy
  · exact Or.inr fun y hy hyA =>
      Set.eq_empty_iff_forall_notMem.mp h y ⟨hy, hyA⟩

theorem all_dichotomy_fiber (hA : S.Definable A) {x : ℝ}
    (hx : x ∈ exactSet (fiberFrontier A) 0) :
    (∀ y : ℝ, pairFn x y ∈ A) ∨ (∀ y : ℝ, pairFn x y ∉ A) := by
  rcases preconnected_split isPreconnected_univ
    (fun y _ => all_frontier_free hA hx y) with h | h
  · exact Or.inl fun y => h (Set.mem_univ y)
  · exact Or.inr fun y hyA =>
      Set.eq_empty_iff_forall_notMem.mp h y ⟨Set.mem_univ y, hyA⟩

/-! ### The regions cover the fiber -/

/-- **Region covering**: for `k ≥ 1`, every height is below rank 0, on a rank graph,
inside a band between consecutive ranks, or above rank `k−1`. -/
theorem regions_cover (A : Set (Fin 2 → ℝ)) {x : ℝ} {k : ℕ} (hk : 0 < k) (y : ℝ) :
    y < nthFn (fiberFrontier A) 0 x ∨
    (∃ j < k, y = nthFn (fiberFrontier A) j x) ∨
    (∃ j, j + 1 < k ∧ nthFn (fiberFrontier A) j x < y ∧
      y < nthFn (fiberFrontier A) (j+1) x) ∨
    nthFn (fiberFrontier A) (k-1) x < y := by
  classical
  by_cases h0 : nthFn (fiberFrontier A) 0 x ≤ y
  · -- the largest rank below-or-at y
    set P : ℕ → Prop := fun j => nthFn (fiberFrontier A) j x ≤ y with hP
    set j₀ := Nat.findGreatest P (k-1) with hj₀
    have hPj₀ : P j₀ := Nat.findGreatest_spec (Nat.zero_le _) h0
    rcases eq_or_lt_of_le hPj₀ with heq | hlt
    · exact Or.inr (Or.inl ⟨j₀, by
        have := Nat.findGreatest_le (P := P) (k-1)
        omega, heq.symm⟩)
    · by_cases htop : j₀ = k - 1
      · rw [htop] at hlt
        exact Or.inr (Or.inr (Or.inr hlt))
      · have hj₀lt : j₀ + 1 ≤ k - 1 := by
          have := Nat.findGreatest_le (P := P) (k-1)
          omega
        have hnP : ¬ P (j₀ + 1) :=
          Nat.findGreatest_is_greatest (by omega) hj₀lt
        rw [hP] at hnP
        push Not at hnP
        exact Or.inr (Or.inr (Or.inl ⟨j₀, by omega, hlt, hnP⟩))
  · rw [not_le] at h0
    exact Or.inl h0

/-! ### The capstone -/

/-- **Band triviality (D5c — the CDT₂ core).** One bound `N`, one cut set `C`: on every
`C`-avoiding interval there is a single class `k ≤ N` on which the `k` rank functions of
`fiberFrontier A` are continuous and strictly ordered, and every region — each rank graph,
each open band between consecutive ranks, both rays, and the `k = 0` full fiber — is
uniformly inside `A` or outside `A` across the whole interval. -/
theorem band_triviality (hA : S.Definable A) :
    ∃ (N : ℕ) (C : Finset ℝ),
      (∀ x : ℝ, ∃ k ≤ N, x ∈ exactSet (fiberFrontier A) k) ∧
      ∀ a b : ℝ, a < b → (∀ s ∈ C, s ∉ Set.Ioo a b) →
      ∃ k ≤ N,
        Set.Ioo a b ⊆ exactSet (fiberFrontier A) k ∧
        (∀ j < k, ContinuousOn (nthFn (fiberFrontier A) j) (Set.Ioo a b)) ∧
        (∀ i j, i < j → j < k → ∀ x ∈ Set.Ioo a b,
          nthFn (fiberFrontier A) i x < nthFn (fiberFrontier A) j x) ∧
        (∀ j < k,
          (∀ x ∈ Set.Ioo a b, pairFn x (nthFn (fiberFrontier A) j x) ∈ A) ∨
          (∀ x ∈ Set.Ioo a b, pairFn x (nthFn (fiberFrontier A) j x) ∉ A)) ∧
        (∀ j, j + 1 < k →
          (∀ x ∈ Set.Ioo a b, ∀ y : ℝ,
            (nthFn (fiberFrontier A) j x < y ∧ y < nthFn (fiberFrontier A) (j+1) x) →
              pairFn x y ∈ A) ∨
          (∀ x ∈ Set.Ioo a b, ∀ y : ℝ,
            (nthFn (fiberFrontier A) j x < y ∧ y < nthFn (fiberFrontier A) (j+1) x) →
              pairFn x y ∉ A)) ∧
        (0 < k →
          ((∀ x ∈ Set.Ioo a b, ∀ y : ℝ, y < nthFn (fiberFrontier A) 0 x →
              pairFn x y ∈ A) ∨
            (∀ x ∈ Set.Ioo a b, ∀ y : ℝ, y < nthFn (fiberFrontier A) 0 x →
              pairFn x y ∉ A)) ∧
          ((∀ x ∈ Set.Ioo a b, ∀ y : ℝ, nthFn (fiberFrontier A) (k-1) x < y →
              pairFn x y ∈ A) ∨
            (∀ x ∈ Set.Ioo a b, ∀ y : ℝ, nthFn (fiberFrontier A) (k-1) x < y →
              pairFn x y ∉ A))) ∧
        (k = 0 →
          (∀ x ∈ Set.Ioo a b, ∀ y : ℝ, pairFn x y ∈ A) ∨
          (∀ x ∈ Set.Ioo a b, ∀ y : ℝ, pairFn x y ∉ A)) := by
  obtain ⟨N, C, hpart, hmaster⟩ := master_refinement hA
  refine ⟨N, C, hpart, ?_⟩
  intro a b hab havoid
  obtain ⟨⟨k, hkN, hIsub⟩, hcont, hgraph, hband, hrays⟩ := hmaster a b hab havoid
  obtain ⟨hloA, hhiA, hallA⟩ := hrays A (Set.mem_insert _ _)
  refine ⟨k, hkN, hIsub, fun j hj => hcont j (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · -- strict rank ordering
    intro i j hij hjk x hx
    exact isNth_lt hij (rank_isNth hA (hIsub hx) (by omega))
      (rank_isNth hA (hIsub hx) hjk)
  · -- graphs
    intro j hj
    rcases hgraph j (by omega) with hin | hout
    · exact Or.inl fun x hx => hin x hx
    · exact Or.inr fun x hx => hout x hx
  · -- bands
    intro j hjk
    rcases hband j (by omega) A (Set.mem_insert _ _) with hin | hout
    · exact Or.inl fun x hx y hy => (hin x hx) y hy
    · refine Or.inr fun x hx y hy hyA => ?_
      rcases band_dichotomy_fiber hA (hIsub hx) hjk with hfin | hfout
      · exact hout x hx (fun y' hy' => hfin y' hy')
      · exact hfout y hy hyA
  · -- rays
    intro hk
    constructor
    · rcases hloA with hin | hout
      · exact Or.inl fun x hx y hy => (hin x hx) y hy
      · refine Or.inr fun x hx y hy hyA => ?_
        rcases rayLow_dichotomy_fiber hA (hIsub hx) with hfin | hfout
        · exact hout x hx (fun y' hy' => hfin y' hy')
        · exact hfout y hy hyA
    · rcases hhiA (k-1) (by omega) with hin | hout
      · exact Or.inl fun x hx y hy => (hin x hx) y hy
      · refine Or.inr fun x hx y hy hyA => ?_
        rcases rayHigh_dichotomy_fiber hA (hIsub hx) hk with hfin | hfout
        · exact hout x hx (fun y' hy' => hfin y' hy')
        · exact hfout y hy hyA
  · -- the frontier-free class
    intro hk
    subst hk
    rcases hallA with hin | hout
    · exact Or.inl fun x hx y => (hin x hx) y
    · refine Or.inr fun x hx y hyA => ?_
      rcases all_dichotomy_fiber hA (hIsub hx) with hfin | hfout
      · exact hout x hx (fun y' => hfin y')
      · exact hfout y hyA

end Sundog.OMinimalAbstract
