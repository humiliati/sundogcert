/-
# O-min lane R4-D5d-1: the `Cell₂` packaging layer.

The cell vocabulary and the two components the final assembly needs:

- **`Cell₁`/`Cell₂`** — cells of the line (point, interval, rays, the line) and of the
  plane (graph, band, half-bands, full column) over a base cell, with `toSet` realization,
  `WellFormed` (height data continuous and ordered on the base), and `IsCellDecomp`
  (covering + pairwise disjoint + adapted to `A` + well-formed). Definability of each
  constructed cell is inherited from the rank functions and is not part of the predicate.
- **`baseCells`** — the decomposition of the line induced by a finite cut set `C`, built
  SORT-FREE: the points of `C`, the adjacent gaps (pairs of `C`-elements with no
  `C`-element between, filtered from `C ×ˢ C`), and the two outer rays (the whole line
  when `C = ∅`). `baseCells_covers` and `baseCells_pairwise` make it a partition.
- **The ray upgrades** — `band_triviality` speaks about bounded `C`-avoiding intervals;
  the outer base cells are rays. `ray_low_uniform`/`ray_high_uniform`/`univ_uniform`
  upgrade any uniformity clause from all bounded subintervals to the full ray (two-point
  argument: a non-uniform pair would sit inside one bounded interval).

D5d-2 (next): the assembly — `cell_decomposition : ∃ cells, IsCellDecomp cells A`.
-/
import Sundogcert.OMinimalBandTriviality

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

/-! ### Cells -/

/-- Cells of the line. -/
inductive Cell₁ : Type where
  | pt (r : ℝ)
  | ioo (a b : ℝ)
  | iio (b : ℝ)
  | ioi (a : ℝ)
  | univ

namespace Cell₁

/-- Realization. -/
def toSet : Cell₁ → Set ℝ
  | pt r => {r}
  | ioo a b => Set.Ioo a b
  | iio b => Set.Iio b
  | ioi a => Set.Ioi a
  | univ => Set.univ

end Cell₁

/-- Cells of the plane over a base cell: a graph, a band between two height functions,
the two half-bands, or a full column. -/
inductive Cell₂ : Type where
  | graph (base : Cell₁) (f : ℝ → ℝ)
  | band (base : Cell₁) (f g : ℝ → ℝ)
  | bandLow (base : Cell₁) (g : ℝ → ℝ)
  | bandHigh (base : Cell₁) (f : ℝ → ℝ)
  | full (base : Cell₁)

namespace Cell₂

/-- The base of a plane cell. -/
def base : Cell₂ → Cell₁
  | graph C _ => C
  | band C _ _ => C
  | bandLow C _ => C
  | bandHigh C _ => C
  | full C => C

/-- Realization. -/
def toSet : Cell₂ → Set (Fin 2 → ℝ)
  | graph C f => {h | h 0 ∈ C.toSet ∧ h 1 = f (h 0)}
  | band C f g => {h | h 0 ∈ C.toSet ∧ (f (h 0) < h 1 ∧ h 1 < g (h 0))}
  | bandLow C g => {h | h 0 ∈ C.toSet ∧ h 1 < g (h 0)}
  | bandHigh C f => {h | h 0 ∈ C.toSet ∧ f (h 0) < h 1}
  | full C => {h | h 0 ∈ C.toSet}

/-- Points of a plane cell sit over its base. -/
theorem base_mem {c : Cell₂} {h : Fin 2 → ℝ} (hc : h ∈ c.toSet) :
    h 0 ∈ c.base.toSet := by
  cases c with
  | graph C f => exact hc.1
  | band C f g => exact hc.1
  | bandLow C g => exact hc.1
  | bandHigh C f => exact hc.1
  | full C => exact hc

/-- Well-formedness: height data continuous and ordered on the base. -/
def WellFormed : Cell₂ → Prop
  | graph C f => ContinuousOn f C.toSet
  | band C f g => ContinuousOn f C.toSet ∧ ContinuousOn g C.toSet ∧
      ∀ x ∈ C.toSet, f x < g x
  | bandLow C g => ContinuousOn g C.toSet
  | bandHigh C f => ContinuousOn f C.toSet
  | full _ => True

end Cell₂

/-- A finite cell decomposition of the plane adapted to `A`: the cells cover, are pairwise
disjoint and well-formed, and each lies inside `A` or misses it. -/
structure IsCellDecomp (cells : List Cell₂) (A : Set (Fin 2 → ℝ)) : Prop where
  covers : ∀ h : Fin 2 → ℝ, ∃ c ∈ cells, h ∈ c.toSet
  pairwise : cells.Pairwise (fun c c' => Disjoint c.toSet c'.toSet)
  adapted : ∀ c ∈ cells, c.toSet ⊆ A ∨ Disjoint c.toSet A
  wellFormed : ∀ c ∈ cells, c.WellFormed

/-! ### The base decomposition of the line -/

/-- Adjacent pair of the cut set: a genuine gap with no cut point inside. -/
def adjPair (C : Finset ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 < p.2 ∧ ∀ c ∈ C, c ≤ p.1 ∨ p.2 ≤ c

open Classical in
/-- The base cells induced by a finite cut set: its points, its adjacent gaps, and the two
outer rays (the whole line if the cut set is empty). Sort-free. -/
noncomputable def baseCells (C : Finset ℝ) : List Cell₁ :=
  if hC : C.Nonempty then
    (C.toList.map .pt) ++
    (((C ×ˢ C).toList.filterMap fun p =>
      if adjPair C p then some (.ioo p.1 p.2) else none) ++
    [.iio (C.min' hC), .ioi (C.max' hC)])
  else [.univ]

open Classical in
/-- Gap-membership characterization (public: the D5d-2 assembly inverts it). -/
theorem mem_gaps_iff {C : Finset ℝ} {c : Cell₁} :
    c ∈ ((C ×ˢ C).toList.filterMap fun p =>
        if adjPair C p then some (.ioo p.1 p.2) else none) ↔
      ∃ l u : ℝ, l ∈ C ∧ u ∈ C ∧ adjPair C (l, u) ∧ c = .ioo l u := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hsome⟩
    by_cases hadj : adjPair C p
    · rw [if_pos hadj] at hsome
      have hmem := Finset.mem_product.mp (Finset.mem_toList.mp hp)
      cases hsome
      exact ⟨p.1, p.2, hmem.1, hmem.2, hadj, rfl⟩
    · rw [if_neg hadj] at hsome
      simp at hsome
  · rintro ⟨l, u, hl, hu, hadj, rfl⟩
    refine ⟨(l, u), Finset.mem_toList.mpr (Finset.mem_product.mpr ⟨hl, hu⟩), ?_⟩
    rw [if_pos hadj]

/-- **The base cells cover the line.** -/
theorem baseCells_covers (C : Finset ℝ) : ∀ x : ℝ, ∃ c ∈ baseCells C, x ∈ c.toSet := by
  classical
  intro x
  by_cases hC : C.Nonempty
  · rw [baseCells, dif_pos hC]
    by_cases hx : x ∈ C
    · exact ⟨.pt x, List.mem_append_left _
        (List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, rfl⟩), rfl⟩
    · by_cases hlo : (C.filter (· < x)).Nonempty <;>
        by_cases hhi : (C.filter (x < ·)).Nonempty
      · -- an interior gap
        have hlC := Finset.mem_filter.mp ((C.filter (· < x)).max'_mem hlo)
        have huC := Finset.mem_filter.mp ((C.filter (x < ·)).min'_mem hhi)
        have hadj : adjPair C ((C.filter (· < x)).max' hlo, (C.filter (x < ·)).min' hhi) := by
          refine ⟨lt_trans hlC.2 huC.2, ?_⟩
          intro c hc
          rcases lt_trichotomy c x with h | rfl | h
          · exact Or.inl ((C.filter (· < x)).le_max' c (Finset.mem_filter.mpr ⟨hc, h⟩))
          · exact absurd hc hx
          · exact Or.inr ((C.filter (x < ·)).min'_le c (Finset.mem_filter.mpr ⟨hc, h⟩))
        exact ⟨.ioo _ _, List.mem_append_right _ (List.mem_append_left _
          (mem_gaps_iff.mpr ⟨_, _, hlC.1, huC.1, hadj, rfl⟩)), hlC.2, huC.2⟩
      · -- nothing above: the upper ray
        have hall : ∀ c ∈ C, c < x := by
          intro c hc
          rcases lt_trichotomy c x with h | rfl | h
          · exact h
          · exact absurd hc hx
          · exact absurd (Finset.mem_filter.mpr ⟨hc, h⟩)
              (fun hmem => hhi ⟨c, hmem⟩)
        exact ⟨.ioi (C.max' hC), List.mem_append_right _ (List.mem_append_right _
          (by simp)), hall _ (C.max'_mem hC)⟩
      · -- nothing below: the lower ray
        have hall : ∀ c ∈ C, x < c := by
          intro c hc
          rcases lt_trichotomy c x with h | rfl | h
          · exact absurd (Finset.mem_filter.mpr ⟨hc, h⟩)
              (fun hmem => hlo ⟨c, hmem⟩)
          · exact absurd hc hx
          · exact h
        exact ⟨.iio (C.min' hC), List.mem_append_right _ (List.mem_append_right _
          (by simp)), hall _ (C.min'_mem hC)⟩
      · -- both empty is impossible for nonempty C
        exfalso
        obtain ⟨c, hc⟩ := hC
        rcases lt_trichotomy c x with h | rfl | h
        · exact hlo ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩
        · exact hx hc
        · exact hhi ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩
  · rw [baseCells, dif_neg hC]
    exact ⟨.univ, by simp, Set.mem_univ x⟩

private theorem gap_disjoint {C : Finset ℝ} {l u l' u' : ℝ}
    (hlu : adjPair C (l, u)) (hl'u' : adjPair C (l', u'))
    (hlC : l ∈ C) (huC : u ∈ C) (hl'C : l' ∈ C) (hu'C : u' ∈ C)
    (hne : ¬ (l = l' ∧ u = u')) :
    Disjoint (Set.Ioo l u) (Set.Ioo l' u') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hne
  constructor
  · rcases lt_trichotomy l l' with h | h | h
    · rcases hlu.2 l' hl'C with hle | hle
      · exact absurd h (not_lt.mpr hle)
      · exact absurd (lt_trans hx'.1 hx.2) (not_lt.mpr hle)
    · exact h
    · rcases hl'u'.2 l hlC with hle | hle
      · exact absurd h (not_lt.mpr hle)
      · exact absurd (lt_trans hx.1 hx'.2) (not_lt.mpr hle)
  · rcases lt_trichotomy u u' with h | h | h
    · rcases hl'u'.2 u huC with hle | hle
      · exact absurd (lt_trans hx'.1 hx.2) (not_lt.mpr hle)
      · exact absurd h (not_lt.mpr hle)
    · exact h
    · rcases hlu.2 u' hu'C with hle | hle
      · exact absurd (lt_trans hx.1 hx'.2) (not_lt.mpr hle)
      · exact absurd h (not_lt.mpr hle)

/-- Self-contained pairwise-through-filterMap, carrying source memberships. -/
private theorem pairwise_filterMap_of_forall {α β : Type*} {R : β → β → Prop}
    {f : α → Option β} {l : List α} (hnd : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ c, f a = some c → ∀ d, f b = some d → R c d) :
    List.Pairwise R (l.filterMap f) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    obtain ⟨hanotin, hndl⟩ := List.nodup_cons.mp hnd
    rw [List.filterMap_cons]
    have htail := ih hndl (fun x hx y hy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    rcases hfa : f a with _ | c
    · exact htail
    · rw [List.pairwise_cons]
      refine ⟨?_, htail⟩
      intro d hd
      obtain ⟨b, hb, hbd⟩ := List.mem_filterMap.mp hd
      exact h a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
        (fun heq => hanotin (heq ▸ hb)) c hfa d hbd

/-- **The base cells are pairwise disjoint.** -/
theorem baseCells_pairwise (C : Finset ℝ) :
    (baseCells C).Pairwise (fun c c' => Disjoint c.toSet c'.toSet) := by
  classical
  by_cases hC : C.Nonempty
  · rw [baseCells, dif_pos hC]
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- points pairwise
      rw [List.pairwise_map]
      exact (Finset.nodup_toList C).imp fun hne => Set.disjoint_singleton.mpr hne
    · rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · -- gaps pairwise
        refine pairwise_filterMap_of_forall (Finset.nodup_toList _) ?_
        intro p hp p' hp' hne c hc c' hc'
        by_cases hadj : adjPair C p
        · by_cases hadj' : adjPair C p'
          · rw [if_pos hadj] at hc
            rw [if_pos hadj'] at hc'
            cases hc
            cases hc'
            have hmem := Finset.mem_product.mp (Finset.mem_toList.mp hp)
            have hmem' := Finset.mem_product.mp (Finset.mem_toList.mp hp')
            exact gap_disjoint hadj hadj' hmem.1 hmem.2 hmem'.1 hmem'.2
              (fun h => hne (Prod.ext h.1 h.2))
          · rw [if_neg hadj'] at hc'
            simp at hc'
        · rw [if_neg hadj] at hc
          simp at hc
      · -- the two rays disjoint
        rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_singleton _ _⟩
        intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        rw [Set.disjoint_left]
        intro x hx hx'
        exact lt_irrefl x
          (lt_trans (lt_of_lt_of_le hx (Finset.min'_le _ _ (C.max'_mem hC))) hx')
      · -- gaps vs rays
        intro c hcg c' hcr
        obtain ⟨l, u, hlC, huC, hadj, rfl⟩ := mem_gaps_iff.mp hcg
        rw [List.mem_cons, List.mem_singleton] at hcr
        rcases hcr with rfl | rfl
        · rw [Set.disjoint_left]
          intro x hx hx'
          exact lt_irrefl x
            (lt_trans hx' (lt_of_le_of_lt (Finset.min'_le _ _ hlC) hx.1))
        · rw [Set.disjoint_left]
          intro x hx hx'
          exact lt_irrefl x
            (lt_trans (lt_of_lt_of_le hx.2 (Finset.le_max' _ _ huC)) hx')
    · -- points vs the rest
      intro c hcp c' hcr
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcp
      have hrC := Finset.mem_toList.mp hr
      rw [List.mem_append] at hcr
      rcases hcr with hcg | hcr
      · obtain ⟨l, u, hlC, huC, hadj, rfl⟩ := mem_gaps_iff.mp hcg
        rw [Set.disjoint_left]
        intro x hx hx'
        simp only [Cell₁.toSet, Set.mem_singleton_iff] at hx
        subst hx
        rcases hadj.2 x hrC with hle | hle
        · exact absurd hx'.1 (not_lt.mpr hle)
        · exact absurd hx'.2 (not_lt.mpr hle)
      · rw [List.mem_cons, List.mem_singleton] at hcr
        rcases hcr with rfl | rfl
        · rw [Set.disjoint_left]
          intro x hx hx'
          simp only [Cell₁.toSet, Set.mem_singleton_iff] at hx
          subst hx
          exact absurd hx' (not_lt.mpr (Finset.min'_le _ _ hrC))
        · rw [Set.disjoint_left]
          intro x hx hx'
          simp only [Cell₁.toSet, Set.mem_singleton_iff] at hx
          subst hx
          exact absurd hx' (not_lt.mpr (Finset.le_max' _ _ hrC))
  · rw [baseCells, dif_neg hC]
    exact List.pairwise_singleton _ _

/-! ### Ray upgrades of interval uniformity -/

/-- Uniformity on all bounded subintervals of a lower ray upgrades to the ray. -/
theorem ray_low_uniform {m : ℝ} {P Q : ℝ → Prop}
    (h : ∀ t, t < m → (∀ x ∈ Set.Ioo t m, P x) ∨ (∀ x ∈ Set.Ioo t m, Q x)) :
    (∀ x ∈ Set.Iio m, P x) ∨ (∀ x ∈ Set.Iio m, Q x) := by
  by_cases hall : ∀ x ∈ Set.Iio m, P x
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x₁, hx₁m, hnx₁⟩ := hall
    refine Or.inr fun x hx => ?_
    obtain ⟨t, ht⟩ := exists_lt (min x x₁)
    have htm : t < m := lt_trans (lt_of_lt_of_le ht (min_le_left _ _)) hx
    rcases h t htm with hP | hQ
    · exact absurd (hP x₁ ⟨lt_of_lt_of_le ht (min_le_right _ _), hx₁m⟩) hnx₁
    · exact hQ x ⟨lt_of_lt_of_le ht (min_le_left _ _), hx⟩

/-- Uniformity on all bounded subintervals of an upper ray upgrades to the ray. -/
theorem ray_high_uniform {m : ℝ} {P Q : ℝ → Prop}
    (h : ∀ t, m < t → (∀ x ∈ Set.Ioo m t, P x) ∨ (∀ x ∈ Set.Ioo m t, Q x)) :
    (∀ x ∈ Set.Ioi m, P x) ∨ (∀ x ∈ Set.Ioi m, Q x) := by
  by_cases hall : ∀ x ∈ Set.Ioi m, P x
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x₁, hx₁m, hnx₁⟩ := hall
    refine Or.inr fun x hx => ?_
    obtain ⟨t, ht⟩ := exists_gt (max x x₁)
    have hmt : m < t := lt_trans hx (lt_of_le_of_lt (le_max_left _ _) ht)
    rcases h t hmt with hP | hQ
    · exact absurd (hP x₁ ⟨hx₁m, lt_of_le_of_lt (le_max_right _ _) ht⟩) hnx₁
    · exact hQ x ⟨hx, lt_of_le_of_lt (le_max_left _ _) ht⟩

/-- Uniformity on all bounded intervals upgrades to the whole line. -/
theorem univ_uniform {P Q : ℝ → Prop}
    (h : ∀ t u : ℝ, t < u → (∀ x ∈ Set.Ioo t u, P x) ∨ (∀ x ∈ Set.Ioo t u, Q x)) :
    (∀ x : ℝ, P x) ∨ (∀ x : ℝ, Q x) := by
  by_cases hall : ∀ x : ℝ, P x
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨x₁, hnx₁⟩ := hall
    refine Or.inr fun x => ?_
    obtain ⟨t, ht⟩ := exists_lt (min x x₁)
    obtain ⟨u, hu⟩ := exists_gt (max x x₁)
    have htu : t < u :=
      lt_trans (lt_of_lt_of_le ht (le_trans (min_le_left _ _) (le_max_left _ _))) hu
    rcases h t u htu with hP | hQ
    · exact absurd (hP x₁ ⟨lt_of_lt_of_le ht (min_le_right _ _),
        lt_of_le_of_lt (le_max_right _ _) hu⟩) hnx₁
    · exact hQ x ⟨lt_of_lt_of_le ht (min_le_left _ _),
        lt_of_le_of_lt (le_max_left _ _) hu⟩

end Sundog.OMinimalAbstract
