/-
# O-min lane R4-D5d-2: CELL DECOMPOSITION FOR ℝ² — the arc's terminal theorem.

**`cell_decomposition`**: every definable `A ⊆ ℝ²` admits a finite cell decomposition —
a list of well-formed plane cells (graphs and bands of continuous height functions over
point/interval/ray/line bases) that covers the plane, is pairwise disjoint, and is adapted
to `A` (each cell inside `A` or disjoint from it). `cell_decomposition_mem` is the union
form: membership in `A` is membership in one of its inside-cells.

Assembly:
- **`cells_over_uniform`** — the generic per-base constructor: over ANY base cell carrying
  a uniform class `k` and uniform region selections, the column decomposes into
  `bandLow · graphs (rank 0..k−1) · bands · bandHigh` (or one `full` cell for `k = 0`);
  covering from `regions_cover`, disjointness from the strict rank ordering, adaptedness
  from the selections, well-formedness from rank continuity.
- The per-base instantiations: point bases get their selections from the per-fiber
  dichotomies (D5c) pointwise; adjacent gaps are cut-avoiding, so `band_triviality` feeds
  them directly; the outer rays and the `C = ∅` line get theirs from the two-point
  uniformity upgrades (D5d-1), with the class matched across overlapping intervals.
- The final list is `(baseCells C).flatMap` of the per-base lists: covering from
  `baseCells_covers`, cross-base disjointness from `baseCells_pairwise` (cells project to
  their bases).

The height functions are the rank functions of `fiberFrontier A` — definable throughout;
`IsCellDecomp` records the topological content (the o-minimal input is `band_triviality`).
-/
import Sundogcert.OMinimalCells

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### Local helpers -/

private theorem cPairEta (h : Fin 2 → ℝ) : pairFn (h 0) (h 1) = h := by
  funext i
  fin_cases i <;> simp [pairFn]

private theorem pairwise_imp_of_mem {α : Type*} {R S : α → α → Prop} {l : List α}
    (h : ∀ a ∈ l, ∀ b ∈ l, R a b → S a b) (hl : l.Pairwise R) : l.Pairwise S := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
    rw [List.pairwise_cons]
    exact ⟨fun b hb => h a List.mem_cons_self b (List.mem_cons_of_mem _ hb) (hhead b hb),
      ih (fun x hx y hy =>
        h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) htail⟩

private theorem pairwise_flatMap_of {α β : Type*} {R : β → β → Prop} {f : α → List β}
    {l : List α} (hin : ∀ a ∈ l, (f a).Pairwise R)
    (hcross : l.Pairwise (fun a a' => ∀ c ∈ f a, ∀ c' ∈ f a', R c c')) :
    (l.flatMap f).Pairwise R := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    rw [List.flatMap_cons, List.pairwise_append]
    obtain ⟨hcross_head, hcross_tail⟩ := List.pairwise_cons.mp hcross
    refine ⟨hin a List.mem_cons_self,
      ih (fun x hx => hin x (List.mem_cons_of_mem _ hx)) hcross_tail, ?_⟩
    intro c hc c' hc'
    obtain ⟨a', ha', hc'mem⟩ := List.mem_flatMap.mp hc'
    exact hcross_head a' ha' c hc c' hc'mem

/-! ### The generic per-base constructor -/

private theorem cells_over_uniform (hA : S.Definable A) (b : Cell₁) (k : ℕ)
    (hcls : ∀ x ∈ b.toSet, x ∈ exactSet (fiberFrontier A) k)
    (hcont : ∀ j < k, ContinuousOn (nthFn (fiberFrontier A) j) b.toSet)
    (hgraph : ∀ j < k,
      (∀ x ∈ b.toSet, pairFn x (nthFn (fiberFrontier A) j x) ∈ A) ∨
      (∀ x ∈ b.toSet, pairFn x (nthFn (fiberFrontier A) j x) ∉ A))
    (hband : ∀ j, j + 1 < k →
      (∀ x ∈ b.toSet, ∀ y : ℝ, (nthFn (fiberFrontier A) j x < y ∧
        y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∈ A) ∨
      (∀ x ∈ b.toSet, ∀ y : ℝ, (nthFn (fiberFrontier A) j x < y ∧
        y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∉ A))
    (hlo : 0 < k →
      (∀ x ∈ b.toSet, ∀ y : ℝ, y < nthFn (fiberFrontier A) 0 x → pairFn x y ∈ A) ∨
      (∀ x ∈ b.toSet, ∀ y : ℝ, y < nthFn (fiberFrontier A) 0 x → pairFn x y ∉ A))
    (hhi : 0 < k →
      (∀ x ∈ b.toSet, ∀ y : ℝ, nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∈ A) ∨
      (∀ x ∈ b.toSet, ∀ y : ℝ, nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∉ A))
    (hall : k = 0 →
      (∀ x ∈ b.toSet, ∀ y : ℝ, pairFn x y ∈ A) ∨
      (∀ x ∈ b.toSet, ∀ y : ℝ, pairFn x y ∉ A)) :
    ∃ cells : List Cell₂, (∀ c ∈ cells, c.base = b) ∧
      (∀ h : Fin 2 → ℝ, h 0 ∈ b.toSet → ∃ c ∈ cells, h ∈ c.toSet) ∧
      cells.Pairwise (fun c c' => Disjoint c.toSet c'.toSet) ∧
      (∀ c ∈ cells, c.toSet ⊆ A ∨ Disjoint c.toSet A) ∧
      (∀ c ∈ cells, c.WellFormed) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0: one full column
    refine ⟨[.full b], ?_, ?_, List.pairwise_singleton _ _, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      rfl
    · intro h hb
      exact ⟨.full b, List.mem_singleton.mpr rfl, hb⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      rcases hall rfl with hin | hout
      · refine Or.inl fun h hh => ?_
        rw [← cPairEta h]
        exact hin (h 0) hh (h 1)
      · refine Or.inr ?_
        rw [Set.disjoint_left]
        intro h hh hhA
        rw [← cPairEta h] at hhA
        exact hout (h 0) hh (h 1) hhA
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
  · -- k > 0: bandLow · graphs · bands · bandHigh
    have hstrict : ∀ x ∈ b.toSet, ∀ i j : ℕ, i < j → j < k →
        nthFn (fiberFrontier A) i x < nthFn (fiberFrontier A) j x :=
      fun x hx i j hij hj =>
        isNth_lt hij (rank_isNth hA (hcls x hx) (by omega)) (rank_isNth hA (hcls x hx) hj)
    have hmono : ∀ x ∈ b.toSet, ∀ i j : ℕ, i ≤ j → j < k →
        nthFn (fiberFrontier A) i x ≤ nthFn (fiberFrontier A) j x := by
      intro x hx i j hij hj
      rcases eq_or_lt_of_le hij with rfl | h
      · exact le_refl _
      · exact (hstrict x hx i j h hj).le
    refine ⟨.bandLow b (nthFn (fiberFrontier A) 0) ::
      (((List.range k).map fun j => .graph b (nthFn (fiberFrontier A) j)) ++
      (((List.range (k-1)).map fun j =>
        .band b (nthFn (fiberFrontier A) j) (nthFn (fiberFrontier A) (j+1))) ++
      [.bandHigh b (nthFn (fiberFrontier A) (k-1))])), ?_, ?_, ?_, ?_, ?_⟩
    · -- bases
      intro c hc
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · rfl
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
        rfl
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
        rfl
      · rw [List.mem_singleton] at hc
        subst hc
        rfl
    · -- covers
      intro h hb
      rcases regions_cover A (x := h 0) hk (h 1) with hlow | ⟨j, hj, heq⟩ |
        ⟨j, hj, h1, h2⟩ | hhigh
      · exact ⟨.bandLow b (nthFn (fiberFrontier A) 0), List.mem_cons_self, hb, hlow⟩
      · exact ⟨.graph b (nthFn (fiberFrontier A) j), List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)),
          hb, heq⟩
      · exact ⟨.band b (nthFn (fiberFrontier A) j) (nthFn (fiberFrontier A) (j+1)),
          List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _
            (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))), hb, h1, h2⟩
      · exact ⟨.bandHigh b (nthFn (fiberFrontier A) (k-1)), List.mem_cons_of_mem _
          (List.mem_append_right _ (List.mem_append_right _
            (List.mem_singleton.mpr rfl))), hb, hhigh⟩
    · -- pairwise disjoint
      rw [List.pairwise_cons]
      constructor
      · -- bandLow vs the rest
        intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
          rw [Set.disjoint_left]
          rintro h ⟨hb, hlt⟩ ⟨-, heq⟩
          rw [heq] at hlt
          exact absurd hlt (not_lt.mpr
            (hmono (h 0) hb 0 j (Nat.zero_le _) (List.mem_range.mp hj)))
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
          rw [Set.disjoint_left]
          rintro h ⟨hb, hlt⟩ ⟨-, h1, -⟩
          have hle := hmono (h 0) hb 0 j (Nat.zero_le _)
            (by have := List.mem_range.mp hj; omega)
          exact lt_irrefl _ (lt_trans (lt_of_le_of_lt hle h1) hlt)
        · rw [List.mem_singleton] at hc
          subst hc
          rw [Set.disjoint_left]
          rintro h ⟨hb, hlt⟩ ⟨-, hgt⟩
          have hle := hmono (h 0) hb 0 (k-1) (Nat.zero_le _) (by omega)
          exact lt_irrefl _ (lt_trans (lt_of_le_of_lt hle hgt) hlt)
      rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · -- graphs pairwise
        rw [List.pairwise_map]
        refine pairwise_imp_of_mem ?_ List.pairwise_lt_range
        intro i hi j hj hij
        rw [Set.disjoint_left]
        rintro h ⟨hb, he1⟩ ⟨-, he2⟩
        have := hstrict (h 0) hb i j hij (List.mem_range.mp hj)
        rw [← he1, ← he2] at this
        exact lt_irrefl _ this
      · rw [List.pairwise_append]
        refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
        · -- bands pairwise
          rw [List.pairwise_map]
          refine pairwise_imp_of_mem ?_ List.pairwise_lt_range
          intro i hi j hj hij
          rw [Set.disjoint_left]
          rintro h ⟨hb, -, hi2⟩ ⟨-, hj1, -⟩
          have hjk := List.mem_range.mp hj
          have hle := hmono (h 0) hb (i+1) j (by omega) (by omega)
          exact lt_irrefl _ (lt_trans (lt_of_lt_of_le hi2 hle) hj1)
        · -- bands vs bandHigh
          intro c hcb c' hch
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcb
          rw [List.mem_singleton] at hch
          subst hch
          rw [Set.disjoint_left]
          rintro h ⟨hb, -, h2⟩ ⟨-, hgt⟩
          have hjk := List.mem_range.mp hj
          have hle := hmono (h 0) hb (j+1) (k-1) (by omega) (by omega)
          exact lt_irrefl _ (lt_trans (lt_of_lt_of_le h2 hle) hgt)
      · -- graphs vs bands and bandHigh
        intro c hcg c' hc'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcg
        have hik := List.mem_range.mp hi
        rw [List.mem_append] at hc'
        rcases hc' with hcb | hch
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcb
          have hjk := List.mem_range.mp hj
          rw [Set.disjoint_left]
          rintro h ⟨hb, he⟩ ⟨-, hj1, hj2⟩
          rw [he] at hj1 hj2
          rcases le_or_gt i j with hle | hgt
          · exact absurd hj1 (not_lt.mpr (hmono (h 0) hb i j hle (by omega)))
          · exact absurd hj2 (not_lt.mpr (hmono (h 0) hb (j+1) i (by omega) (by omega)))
        · rw [List.mem_singleton] at hch
          subst hch
          rw [Set.disjoint_left]
          rintro h ⟨hb, he⟩ ⟨-, hgt⟩
          rw [he] at hgt
          exact absurd hgt (not_lt.mpr (hmono (h 0) hb i (k-1) (by omega) (by omega)))
    · -- adapted
      intro c hc
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · rcases hlo hk with hin | hout
        · refine Or.inl ?_
          rintro h ⟨hb, hlt⟩
          rw [← cPairEta h]
          exact hin (h 0) hb (h 1) hlt
        · refine Or.inr ?_
          rw [Set.disjoint_left]
          rintro h ⟨hb, hlt⟩ hhA
          rw [← cPairEta h] at hhA
          exact hout (h 0) hb (h 1) hlt hhA
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
        rcases hgraph j (List.mem_range.mp hj) with hin | hout
        · refine Or.inl ?_
          rintro h ⟨hb, he⟩
          rw [← cPairEta h, he]
          exact hin (h 0) hb
        · refine Or.inr ?_
          rw [Set.disjoint_left]
          rintro h ⟨hb, he⟩ hhA
          rw [← cPairEta h, he] at hhA
          exact hout (h 0) hb hhA
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
        rcases hband j (by have := List.mem_range.mp hj; omega) with hin | hout
        · refine Or.inl ?_
          rintro h ⟨hb, h1, h2⟩
          rw [← cPairEta h]
          exact hin (h 0) hb (h 1) ⟨h1, h2⟩
        · refine Or.inr ?_
          rw [Set.disjoint_left]
          rintro h ⟨hb, h1, h2⟩ hhA
          rw [← cPairEta h] at hhA
          exact hout (h 0) hb (h 1) ⟨h1, h2⟩ hhA
      · rw [List.mem_singleton] at hc
        subst hc
        rcases hhi hk with hin | hout
        · refine Or.inl ?_
          rintro h ⟨hb, hgt⟩
          rw [← cPairEta h]
          exact hin (h 0) hb (h 1) hgt
        · refine Or.inr ?_
          rw [Set.disjoint_left]
          rintro h ⟨hb, hgt⟩ hhA
          rw [← cPairEta h] at hhA
          exact hout (h 0) hb (h 1) hgt hhA
    · -- well-formed
      intro c hc
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hcont 0 hk
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
        exact hcont j (List.mem_range.mp hj)
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
        have hjk := List.mem_range.mp hj
        exact ⟨hcont j (by omega), hcont (j+1) (by omega),
          fun x hx => hstrict x hx j (j+1) (Nat.lt_succ_self j) (by omega)⟩
      · rw [List.mem_singleton] at hc
        subst hc
        exact hcont (k-1) (by omega)

/-! ### The terminal theorem -/

/-- **CELL DECOMPOSITION FOR ℝ² (CDT₂).** Every definable planar set admits a finite,
pairwise disjoint, covering, adapted, well-formed cell decomposition. -/
theorem cell_decomposition (hA : S.Definable A) :
    ∃ cells : List Cell₂, IsCellDecomp cells A := by
  classical
  obtain ⟨N, C, hpart, htriv⟩ := band_triviality hA
  -- the per-base cell lists
  have hover : ∀ b : Cell₁, ∃ cellsb : List Cell₂, b ∈ baseCells C →
      ((∀ c ∈ cellsb, c.base = b) ∧
       (∀ h : Fin 2 → ℝ, h 0 ∈ b.toSet → ∃ c ∈ cellsb, h ∈ c.toSet) ∧
       cellsb.Pairwise (fun c c' => Disjoint c.toSet c'.toSet) ∧
       (∀ c ∈ cellsb, c.toSet ⊆ A ∨ Disjoint c.toSet A) ∧
       (∀ c ∈ cellsb, c.WellFormed)) := by
    intro b
    by_cases hb : b ∈ baseCells C
    swap
    · exact ⟨[], fun h => absurd h hb⟩
    by_cases hC : C.Nonempty
    · rw [baseCells, dif_pos hC] at hb
      rw [List.mem_append] at hb
      rcases hb with hpt | hb
      · -- a point base
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hpt
        have hxr : ∀ x ∈ (Cell₁.pt r).toSet, x = r := by
          intro x hx
          simpa [Cell₁.toSet] using hx
        have hfin := fiberFrontier_fiber_finite hA r
        have hclsr : r ∈ exactSet (fiberFrontier A)
            {y : ℝ | pairFn r y ∈ fiberFrontier A}.ncard :=
          (mem_exactSet_iff hfin).mpr rfl
        obtain ⟨cells, hprops⟩ := cells_over_uniform hA (.pt r)
          {y : ℝ | pairFn r y ∈ fiberFrontier A}.ncard
          (fun x hx => by rw [hxr x hx]; exact hclsr)
          (fun j hj => continuousOn_singleton _ r)
          (fun j hj => by
            by_cases hmem : pairFn r (nthFn (fiberFrontier A) j r) ∈ A
            · exact Or.inl fun x hx => by rw [hxr x hx]; exact hmem
            · exact Or.inr fun x hx => by rw [hxr x hx]; exact hmem)
          (fun j hj => by
            rcases band_dichotomy_fiber hA hclsr hj with hin | hout
            · exact Or.inl fun x hx => by rw [hxr x hx]; exact hin
            · exact Or.inr fun x hx => by rw [hxr x hx]; exact hout)
          (fun hk => by
            rcases rayLow_dichotomy_fiber hA hclsr with hin | hout
            · exact Or.inl fun x hx => by rw [hxr x hx]; exact hin
            · exact Or.inr fun x hx => by rw [hxr x hx]; exact hout)
          (fun hk => by
            rcases rayHigh_dichotomy_fiber hA hclsr hk with hin | hout
            · exact Or.inl fun x hx => by rw [hxr x hx]; exact hin
            · exact Or.inr fun x hx => by rw [hxr x hx]; exact hout)
          (fun hk0 => by
            rcases all_dichotomy_fiber hA (hk0 ▸ hclsr) with hin | hout
            · exact Or.inl fun x hx => by rw [hxr x hx]; exact hin
            · exact Or.inr fun x hx => by rw [hxr x hx]; exact hout)
        exact ⟨cells, fun _ => hprops⟩
      rw [List.mem_append] at hb
      rcases hb with hgap | hray
      · -- an adjacent gap: cut-avoiding, band_triviality feeds directly
        obtain ⟨l, u, hlC, huC, hadj, rfl⟩ := mem_gaps_iff.mp hgap
        have havoid : ∀ s ∈ C, s ∉ Set.Ioo l u := by
          intro s hs hsIoo
          rcases hadj.2 s hs with hle | hle
          · exact absurd hsIoo.1 (not_lt.mpr hle)
          · exact absurd hsIoo.2 (not_lt.mpr hle)
        obtain ⟨k, hkN, hsub, hcont', hord', hgraph', hband', hrays', hall'⟩ :=
          htriv l u hadj.1 havoid
        obtain ⟨cells, hprops⟩ := cells_over_uniform hA (.ioo l u) k
          (fun x hx => hsub hx) hcont' hgraph' hband'
          (fun hk => (hrays' hk).1) (fun hk => (hrays' hk).2) hall'
        exact ⟨cells, fun _ => hprops⟩
      · rw [List.mem_cons, List.mem_singleton] at hray
        rcases hray with rfl | rfl
        · -- the lower ray
          have havoid : ∀ t : ℝ, ∀ s ∈ C, s ∉ Set.Ioo t (C.min' hC) := by
            intro t s hs hsIoo
            exact absurd hsIoo.2 (not_lt.mpr (C.min'_le s hs))
          obtain ⟨x₀, hx₀⟩ := exists_lt (C.min' hC)
          obtain ⟨k, hkN, hx₀k⟩ := hpart x₀
          have hcls : ∀ x ∈ Set.Iio (C.min' hC), x ∈ exactSet (fiberFrontier A) k := by
            intro x hx
            obtain ⟨t, ht⟩ := exists_lt (min x x₀)
            have htm : t < C.min' hC :=
              lt_trans (lt_of_lt_of_le ht (min_le_left _ _)) hx
            obtain ⟨k', hk'N, hsub, -, -, -, -, -, -⟩ := htriv t _ htm (havoid t)
            have h1 := hsub ⟨lt_of_lt_of_le ht (min_le_right _ _), hx₀⟩
            have h2 := hsub ⟨lt_of_lt_of_le ht (min_le_left _ _), hx⟩
            have e1 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA x₀)).mp h1
            have e2 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA x₀)).mp hx₀k
            have : k' = k := by omega
            rw [← this]
            exact h2
          have hbundle : ∀ t, t < C.min' hC →
              (∀ j < k, ContinuousOn (nthFn (fiberFrontier A) j)
                (Set.Ioo t (C.min' hC))) ∧
              (∀ j < k,
                (∀ x ∈ Set.Ioo t (C.min' hC),
                  pairFn x (nthFn (fiberFrontier A) j x) ∈ A) ∨
                (∀ x ∈ Set.Ioo t (C.min' hC),
                  pairFn x (nthFn (fiberFrontier A) j x) ∉ A)) ∧
              (∀ j, j + 1 < k →
                (∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ,
                  (nthFn (fiberFrontier A) j x < y ∧
                    y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∈ A) ∨
                (∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ,
                  (nthFn (fiberFrontier A) j x < y ∧
                    y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∉ A)) ∧
              (0 < k →
                ((∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ,
                  y < nthFn (fiberFrontier A) 0 x → pairFn x y ∈ A) ∨
                 (∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ,
                  y < nthFn (fiberFrontier A) 0 x → pairFn x y ∉ A)) ∧
                ((∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ,
                  nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∈ A) ∨
                 (∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ,
                  nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∉ A))) ∧
              (k = 0 →
                (∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ, pairFn x y ∈ A) ∨
                (∀ x ∈ Set.Ioo t (C.min' hC), ∀ y : ℝ, pairFn x y ∉ A)) := by
            intro t ht
            obtain ⟨k', hk'N, hsub, hcont', hord', hgraph', hband', hrays', hall'⟩ :=
              htriv t _ ht (havoid t)
            obtain ⟨p, hp⟩ := exists_between ht
            have e1 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA p)).mp (hsub hp)
            have e2 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA p)).mp
              (hcls p hp.2)
            have hk'eq : k' = k := by omega
            subst hk'eq
            exact ⟨hcont', hgraph', hband', hrays', hall'⟩
          obtain ⟨cells, hprops⟩ := cells_over_uniform hA (.iio (C.min' hC)) k hcls
            (fun j hj x hx => by
              obtain ⟨t, ht⟩ := exists_lt x
              exact (((hbundle t (lt_trans ht hx)).1 j hj).continuousAt
                (Ioo_mem_nhds ht hx)).continuousWithinAt)
            (fun j hj => ray_low_uniform (fun t ht => (hbundle t ht).2.1 j hj))
            (fun j hj => ray_low_uniform (fun t ht => (hbundle t ht).2.2.1 j hj))
            (fun hk => ray_low_uniform (fun t ht => ((hbundle t ht).2.2.2.1 hk).1))
            (fun hk => ray_low_uniform (fun t ht => ((hbundle t ht).2.2.2.1 hk).2))
            (fun hk0 => ray_low_uniform (fun t ht => (hbundle t ht).2.2.2.2 hk0))
          exact ⟨cells, fun _ => hprops⟩
        · -- the upper ray (mirror)
          have havoid : ∀ t : ℝ, ∀ s ∈ C, s ∉ Set.Ioo (C.max' hC) t := by
            intro t s hs hsIoo
            exact absurd hsIoo.1 (not_lt.mpr (C.le_max' s hs))
          obtain ⟨x₀, hx₀⟩ := exists_gt (C.max' hC)
          obtain ⟨k, hkN, hx₀k⟩ := hpart x₀
          have hcls : ∀ x ∈ Set.Ioi (C.max' hC), x ∈ exactSet (fiberFrontier A) k := by
            intro x hx
            obtain ⟨t, ht⟩ := exists_gt (max x x₀)
            have hmt : C.max' hC < t :=
              lt_trans hx (lt_of_le_of_lt (le_max_left _ _) ht)
            obtain ⟨k', hk'N, hsub, -, -, -, -, -, -⟩ := htriv _ t hmt (havoid t)
            have h1 := hsub ⟨hx₀, lt_of_le_of_lt (le_max_right _ _) ht⟩
            have h2 := hsub ⟨hx, lt_of_le_of_lt (le_max_left _ _) ht⟩
            have e1 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA x₀)).mp h1
            have e2 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA x₀)).mp hx₀k
            have : k' = k := by omega
            rw [← this]
            exact h2
          have hbundle : ∀ t, C.max' hC < t →
              (∀ j < k, ContinuousOn (nthFn (fiberFrontier A) j)
                (Set.Ioo (C.max' hC) t)) ∧
              (∀ j < k,
                (∀ x ∈ Set.Ioo (C.max' hC) t,
                  pairFn x (nthFn (fiberFrontier A) j x) ∈ A) ∨
                (∀ x ∈ Set.Ioo (C.max' hC) t,
                  pairFn x (nthFn (fiberFrontier A) j x) ∉ A)) ∧
              (∀ j, j + 1 < k →
                (∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ,
                  (nthFn (fiberFrontier A) j x < y ∧
                    y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∈ A) ∨
                (∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ,
                  (nthFn (fiberFrontier A) j x < y ∧
                    y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∉ A)) ∧
              (0 < k →
                ((∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ,
                  y < nthFn (fiberFrontier A) 0 x → pairFn x y ∈ A) ∨
                 (∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ,
                  y < nthFn (fiberFrontier A) 0 x → pairFn x y ∉ A)) ∧
                ((∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ,
                  nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∈ A) ∨
                 (∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ,
                  nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∉ A))) ∧
              (k = 0 →
                (∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ, pairFn x y ∈ A) ∨
                (∀ x ∈ Set.Ioo (C.max' hC) t, ∀ y : ℝ, pairFn x y ∉ A)) := by
            intro t ht
            obtain ⟨k', hk'N, hsub, hcont', hord', hgraph', hband', hrays', hall'⟩ :=
              htriv _ t ht (havoid t)
            obtain ⟨p, hp⟩ := exists_between ht
            have e1 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA p)).mp (hsub hp)
            have e2 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA p)).mp
              (hcls p hp.1)
            have hk'eq : k' = k := by omega
            subst hk'eq
            exact ⟨hcont', hgraph', hband', hrays', hall'⟩
          obtain ⟨cells, hprops⟩ := cells_over_uniform hA (.ioi (C.max' hC)) k hcls
            (fun j hj x hx => by
              obtain ⟨t, ht⟩ := exists_gt x
              exact (((hbundle t (lt_trans hx ht)).1 j hj).continuousAt
                (Ioo_mem_nhds hx ht)).continuousWithinAt)
            (fun j hj => ray_high_uniform (fun t ht => (hbundle t ht).2.1 j hj))
            (fun j hj => ray_high_uniform (fun t ht => (hbundle t ht).2.2.1 j hj))
            (fun hk => ray_high_uniform (fun t ht => ((hbundle t ht).2.2.2.1 hk).1))
            (fun hk => ray_high_uniform (fun t ht => ((hbundle t ht).2.2.2.1 hk).2))
            (fun hk0 => ray_high_uniform (fun t ht => (hbundle t ht).2.2.2.2 hk0))
          exact ⟨cells, fun _ => hprops⟩
    · -- C = ∅: the whole line is one base
      rw [baseCells, dif_neg hC] at hb
      rw [List.mem_singleton] at hb
      subst hb
      have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      have havoid : ∀ t u : ℝ, ∀ s ∈ C, s ∉ Set.Ioo t u := by
        intro t u s hs
        rw [hCempty] at hs
        exact absurd hs (Finset.notMem_empty s)
      obtain ⟨k, hkN, hx₀k⟩ := hpart 0
      have hcls : ∀ x : ℝ, x ∈ exactSet (fiberFrontier A) k := by
        intro x
        obtain ⟨t, ht⟩ := exists_lt (min x 0)
        obtain ⟨u, hu⟩ := exists_gt (max x 0)
        have htu : t < u := lt_trans (lt_of_lt_of_le ht
          (le_trans (min_le_left _ _) (le_max_left _ _))) hu
        obtain ⟨k', hk'N, hsub, -, -, -, -, -, -⟩ := htriv t u htu (havoid t u)
        have h1 := hsub ⟨lt_of_lt_of_le ht (min_le_right _ _),
          lt_of_le_of_lt (le_max_right _ _) hu⟩
        have h2 := hsub ⟨lt_of_lt_of_le ht (min_le_left _ _),
          lt_of_le_of_lt (le_max_left _ _) hu⟩
        have e1 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA 0)).mp h1
        have e2 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA 0)).mp hx₀k
        have : k' = k := by omega
        rw [← this]
        exact h2
      have hbundle : ∀ t u : ℝ, t < u →
          (∀ j < k, ContinuousOn (nthFn (fiberFrontier A) j) (Set.Ioo t u)) ∧
          (∀ j < k,
            (∀ x ∈ Set.Ioo t u, pairFn x (nthFn (fiberFrontier A) j x) ∈ A) ∨
            (∀ x ∈ Set.Ioo t u, pairFn x (nthFn (fiberFrontier A) j x) ∉ A)) ∧
          (∀ j, j + 1 < k →
            (∀ x ∈ Set.Ioo t u, ∀ y : ℝ, (nthFn (fiberFrontier A) j x < y ∧
              y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∈ A) ∨
            (∀ x ∈ Set.Ioo t u, ∀ y : ℝ, (nthFn (fiberFrontier A) j x < y ∧
              y < nthFn (fiberFrontier A) (j+1) x) → pairFn x y ∉ A)) ∧
          (0 < k →
            ((∀ x ∈ Set.Ioo t u, ∀ y : ℝ,
              y < nthFn (fiberFrontier A) 0 x → pairFn x y ∈ A) ∨
             (∀ x ∈ Set.Ioo t u, ∀ y : ℝ,
              y < nthFn (fiberFrontier A) 0 x → pairFn x y ∉ A)) ∧
            ((∀ x ∈ Set.Ioo t u, ∀ y : ℝ,
              nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∈ A) ∨
             (∀ x ∈ Set.Ioo t u, ∀ y : ℝ,
              nthFn (fiberFrontier A) (k-1) x < y → pairFn x y ∉ A))) ∧
          (k = 0 →
            (∀ x ∈ Set.Ioo t u, ∀ y : ℝ, pairFn x y ∈ A) ∨
            (∀ x ∈ Set.Ioo t u, ∀ y : ℝ, pairFn x y ∉ A)) := by
        intro t u htu
        obtain ⟨k', hk'N, hsub, hcont', hord', hgraph', hband', hrays', hall'⟩ :=
          htriv t u htu (havoid t u)
        obtain ⟨p, hp⟩ := exists_between htu
        have e1 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA p)).mp (hsub hp)
        have e2 := (mem_exactSet_iff (fiberFrontier_fiber_finite hA p)).mp (hcls p)
        have hk'eq : k' = k := by omega
        subst hk'eq
        exact ⟨hcont', hgraph', hband', hrays', hall'⟩
      obtain ⟨cells, hprops⟩ := cells_over_uniform hA .univ k
        (fun x _ => hcls x)
        (fun j hj x _ => by
          obtain ⟨t, ht⟩ := exists_lt x
          obtain ⟨u, hu⟩ := exists_gt x
          exact (((hbundle t u (lt_trans ht hu)).1 j hj).continuousAt
            (Ioo_mem_nhds ht hu)).continuousWithinAt)
        (fun j hj => by
          rcases univ_uniform (fun t u htu => (hbundle t u htu).2.1 j hj) with hin | hout
          · exact Or.inl fun x _ => hin x
          · exact Or.inr fun x _ => hout x)
        (fun j hj => by
          rcases univ_uniform (fun t u htu => (hbundle t u htu).2.2.1 j hj)
            with hin | hout
          · exact Or.inl fun x _ => hin x
          · exact Or.inr fun x _ => hout x)
        (fun hk => by
          rcases univ_uniform (fun t u htu => ((hbundle t u htu).2.2.2.1 hk).1)
            with hin | hout
          · exact Or.inl fun x _ => hin x
          · exact Or.inr fun x _ => hout x)
        (fun hk => by
          rcases univ_uniform (fun t u htu => ((hbundle t u htu).2.2.2.1 hk).2)
            with hin | hout
          · exact Or.inl fun x _ => hin x
          · exact Or.inr fun x _ => hout x)
        (fun hk0 => by
          rcases univ_uniform (fun t u htu => (hbundle t u htu).2.2.2.2 hk0)
            with hin | hout
          · exact Or.inl fun x _ => hin x
          · exact Or.inr fun x _ => hout x)
      exact ⟨cells, fun _ => hprops⟩
  choose cellsF hcellsF using hover
  refine ⟨(baseCells C).flatMap cellsF, ?_, ?_, ?_, ?_⟩
  · -- covers
    intro h
    obtain ⟨b, hbmem, hbx⟩ := baseCells_covers C (h 0)
    obtain ⟨-, hcov, -, -, -⟩ := hcellsF b hbmem
    obtain ⟨c, hc, hch⟩ := hcov h hbx
    exact ⟨c, List.mem_flatMap.mpr ⟨b, hbmem, hc⟩, hch⟩
  · -- pairwise
    refine pairwise_flatMap_of (fun b hb => (hcellsF b hb).2.2.1) ?_
    refine pairwise_imp_of_mem ?_ (baseCells_pairwise C)
    intro b hb b' hb' hdis c hc c' hc'
    rw [Set.disjoint_left]
    intro h hch hch'
    have h1 := Cell₂.base_mem hch
    have h2 := Cell₂.base_mem hch'
    rw [(hcellsF b hb).1 c hc] at h1
    rw [(hcellsF b' hb').1 c' hc'] at h2
    exact Set.disjoint_left.mp hdis h1 h2
  · -- adapted
    intro c hc
    obtain ⟨b, hb, hcb⟩ := List.mem_flatMap.mp hc
    exact (hcellsF b hb).2.2.2.1 c hcb
  · -- well-formed
    intro c hc
    obtain ⟨b, hb, hcb⟩ := List.mem_flatMap.mp hc
    exact (hcellsF b hb).2.2.2.2 c hcb

/-- **CDT₂, union form**: membership in `A` is membership in one of its inside-cells. -/
theorem cell_decomposition_mem (hA : S.Definable A) :
    ∃ cells : List Cell₂, IsCellDecomp cells A ∧
      ∀ h : Fin 2 → ℝ, h ∈ A ↔ ∃ c ∈ cells, c.toSet ⊆ A ∧ h ∈ c.toSet := by
  obtain ⟨cells, hdec⟩ := cell_decomposition hA
  refine ⟨cells, hdec, fun h => ⟨fun hh => ?_, fun ⟨c, _, hsub, hch⟩ => hsub hch⟩⟩
  obtain ⟨c, hc, hch⟩ := hdec.covers h
  rcases hdec.adapted c hc with hsub | hdis
  · exact ⟨c, hc, hsub, hch⟩
  · exact absurd hh (Set.disjoint_left.mp hdis hch)

end Sundog.OMinimalAbstract
