/-
# R4-E: the Pillay–Steinhorn bridge — definable families are NIP.

The bounded form of the Pillay–Steinhorn observation, reachable from CDT₂: in ANY
o-minimal structure, a definable planar set — read as a family of subsets of the line,
`x ↦ {y | pairFn x y ∈ A}` — cannot shatter arbitrarily large finite sets. The bound is
explicit: `2 · (number of cells) + 1`.

- **`ShattersFam`** — the trace-shattering predicate (the combinatorial content of the
  independence property, no model-theoretic syntax).
- **`shatter_le_of_ordConnected_pieces`** — the alternation/pigeonhole core: a family
  whose every member is a union of at most `K` order-connected pieces cannot shatter
  `2K + 2` points (the `K + 1` even-indexed points of a shattered chain would need
  pairwise-distinct pieces, since any two share an excluded odd point between them).
- **`cell₂_fiber_ordConnected`** — cell fibers are order-connected, by band shape.
- **`definable_family_nip`** — the abstract R4-E: cell decomposition bounds every
  fiber by `cells.length` order-connected pieces.
- **`semialgebraic_family_nip` / `semilinear_family_nip`** — the bridge back to the
  approximation lane: polynomial AND piecewise-linear (ReLU-class) families have
  uniformly bounded shattering — VC-finiteness from tameness, through both landed
  structures.
-/
import Sundogcert.SemialgebraicStructure
import Sundogcert.SemilinearStructure

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

/-! ### Shattering -/

/-- The family `Fam` shatters `s`: every subset of `s` is a trace of some member. -/
def ShattersFam (Fam : ℝ → Set ℝ) (s : Finset ℝ) : Prop :=
  ∀ t ⊆ s, ∃ x : ℝ, ∀ z ∈ s, z ∈ Fam x ↔ z ∈ t

theorem shattersFam_mono {Fam : ℝ → Set ℝ} {s s' : Finset ℝ} (hss : s' ⊆ s)
    (h : ShattersFam Fam s) : ShattersFam Fam s' := by
  intro t ht
  obtain ⟨x, hx⟩ := h t (ht.trans hss)
  exact ⟨x, fun z hz => hx z (hss hz)⟩

/-! ### The alternation bound -/

/-- **The combinatorial core.** A family whose members are unions of at most `K`
order-connected pieces cannot shatter more than `2K + 1` points. -/
theorem shatter_le_of_ordConnected_pieces (Fam : ℝ → Set ℝ) (K : ℕ)
    (hFam : ∀ x : ℝ, ∃ pieces : List (Set ℝ), pieces.length ≤ K ∧
      (∀ p ∈ pieces, p.OrdConnected) ∧ Fam x = ⋃ p ∈ pieces, p) :
    ∀ s : Finset ℝ, ShattersFam Fam s → s.card ≤ 2 * K + 1 := by
  classical
  intro s hs
  by_contra hcard
  push Not at hcard
  obtain ⟨s', hs'sub, hs'card⟩ :=
    Finset.exists_subset_card_eq (show 2 * K + 2 ≤ s.card by omega)
  have hsh := shattersFam_mono hs'sub hs
  set e := s'.orderEmbOfFin hs'card with he
  set t : Finset ℝ :=
    (Finset.univ.filter (fun i : Fin (2 * K + 2) => i.val % 2 = 0)).image
      (fun i => e i) with ht
  have htsub : t ⊆ s' := by
    intro z hz
    rw [ht, Finset.mem_image] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact Finset.orderEmbOfFin_mem s' hs'card i
  obtain ⟨x, hx⟩ := hsh t htsub
  obtain ⟨pieces, hlen, hoc, hcover⟩ := hFam x
  have heven : ∀ i : Fin (2 * K + 2), i.val % 2 = 0 → e i ∈ Fam x := by
    intro i hi
    refine (hx _ (Finset.orderEmbOfFin_mem s' hs'card i)).mpr ?_
    rw [ht, Finset.mem_image]
    exact ⟨i, by simp [hi], rfl⟩
  have hodd : ∀ i : Fin (2 * K + 2), i.val % 2 = 1 → e i ∉ Fam x := by
    intro i hi hmem
    have hti := (hx _ (Finset.orderEmbOfFin_mem s' hs'card i)).mp hmem
    rw [ht, Finset.mem_image] at hti
    obtain ⟨j, hj, hji⟩ := hti
    rw [Finset.mem_filter] at hj
    have hj2 := hj.2
    have hji' : j = i := e.injective hji
    subst hji'
    omega
  have hsel : ∀ j : Fin (K + 1), ∃ pi ∈ pieces,
      e ⟨2 * j.val, by omega⟩ ∈ pi := by
    intro j
    have hm := heven ⟨2 * j.val, by omega⟩ (by change 2 * j.val % 2 = 0; omega)
    rw [hcover] at hm
    simpa using hm
  choose φ hφmem hφ using hsel
  have key : ∀ j j' : Fin (K + 1), j < j' → φ j = φ j' → False := by
    intro j j' hlt heq
    have hjj' : j.val < j'.val := hlt
    have h1 : e ⟨2 * j.val, by omega⟩ ∈ φ j := hφ j
    have h2 : e ⟨2 * j'.val, by omega⟩ ∈ φ j := heq ▸ hφ j'
    have hzodd : e ⟨2 * j.val + 1, by omega⟩ ∈ φ j := by
      refine (hoc (φ j) (hφmem j)).out h1 h2 ?_
      constructor
      · exact e.monotone (by
          rw [Fin.mk_le_mk]
          omega)
      · exact e.monotone (by
          rw [Fin.mk_le_mk]
          omega)
    refine hodd ⟨2 * j.val + 1, by omega⟩
      (by change (2 * j.val + 1) % 2 = 1; omega) ?_
    rw [hcover]
    exact Set.mem_biUnion (hφmem j) hzodd
  have hinj : Function.Injective φ := by
    intro j j' hjj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key j j' hlt hjj
    · exact key j' j hlt hjj.symm
  have h1 : (Finset.univ.image φ).card = K + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have h2 : Finset.univ.image φ ⊆ pieces.toFinset := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨j, _, rfl⟩ := hp
    rw [List.mem_toFinset]
    exact hφmem j
  have h3 := Finset.card_le_card h2
  have h4 : pieces.toFinset.card ≤ pieces.length := pieces.toFinset_card_le
  omega

/-! ### Cell fibers are order-connected -/

theorem cell₂_fiber_ordConnected (c : Cell₂) (x : ℝ) :
    Set.OrdConnected {y : ℝ | pairFn x y ∈ c.toSet} := by
  constructor
  intro y₁ h₁ y₂ h₂ z hz
  cases c with
  | graph C f =>
    simp only [Cell₂.toSet, Set.mem_setOf_eq, pairFn_zero, pairFn_one] at h₁ h₂ ⊢
    exact ⟨h₁.1, le_antisymm (h₂.2 ▸ hz.2) (h₁.2 ▸ hz.1)⟩
  | band C f g =>
    simp only [Cell₂.toSet, Set.mem_setOf_eq, pairFn_zero, pairFn_one] at h₁ h₂ ⊢
    exact ⟨h₁.1, lt_of_lt_of_le h₁.2.1 hz.1, lt_of_le_of_lt hz.2 h₂.2.2⟩
  | bandLow C g =>
    simp only [Cell₂.toSet, Set.mem_setOf_eq, pairFn_zero, pairFn_one] at h₁ h₂ ⊢
    exact ⟨h₁.1, lt_of_le_of_lt hz.2 h₂.2⟩
  | bandHigh C f =>
    simp only [Cell₂.toSet, Set.mem_setOf_eq, pairFn_zero, pairFn_one] at h₁ h₂ ⊢
    exact ⟨h₁.1, lt_of_lt_of_le h₁.2 hz.1⟩
  | full C =>
    simp only [Cell₂.toSet, Set.mem_setOf_eq, pairFn_zero] at h₁ ⊢
    exact h₁

/-! ### The abstract bridge -/

/-- **R4-E (Pillay–Steinhorn, bounded form).** In any o-minimal structure, a definable
planar set — as a family of line sets — has uniformly bounded shattering. -/
theorem definable_family_nip (S : OMinStructure) {A : Set (Fin 2 → ℝ)}
    (hA : S.Definable A) :
    ∃ d : ℕ, ∀ s : Finset ℝ,
      ShattersFam (fun x => {y : ℝ | pairFn x y ∈ A}) s → s.card ≤ d := by
  classical
  obtain ⟨cells, hdec⟩ := cell_decomposition (S := S) hA
  refine ⟨2 * cells.length + 1,
    shatter_le_of_ordConnected_pieces _ cells.length ?_⟩
  intro x
  refine ⟨cells.map (fun c =>
    if c.toSet ⊆ A then {y : ℝ | pairFn x y ∈ c.toSet} else ∅), by simp, ?_, ?_⟩
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    by_cases hcA : c.toSet ⊆ A
    · rw [if_pos hcA]
      exact cell₂_fiber_ordConnected c x
    · rw [if_neg hcA]
      exact Set.ordConnected_empty
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, List.mem_map, exists_prop,
      exists_exists_and_eq_and]
    constructor
    · intro hy
      obtain ⟨c, hc, hyc⟩ := hdec.covers (pairFn x y)
      have hcA : c.toSet ⊆ A := by
        rcases hdec.adapted c hc with h | h
        · exact h
        · exact absurd hy (Set.disjoint_left.mp h hyc)
      refine ⟨c, hc, ?_⟩
      rw [if_pos hcA]
      exact hyc
    · rintro ⟨c, hc, hyp⟩
      by_cases hcA : c.toSet ⊆ A
      · rw [if_pos hcA] at hyp
        exact hcA hyp
      · rw [if_neg hcA] at hyp
        simp at hyp

/-! ### The bridge back to the approximation lane -/

/-- Semialgebraic planar families have uniformly bounded shattering. -/
theorem semialgebraic_family_nip {A : Set (Fin 2 → ℝ)}
    (hA : Sundog.TarskiQE.SADef 2 A) :
    ∃ d : ℕ, ∀ s : Finset ℝ,
      ShattersFam (fun x => {y : ℝ | pairFn x y ∈ A}) s → s.card ≤ d :=
  definable_family_nip Sundog.TarskiQE.semialgebraicStructure hA

/-- Semilinear (ReLU-class) planar families have uniformly bounded shattering. -/
theorem semilinear_family_nip {A : Set (Fin 2 → ℝ)}
    (hA : Sundog.SemilinearInstance.semilinearStructure.Definable A) :
    ∃ d : ℕ, ∀ s : Finset ℝ,
      ShattersFam (fun x => {y : ℝ | pairFn x y ∈ A}) s → s.card ≤ d :=
  definable_family_nip Sundog.SemilinearInstance.semilinearStructure hA

end Sundog.OMinimalAbstract
