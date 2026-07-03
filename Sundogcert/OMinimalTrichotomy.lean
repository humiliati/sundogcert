/-
# O-min lane R4-C1a: toolkit riders — intervals inside infinite tame sets, and the pointwise
eventual-sign trichotomy.

Two riders on the rung-1/2 machinery, feeding the Monotonicity Theorem:

- **`tame_infinite_contains_Ioo`**: an infinite tame set contains an open interval — rung 2's
  normal form leaves an infinite part in the open-interval pieces, and a nonempty open set
  contains a ball.
- **`eventual_right_sign` / `eventual_left_sign`**: for a definable `φ` and *any* point `x`,
  `φ` has an eventual sign on a right (left) window of `x` — the three comparison sets
  `{y | φ y ≷/= φ x}` are tame (parametric only in the real `φ x`), a window past `x` avoids
  their finitely many frontier points (`exists_right_window`), and `preconnected_split` forces
  each set to be full-or-empty on the window; the midpoint shows one is full.

Also fills the R4-A payoff gap: `tame_sublevelSet` (from super + level by tame booleans).

**Honest fence.** Pointwise riders only: the sign *partition* of the line, the gluing lemmas,
and the mixed-sign kills are C1b–C1d.
-/
import Sundogcert.OMinimalFormula

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalNormalForm

/-! ### An infinite tame set contains an interval -/

/-- **Infinite tame sets contain open intervals** — the o-minimal dichotomy in working form:
a tame set is finite or somewhere dense. -/
theorem tame_infinite_contains_Ioo {T : Set ℝ} (hT : Tame T) (hinf : T.Infinite) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ T := by
  obtain ⟨P, J, hJ, rfl⟩ := normalForm_of_tame hT
  have hUinf : (⋃₀ (↑J : Set (Set ℝ))).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact hinf (P.finite_toSet.union hfin)
  obtain ⟨x, hx⟩ := hUinf.nonempty
  obtain ⟨j, hjJ, hxj⟩ := Set.mem_sUnion.mp hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hJ j (Finset.mem_coe.mp hjJ)).1 x hxj
  refine ⟨x - ε, x + ε, by linarith, ?_⟩
  intro y hy
  rw [Set.mem_Ioo] at hy
  have hyj : y ∈ j := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  exact Set.mem_union_right _ (Set.mem_sUnion.mpr ⟨j, hjJ, hyj⟩)

/-! ### The sublevel gap-fill -/

/-- Strict sublevel sets of definable functions are tame (complement of super ∪ level). -/
theorem OMinStructure.DefinableFun.tame_sublevelSet {S : OMinStructure} {φ : ℝ → ℝ}
    (hφ : S.DefinableFun φ) (r : ℝ) : Tame {x : ℝ | φ x < r} := by
  have h := tame_compl (tame_union (hφ.tame_superlevelSet S r) (hφ.tame_levelSet S r))
  have e : ({x : ℝ | r < φ x} ∪ {x : ℝ | φ x = r})ᶜ = {x : ℝ | φ x < r} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy (φ z) r with h' | h' | h'
      · exact h'
      · exact absurd h' h2
      · exact absurd h' h1
    · intro h'
      exact ⟨by linarith, by linarith⟩
  rwa [e] at h

/-! ### Frontier-avoiding windows -/

/-- Past any point there is a right window avoiding any finite set. -/
theorem exists_right_window {F : Set ℝ} (hF : F.Finite) (x : ℝ) :
    ∃ v : ℝ, x < v ∧ ∀ y ∈ Set.Ioo x v, y ∉ F := by
  classical
  by_cases hne : (F ∩ Set.Ioi x).Nonempty
  · have hGfin : (F ∩ Set.Ioi x).Finite := hF.inter_of_left _
    have hGne : hGfin.toFinset.Nonempty := hGfin.toFinset_nonempty.mpr hne
    refine ⟨hGfin.toFinset.min' hGne, ?_, ?_⟩
    · have hmem := hGfin.toFinset.min'_mem hGne
      rw [Set.Finite.mem_toFinset] at hmem
      exact hmem.2
    · intro y hy hyF
      rw [Set.mem_Ioo] at hy
      have hyG : y ∈ hGfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hyF, hy.1⟩
      exact absurd (hGfin.toFinset.min'_le y hyG) (not_le.mpr hy.2)
  · refine ⟨x + 1, by linarith, ?_⟩
    intro y hy hyF
    rw [Set.mem_Ioo] at hy
    exact hne ⟨y, hyF, hy.1⟩

/-- Before any point there is a left window avoiding any finite set. -/
theorem exists_left_window {F : Set ℝ} (hF : F.Finite) (x : ℝ) :
    ∃ u : ℝ, u < x ∧ ∀ y ∈ Set.Ioo u x, y ∉ F := by
  classical
  by_cases hne : (F ∩ Set.Iio x).Nonempty
  · have hGfin : (F ∩ Set.Iio x).Finite := hF.inter_of_left _
    have hGne : hGfin.toFinset.Nonempty := hGfin.toFinset_nonempty.mpr hne
    refine ⟨hGfin.toFinset.max' hGne, ?_, ?_⟩
    · have hmem := hGfin.toFinset.max'_mem hGne
      rw [Set.Finite.mem_toFinset] at hmem
      exact hmem.2
    · intro y hy hyF
      rw [Set.mem_Ioo] at hy
      have hyG : y ∈ hGfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hyF, hy.2⟩
      exact absurd (hGfin.toFinset.le_max' y hyG) (not_le.mpr hy.1)
  · refine ⟨x - 1, by linarith, ?_⟩
    intro y hy hyF
    rw [Set.mem_Ioo] at hy
    exact hne ⟨y, hyF, hy.2⟩

/-! ### The pointwise eventual-sign trichotomies -/

/-- **The right-sign trichotomy**: a definable function has an eventual sign relative to `φ x`
on some right window of every point — the three comparison sets are tame, a window avoids
their frontiers, `preconnected_split` makes each full-or-empty, and the midpoint picks one. -/
theorem eventual_right_sign {S : OMinStructure} {φ : ℝ → ℝ}
    (hφ : S.DefinableFun φ) (x : ℝ) :
    (∃ v, x < v ∧ ∀ y, x < y → y < v → φ x < φ y) ∨
    (∃ v, x < v ∧ ∀ y, x < y → y < v → φ y < φ x) ∨
    (∃ v, x < v ∧ ∀ y, x < y → y < v → φ y = φ x) := by
  have hgt : Tame {y : ℝ | φ x < φ y} := hφ.tame_superlevelSet S (φ x)
  have hlt : Tame {y : ℝ | φ y < φ x} := hφ.tame_sublevelSet (φ x)
  have heq0 : Tame {y : ℝ | φ y = φ x} := hφ.tame_levelSet S (φ x)
  have hF : (frontier {y : ℝ | φ x < φ y} ∪ frontier {y : ℝ | φ y < φ x}
      ∪ frontier {y : ℝ | φ y = φ x}).Finite := (hgt.union hlt).union heq0
  obtain ⟨v, hxv, hwin⟩ := exists_right_window hF x
  have hsplit : ∀ A : Set ℝ, frontier A ⊆ frontier {y : ℝ | φ x < φ y}
      ∪ frontier {y : ℝ | φ y < φ x} ∪ frontier {y : ℝ | φ y = φ x} →
      Set.Ioo x v ⊆ A ∨ Set.Ioo x v ∩ A = ∅ := by
    intro A hA
    apply preconnected_split Set.ordConnected_Ioo.isPreconnected
    intro y hy hyfr
    exact hwin y hy (hA hyfr)
  have hmid : (x + v) / 2 ∈ Set.Ioo x v := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  rcases hsplit {y : ℝ | φ x < φ y}
      (fun z hz => Set.mem_union_left _ (Set.mem_union_left _ hz)) with hfull | hempGt
  · exact Or.inl ⟨v, hxv, fun y h1 h2 => hfull ⟨h1, h2⟩⟩
  rcases hsplit {y : ℝ | φ y < φ x}
      (fun z hz => Set.mem_union_left _ (Set.mem_union_right _ hz)) with hfull | hempLt
  · exact Or.inr (Or.inl ⟨v, hxv, fun y h1 h2 => hfull ⟨h1, h2⟩⟩)
  rcases hsplit {y : ℝ | φ y = φ x}
      (fun z hz => Set.mem_union_right _ hz) with hfull | hempEq
  · exact Or.inr (Or.inr ⟨v, hxv, fun y h1 h2 => hfull ⟨h1, h2⟩⟩)
  exfalso
  rcases lt_trichotomy (φ x) (φ ((x + v) / 2)) with h' | h' | h'
  · have hc : (x + v) / 2 ∈ Set.Ioo x v ∩ {y : ℝ | φ x < φ y} := ⟨hmid, h'⟩
    rw [hempGt] at hc
    exact hc
  · have hc : (x + v) / 2 ∈ Set.Ioo x v ∩ {y : ℝ | φ y = φ x} := ⟨hmid, h'.symm⟩
    rw [hempEq] at hc
    exact hc
  · have hc : (x + v) / 2 ∈ Set.Ioo x v ∩ {y : ℝ | φ y < φ x} := ⟨hmid, h'⟩
    rw [hempLt] at hc
    exact hc

/-- **The left-sign trichotomy** (mirror). -/
theorem eventual_left_sign {S : OMinStructure} {φ : ℝ → ℝ}
    (hφ : S.DefinableFun φ) (x : ℝ) :
    (∃ u, u < x ∧ ∀ y, u < y → y < x → φ y < φ x) ∨
    (∃ u, u < x ∧ ∀ y, u < y → y < x → φ x < φ y) ∨
    (∃ u, u < x ∧ ∀ y, u < y → y < x → φ y = φ x) := by
  have hgt : Tame {y : ℝ | φ x < φ y} := hφ.tame_superlevelSet S (φ x)
  have hlt : Tame {y : ℝ | φ y < φ x} := hφ.tame_sublevelSet (φ x)
  have heq0 : Tame {y : ℝ | φ y = φ x} := hφ.tame_levelSet S (φ x)
  have hF : (frontier {y : ℝ | φ x < φ y} ∪ frontier {y : ℝ | φ y < φ x}
      ∪ frontier {y : ℝ | φ y = φ x}).Finite := (hgt.union hlt).union heq0
  obtain ⟨u, hux, hwin⟩ := exists_left_window hF x
  have hsplit : ∀ A : Set ℝ, frontier A ⊆ frontier {y : ℝ | φ x < φ y}
      ∪ frontier {y : ℝ | φ y < φ x} ∪ frontier {y : ℝ | φ y = φ x} →
      Set.Ioo u x ⊆ A ∨ Set.Ioo u x ∩ A = ∅ := by
    intro A hA
    apply preconnected_split Set.ordConnected_Ioo.isPreconnected
    intro y hy hyfr
    exact hwin y hy (hA hyfr)
  have hmid : (u + x) / 2 ∈ Set.Ioo u x := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  rcases hsplit {y : ℝ | φ y < φ x}
      (fun z hz => Set.mem_union_left _ (Set.mem_union_right _ hz)) with hfull | hempLt
  · exact Or.inl ⟨u, hux, fun y h1 h2 => hfull ⟨h1, h2⟩⟩
  rcases hsplit {y : ℝ | φ x < φ y}
      (fun z hz => Set.mem_union_left _ (Set.mem_union_left _ hz)) with hfull | hempGt
  · exact Or.inr (Or.inl ⟨u, hux, fun y h1 h2 => hfull ⟨h1, h2⟩⟩)
  rcases hsplit {y : ℝ | φ y = φ x}
      (fun z hz => Set.mem_union_right _ hz) with hfull | hempEq
  · exact Or.inr (Or.inr ⟨u, hux, fun y h1 h2 => hfull ⟨h1, h2⟩⟩)
  exfalso
  rcases lt_trichotomy (φ x) (φ ((u + x) / 2)) with h' | h' | h'
  · have hc : (u + x) / 2 ∈ Set.Ioo u x ∩ {y : ℝ | φ x < φ y} := ⟨hmid, h'⟩
    rw [hempGt] at hc
    exact hc
  · have hc : (u + x) / 2 ∈ Set.Ioo u x ∩ {y : ℝ | φ y = φ x} := ⟨hmid, h'.symm⟩
    rw [hempEq] at hc
    exact hc
  · have hc : (u + x) / 2 ∈ Set.Ioo u x ∩ {y : ℝ | φ y < φ x} := ⟨hmid, h'⟩
    rw [hempLt] at hc
    exact hc

end Sundog.OMinimalAbstract
