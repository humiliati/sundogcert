/-
# O-min lane R4-C1d: the mixed-sign kills and THE MONOTONICITY THEOREM.

**The theorem** (`monotonicity_theorem`): for every o-minimal structure `S` and `S`-definable
`φ : ℝ → ℝ`, there is a finite cut-set `F` such that on every `F`-free open interval, `φ` is
constant, strictly increasing, or strictly decreasing — van den Dries Ch. 3 §1 (C1: without
continuity on the pieces; C2 is a later scope). The first theorem of the abstract theory.

**The kills.** C1b's partition leaves one class per gap; the bad class dies by showing
`badSet φ` is **finite**: a bad interval would carry uniform one-sided signs on a subwindow
(the six sign sets are full-or-empty there), and all nine sign combinations are impossible:
- three coherent combos are `locConst`/`locInc`/`locDec` — contradicting badness directly;
- four eq-mixed combos die by short window contradictions (a constant window meets a strict
  one-sided window: `kill_rightEq_left` / `kill_leftEq_right`);
- the two extremum combos (every point a strict neighbor-minimum, or -maximum) die by
  **countability**: strict neighbor-extrema of *any* real function inject into ℚ × ℚ via
  rational witness windows (two extrema sharing a window would each dominate the other), and
  a nonempty open interval is uncountable (`Cardinal.mk_Ioo_real`).

**Honest scope.** The countability kill is ℝ-specific — over a general real closed field (no
countability), van den Dries's constant-or-injective route is needed instead; that refinement
is named, not claimed. Assembly: `F := sign-partition cut-set ∪ badSet`; good gaps glue by
C1c's `rel_propagate` instantiations.
-/
import Sundogcert.OMinimalGluing
import Mathlib.Analysis.Real.Cardinality

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

/-! ### The countability kill -/

/-- Strict neighbor-minima of any real function are countable: each injects its rational
witness window, and two minima sharing a window would each dominate the other. -/
private theorem countable_min_pts (φ : ℝ → ℝ) :
    (rightAbove φ ∩ leftAbove φ).Countable := by
  classical
  have hch : ∀ x : ℝ, ∃ q : ℚ × ℚ, x ∈ rightAbove φ ∩ leftAbove φ →
      (q.1 : ℝ) < x ∧ x < (q.2 : ℝ) ∧
      ∀ y, (q.1 : ℝ) < y → y < (q.2 : ℝ) → y ≠ x → φ x < φ y := by
    intro x
    by_cases hx : x ∈ rightAbove φ ∩ leftAbove φ
    · obtain ⟨⟨v, hv, hR⟩, ⟨u, hu, hL⟩⟩ := hx
      obtain ⟨q1, hq1u, hq1x⟩ := exists_rat_btwn hu
      obtain ⟨q2, hq2x, hq2v⟩ := exists_rat_btwn hv
      refine ⟨(q1, q2), fun _ => ⟨hq1x, hq2x, ?_⟩⟩
      intro y hy1 hy2 hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hL y (hq1u.trans hy1) h
      · exact hR y h (hy2.trans hq2v)
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose f hf using hch
  rw [← Set.countable_coe_iff]
  have hinj : Function.Injective
      (fun p : ↥(rightAbove φ ∩ leftAbove φ) => f p.1) := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ heq
    simp only at heq
    obtain ⟨h1, h2, h3⟩ := hf x hx
    obtain ⟨h1', h2', h3'⟩ := hf x' hx'
    by_contra hne
    have hnexx : x ≠ x' := fun h => hne (Subtype.ext h)
    have hx'win : (((f x).1 : ℝ) < x' ∧ x' < ((f x).2 : ℝ)) := by
      rw [heq]
      exact ⟨h1', h2'⟩
    have hxwin : (((f x').1 : ℝ) < x ∧ x < ((f x').2 : ℝ)) := by
      rw [← heq]
      exact ⟨h1, h2⟩
    have hA : φ x < φ x' := h3 x' hx'win.1 hx'win.2 hnexx.symm
    have hB : φ x' < φ x := h3' x hxwin.1 hxwin.2 hnexx
    linarith
  exact hinj.countable

/-- A nonempty open interval is uncountable (`Cardinal.mk_Ioo_real`). -/
private theorem uncountable_Ioo {a b : ℝ} (h : a < b) : ¬ (Set.Ioo a b).Countable := by
  intro hc
  have h1 := Cardinal.mk_Ioo_real h
  have h2 : Cardinal.mk ↥(Set.Ioo a b) ≤ Cardinal.aleph0 := by
    have := Set.countable_coe_iff.mpr hc
    exact Cardinal.mk_le_aleph0
  rw [h1] at h2
  exact absurd h2 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- The negation mirrors: below-signs for `φ` are above-signs for `-φ`. -/
private theorem rightBelow_eq_neg (φ : ℝ → ℝ) :
    rightBelow φ = rightAbove (fun t => -φ t) := by
  ext x
  simp only [rightBelow, rightAbove, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, fun y h1 h2 => neg_lt_neg (h y h1 h2)⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, fun y h1 h2 => ?_⟩
    have := h y h1 h2
    linarith

private theorem leftBelow_eq_neg (φ : ℝ → ℝ) :
    leftBelow φ = leftAbove (fun t => -φ t) := by
  ext x
  simp only [leftBelow, leftAbove, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, fun y h1 h2 => neg_lt_neg (h y h1 h2)⟩
  · rintro ⟨u, hu, h⟩
    refine ⟨u, hu, fun y h1 h2 => ?_⟩
    have := h y h1 h2
    linarith

/-- Every point a strict neighbor-minimum on an interval: impossible. -/
private theorem kill_min {φ : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (h1 : Set.Ioo c d ⊆ rightAbove φ) (h2 : Set.Ioo c d ⊆ leftAbove φ) : False :=
  uncountable_Ioo hcd ((countable_min_pts φ).mono
    (Set.subset_inter h1 h2))

/-- Every point a strict neighbor-maximum on an interval: impossible (apply the minimum kill
to `-φ`). -/
private theorem kill_max {φ : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (h1 : Set.Ioo c d ⊆ rightBelow φ) (h2 : Set.Ioo c d ⊆ leftBelow φ) : False := by
  rw [rightBelow_eq_neg] at h1
  rw [leftBelow_eq_neg] at h2
  exact kill_min hcd h1 h2

/-! ### The eq-mixed kills -/

/-- A right-constant window meets a strict left window: impossible on an interval. -/
private theorem kill_rightEq_left {φ : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hRE : Set.Ioo c d ⊆ rightEq φ)
    (hL : Set.Ioo c d ⊆ leftAbove φ ∨ Set.Ioo c d ⊆ leftBelow φ) : False := by
  have hs : (c + d) / 2 ∈ Set.Ioo c d := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨v, hsv, hconst⟩ := hRE hs
  set s := (c + d) / 2 with hsdef
  have hsmin : s < min v d := lt_min hsv hs.2
  have hts : s < (s + min v d) / 2 := by linarith
  have htmin : (s + min v d) / 2 < min v d := by linarith
  set t := (s + min v d) / 2 with htdef
  have htIoo : t ∈ Set.Ioo c d := by
    rw [Set.mem_Ioo]
    exact ⟨lt_trans hs.1 hts, lt_of_lt_of_le htmin (min_le_right _ _)⟩
  have htv : t < v := lt_of_lt_of_le htmin (min_le_left _ _)
  have hφt : φ t = φ s := hconst t hts htv
  -- the strict left window of t, probed inside (s, t)
  have hkill : ∀ u₀ : ℝ, u₀ < t → ∀ P : ℝ → ℝ → Prop,
      (∀ y, u₀ < y → y < t → P (φ t) (φ y)) →
      (∀ p q : ℝ, P p q → p ≠ q) → False := by
    intro u₀ hu₀t P hP hPne
    have hmax : max u₀ s < t := max_lt hu₀t hts
    have hy : (max u₀ s + t) / 2 ∈ Set.Ioo (max u₀ s) t := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    have hys : s < (max u₀ s + t) / 2 :=
      lt_of_le_of_lt (le_max_right u₀ s) hy.1
    have hyv : (max u₀ s + t) / 2 < v := lt_trans hy.2 htv
    have hφy : φ ((max u₀ s + t) / 2) = φ s := hconst _ hys hyv
    have hne := hPne _ _ (hP _ (lt_of_le_of_lt (le_max_left u₀ s) hy.1) hy.2)
    rw [hφy, hφt] at hne
    exact hne rfl
  rcases hL with hLA | hLB
  · obtain ⟨u₀, hu₀, habove⟩ := hLA htIoo
    exact hkill u₀ hu₀ (fun p q => p < q) habove (fun p q h => ne_of_lt h)
  · obtain ⟨u₀, hu₀, hbelow⟩ := hLB htIoo
    exact hkill u₀ hu₀ (fun p q => q < p) hbelow (fun p q h => ne_of_gt h)

/-- A left-constant window meets a strict right window: impossible on an interval. -/
private theorem kill_leftEq_right {φ : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hLE : Set.Ioo c d ⊆ leftEq φ)
    (hR : Set.Ioo c d ⊆ rightAbove φ ∨ Set.Ioo c d ⊆ rightBelow φ) : False := by
  have hs : (c + d) / 2 ∈ Set.Ioo c d := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨u, hus, hconst⟩ := hLE hs
  set s := (c + d) / 2 with hsdef
  have hsmax : max u c < s := max_lt hus hs.1
  have hts : (max u c + s) / 2 < s := by linarith
  have htmax : max u c < (max u c + s) / 2 := by linarith
  set t := (max u c + s) / 2 with htdef
  have htIoo : t ∈ Set.Ioo c d := by
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_lt (le_max_right u c) htmax, lt_trans hts hs.2⟩
  have htu : u < t := lt_of_le_of_lt (le_max_left u c) htmax
  have hφt : φ t = φ s := hconst t htu hts
  have hkill : ∀ v₀ : ℝ, t < v₀ → ∀ P : ℝ → ℝ → Prop,
      (∀ y, t < y → y < v₀ → P (φ t) (φ y)) →
      (∀ p q : ℝ, P p q → p ≠ q) → False := by
    intro v₀ htv₀ P hP hPne
    have hmin : t < min v₀ s := lt_min htv₀ hts
    have hy : (t + min v₀ s) / 2 ∈ Set.Ioo t (min v₀ s) := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    have hyu : u < (t + min v₀ s) / 2 := lt_trans htu hy.1
    have hys : (t + min v₀ s) / 2 < s :=
      lt_of_lt_of_le hy.2 (min_le_right _ _)
    have hφy : φ ((t + min v₀ s) / 2) = φ s := hconst _ hyu hys
    have hne := hPne _ _ (hP _ hy.1 (lt_of_lt_of_le hy.2 (min_le_left _ _)))
    rw [hφy, hφt] at hne
    exact hne rfl
  rcases hR with hRA | hRB
  · obtain ⟨v₀, hv₀, habove⟩ := hRA htIoo
    exact hkill v₀ hv₀ (fun p q => p < q) habove (fun p q h => ne_of_lt h)
  · obtain ⟨v₀, hv₀, hbelow⟩ := hRB htIoo
    exact hkill v₀ hv₀ (fun p q => q < p) hbelow (fun p q h => ne_of_gt h)

/-! ### Electing the uniform signs -/

/-- Three covering sets, each full-or-empty on a window: one is full. -/
private theorem elect3 {A B C : Set ℝ} {c d : ℝ} (hcd : c < d)
    (hcover : A ∪ B ∪ C = Set.univ)
    (hA : Set.Ioo c d ⊆ A ∨ Set.Ioo c d ∩ A = ∅)
    (hB : Set.Ioo c d ⊆ B ∨ Set.Ioo c d ∩ B = ∅)
    (hC : Set.Ioo c d ⊆ C ∨ Set.Ioo c d ∩ C = ∅) :
    Set.Ioo c d ⊆ A ∨ Set.Ioo c d ⊆ B ∨ Set.Ioo c d ⊆ C := by
  rcases hA with hfull | hempA
  · exact Or.inl hfull
  rcases hB with hfull | hempB
  · exact Or.inr (Or.inl hfull)
  rcases hC with hfull | hempC
  · exact Or.inr (Or.inr hfull)
  exfalso
  have hmid : (c + d) / 2 ∈ Set.Ioo c d := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hcov : (c + d) / 2 ∈ A ∪ B ∪ C := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hcov with (h | h) | h
  · have hc' : (c + d) / 2 ∈ Set.Ioo c d ∩ A := ⟨hmid, h⟩
    rw [hempA] at hc'
    exact hc'
  · have hc' : (c + d) / 2 ∈ Set.Ioo c d ∩ B := ⟨hmid, h⟩
    rw [hempB] at hc'
    exact hc'
  · have hc' : (c + d) / 2 ∈ Set.Ioo c d ∩ C := ⟨hmid, h⟩
    rw [hempC] at hc'
    exact hc'

/-! ### The bad set is finite -/

/-- **The kill (C1d core): the bad set of a definable function is finite.** A bad interval
would carry uniform one-sided signs on a frontier-free subwindow; all nine combinations are
impossible. -/
theorem badSet_finite {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) :
    (badSet φ).Finite := by
  classical
  by_contra hinf
  obtain ⟨a, b, hab, hsub⟩ := tame_infinite_contains_Ioo (tame_badSet hφ) hinf
  -- a frontier-free subwindow (c, d) of (a, b)
  have hF : (frontier (rightAbove φ) ∪ frontier (rightBelow φ) ∪ frontier (rightEq φ)
      ∪ frontier (leftBelow φ) ∪ frontier (leftAbove φ) ∪ frontier (leftEq φ)).Finite :=
    (((((tame_rightAbove hφ).union (tame_rightBelow hφ)).union (tame_rightEq hφ)).union
      (tame_leftBelow hφ)).union (tame_leftAbove hφ)).union (tame_leftEq hφ)
  have hcab : a < (a + b) / 2 := by linarith
  have hcbb : (a + b) / 2 < b := by linarith
  obtain ⟨v, hv, hwin⟩ := exists_right_window hF ((a + b) / 2)
  set c := (a + b) / 2 with hcdef
  set d := min v b with hddef
  have hcd : c < d := lt_min hv hcbb
  have hsubab : Set.Ioo c d ⊆ Set.Ioo a b := by
    intro y hy
    rw [Set.mem_Ioo] at hy ⊢
    exact ⟨lt_trans hcab hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩
  have havoid : ∀ y ∈ Set.Ioo c d, ∀ {X : Set ℝ},
      frontier X ⊆ frontier (rightAbove φ) ∪ frontier (rightBelow φ) ∪ frontier (rightEq φ)
        ∪ frontier (leftBelow φ) ∪ frontier (leftAbove φ) ∪ frontier (leftEq φ) →
      y ∉ frontier X := by
    intro y hy X hX hyfr
    rw [Set.mem_Ioo] at hy
    exact hwin y (by rw [Set.mem_Ioo]; exact ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩)
      (hX hyfr)
  -- full-or-empty for each of the six on (c, d)
  have hsplit : ∀ X : Set ℝ,
      frontier X ⊆ frontier (rightAbove φ) ∪ frontier (rightBelow φ) ∪ frontier (rightEq φ)
        ∪ frontier (leftBelow φ) ∪ frontier (leftAbove φ) ∪ frontier (leftEq φ) →
      Set.Ioo c d ⊆ X ∨ Set.Ioo c d ∩ X = ∅ := by
    intro X hX
    exact full_or_empty_on_window (fun y hy => havoid y hy hX)
  -- elect the uniform right sign
  have hR := elect3 hcd (right_sign_cover hφ)
    (hsplit _ (fun z hz => Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_left _ hz))))))
    (hsplit _ (fun z hz => Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (Set.mem_union_right _ hz))))))
    (hsplit _ (fun z hz => Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ hz)))))
  -- elect the uniform left sign
  have hL := elect3 hcd (left_sign_cover hφ)
    (hsplit _ (fun z hz => Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ hz))))
    (hsplit _ (fun z hz => Set.mem_union_left _ (Set.mem_union_right _ hz)))
    (hsplit _ (fun z hz => Set.mem_union_right _ hz))
  -- all points of (c, d) are bad
  have hbad : ∀ x ∈ Set.Ioo c d, x ∈ badSet φ := fun x hx => hsub (hsubab hx)
  have hnotgood : ∀ x ∈ Set.Ioo c d, x ∉ locConst φ ∪ locInc φ ∪ locDec φ := by
    intro x hx hgood
    exact hbad x hx hgood
  -- nine combinations
  rcases hR with hRA | hRB | hRE
  · rcases hL with hLB | hLA | hLE
    · -- (above, below) = locInc: contradiction with badness
      have hmid : (c + d) / 2 ∈ Set.Ioo c d := by
        rw [Set.mem_Ioo]
        constructor <;> linarith
      exact hnotgood _ hmid (Set.mem_union_left _ (Set.mem_union_right _
        ⟨hRA hmid, hLB hmid⟩))
    · exact kill_min hcd hRA hLA
    · exact kill_leftEq_right hcd hLE (Or.inl hRA)
  · rcases hL with hLB | hLA | hLE
    · exact kill_max hcd hRB hLB
    · -- (below, above) = locDec
      have hmid : (c + d) / 2 ∈ Set.Ioo c d := by
        rw [Set.mem_Ioo]
        constructor <;> linarith
      exact hnotgood _ hmid (Set.mem_union_right _ ⟨hRB hmid, hLA hmid⟩)
    · exact kill_leftEq_right hcd hLE (Or.inr hRB)
  · rcases hL with hLB | hLA | hLE
    · exact kill_rightEq_left hcd hRE (Or.inr hLB)
    · exact kill_rightEq_left hcd hRE (Or.inl hLA)
    · -- (eq, eq) = locConst
      have hmid : (c + d) / 2 ∈ Set.Ioo c d := by
        rw [Set.mem_Ioo]
        constructor <;> linarith
      exact hnotgood _ hmid (Set.mem_union_left _ (Set.mem_union_left _
        ⟨hRE hmid, hLE hmid⟩))

/-! ### THE MONOTONICITY THEOREM -/

/-- **The Monotonicity Theorem (C1).** For every o-minimal structure and definable
`φ : ℝ → ℝ`: a finite cut-set outside of which `φ` is piecewise constant, strictly increasing,
or strictly decreasing — van den Dries Ch. 3 §1, without continuity (C2). The first theorem of
the abstract theory, machine-checked. -/
theorem monotonicity_theorem {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) :
    ∃ F : Finset ℝ, ∀ a b : ℝ, a < b → (∀ s ∈ F, s ∉ Set.Ioo a b) →
      (∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, φ x = φ y) ∨
      StrictMonoOn φ (Set.Ioo a b) ∨ StrictAntiOn φ (Set.Ioo a b) := by
  classical
  obtain ⟨F₀, hF₀⟩ := sign_partition hφ
  have hbadfin := badSet_finite hφ
  refine ⟨F₀ ∪ hbadfin.toFinset, ?_⟩
  intro a b hab hgap
  have hgap₀ : ∀ s ∈ F₀, s ∉ Set.Ioo a b := fun s hs =>
    hgap s (Finset.mem_union_left _ hs)
  have hnobad : ∀ x ∈ Set.Ioo a b, x ∉ badSet φ := by
    intro x hx hxbad
    exact hgap x (Finset.mem_union_right _ (by
      rw [Set.Finite.mem_toFinset]
      exact hxbad)) hx
  rcases hF₀ a b hab hgap₀ with hC | hI | hD | hB
  · exact Or.inl (eqOn_of_locConst hC)
  · exact Or.inr (Or.inl (strictMonoOn_of_locInc hI))
  · exact Or.inr (Or.inr (strictAntiOn_of_locDec hD))
  · exfalso
    have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    exact hnobad _ hmid (hB hmid)

end Sundog.OMinimalAbstract
