/-
# O-min lane R4-C1c: the gluing lemmas — neighbor-sense local behavior globalizes.

Pure real analysis, no definability and **no continuity**: on an open interval where every
point is neighbor-sense locally increasing (left neighbors below, right neighbors above), the
function is strictly increasing on the whole interval — and likewise decreasing and constant.

**One engine.** The sup-chaining argument uses nothing about the comparison except
transitivity, so it is proved once (`rel_propagate`) over an abstract transitive relation `R`:
propagate `R (φ u) (φ ·)` rightward through the set
`T = {z ∈ [u,w] | ∀ t ∈ (u, z], R (φ u) (φ t)}` — the sup `s` of `T` is itself absorbed (chain
through a member of `T` inside `s`'s left window), and `s < w` is impossible (`s`'s right
window pushes `T` past the sup). Instantiations: `R = (· < ·)` (increasing), `R p q = q < p`
(decreasing), `R p q = (q = p)` (constant) — the three window shapes are exactly C1b's
`rightAbove ∩ leftBelow`, `rightBelow ∩ leftAbove`, `rightEq ∩ leftEq`.

The two-sidedness is essential (the scout's sawtooth counterexample kills the one-sided
version); mathlib recon found no local-to-global monotonicity lemma, so these are new.

**Honest fence.** The good-gap gluing only: the bad set's finiteness (the mixed-sign kills) and
the Monotonicity Theorem assembly are C1d.
-/
import Sundogcert.OMinimalSignPartition

namespace Sundog.OMinimalAbstract

/-! ### The propagation engine -/

/-- **The gluing engine.** If every point of `(a,b)` has an `R`-coherent two-sided window
(left neighbors `R`-below, right neighbors `R`-above), then `R (φ u) (φ w)` for all
`u < w` in `(a,b)` — by chaining through the supremum of the absorbed set. Only transitivity
of `R` is used. -/
theorem rel_propagate {φ : ℝ → ℝ} {R : ℝ → ℝ → Prop}
    (htrans : ∀ {p q r : ℝ}, R p q → R q r → R p r) {a b : ℝ}
    (hwin : ∀ x ∈ Set.Ioo a b,
      (∃ u₀, u₀ < x ∧ ∀ y, u₀ < y → y < x → R (φ y) (φ x)) ∧
      (∃ v₀, x < v₀ ∧ ∀ y, x < y → y < v₀ → R (φ x) (φ y)))
    {u w : ℝ} (hu : u ∈ Set.Ioo a b) (hw : w ∈ Set.Ioo a b) (huw : u < w) :
    R (φ u) (φ w) := by
  rw [Set.mem_Ioo] at hu hw
  set T : Set ℝ := {z | z ∈ Set.Icc u w ∧ ∀ t, u < t → t ≤ z → R (φ u) (φ t)} with hTdef
  have huT : u ∈ T := by
    constructor
    · rw [Set.mem_Icc]
      exact ⟨le_refl u, huw.le⟩
    · intro t h1 h2
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl u)
  have hTne : T.Nonempty := ⟨u, huT⟩
  have hbdd : BddAbove T := ⟨w, fun z hz => (Set.mem_Icc.mp hz.1).2⟩
  set s := sSup T with hsdef
  have hus : u ≤ s := le_csSup hbdd huT
  have hsw : s ≤ w := csSup_le hTne (fun z hz => (Set.mem_Icc.mp hz.1).2)
  have hsIoo : s ∈ Set.Ioo a b := by
    rw [Set.mem_Ioo]
    exact ⟨lt_of_lt_of_le hu.1 hus, lt_of_le_of_lt hsw hw.2⟩
  obtain ⟨⟨u₀, hu₀s, hleft⟩, ⟨v₀, hsv₀, hright⟩⟩ := hwin s hsIoo
  -- Claim 1: the sup is itself absorbed
  have hPs : ∀ t, u < t → t ≤ s → R (φ u) (φ t) := by
    intro t hut hts
    rcases eq_or_lt_of_le hts with heq | htlt
    · subst heq
      have hmaxlt : max u₀ u < s := max_lt hu₀s hut
      obtain ⟨z', hz'T, hmz'⟩ := exists_lt_of_lt_csSup hTne hmaxlt
      have hz's : z' ≤ s := le_csSup hbdd hz'T
      rcases eq_or_lt_of_le hz's with heq2 | hlt2
      · exact hz'T.2 s hut (le_of_eq heq2.symm)
      · have h1 : R (φ u) (φ z') :=
          hz'T.2 z' (lt_of_le_of_lt (le_max_right u₀ u) hmz') (le_refl z')
        have h2 : R (φ z') (φ s) := hleft z' (lt_of_le_of_lt (le_max_left u₀ u) hmz') hlt2
        exact htrans h1 h2
    · obtain ⟨z', hz'T, htz'⟩ := exists_lt_of_lt_csSup hTne htlt
      exact hz'T.2 t hut htz'.le
  -- Claim 2: the sup is w (else the right window pushes T past it)
  have hseq : s = w := by
    rcases eq_or_lt_of_le hsw with heq | hlt
    · exact heq
    · exfalso
      have hmin : s < min v₀ w := lt_min hsv₀ hlt
      have hsy : s < (s + min v₀ w) / 2 := by linarith
      have hymin : (s + min v₀ w) / 2 < min v₀ w := by linarith
      have hyv₀ : (s + min v₀ w) / 2 < v₀ := lt_of_lt_of_le hymin (min_le_left _ _)
      have hyw : (s + min v₀ w) / 2 ≤ w := le_of_lt (lt_of_lt_of_le hymin (min_le_right _ _))
      have hyT : (s + min v₀ w) / 2 ∈ T := by
        constructor
        · rw [Set.mem_Icc]
          exact ⟨le_trans hus hsy.le, hyw⟩
        · intro t hut hty
          rcases le_or_gt t s with hts | hst
          · exact hPs t hut hts
          · have hRst : R (φ s) (φ t) := hright t hst (lt_of_le_of_lt hty hyv₀)
            rcases eq_or_lt_of_le hus with hueq | hult
            · rw [hueq]
              exact hRst
            · exact htrans (hPs s hult (le_refl s)) hRst
      have hcontra : (s + min v₀ w) / 2 ≤ s := le_csSup hbdd hyT
      linarith
  have hPw : ∀ t, u < t → t ≤ w → R (φ u) (φ t) := hseq ▸ hPs
  exact hPw w huw (le_refl w)

/-! ### The three instantiations -/

/-- **Locally increasing everywhere glues**: neighbor-sense local increase at every point of an
open interval gives `StrictMonoOn`. -/
theorem strictMonoOn_of_locInc {φ : ℝ → ℝ} {a b : ℝ}
    (hloc : ∀ x ∈ Set.Ioo a b, x ∈ locInc φ) : StrictMonoOn φ (Set.Ioo a b) := by
  intro u hu w hw huw
  refine rel_propagate (R := (· < ·)) (fun hpq hqr => lt_trans hpq hqr) ?_ hu hw huw
  intro x hx
  obtain ⟨hR, hL⟩ := hloc x hx
  exact ⟨hL, hR⟩

/-- **Locally decreasing everywhere glues**: `StrictAntiOn`. -/
theorem strictAntiOn_of_locDec {φ : ℝ → ℝ} {a b : ℝ}
    (hloc : ∀ x ∈ Set.Ioo a b, x ∈ locDec φ) : StrictAntiOn φ (Set.Ioo a b) := by
  intro u hu w hw huw
  refine rel_propagate (R := fun p q => q < p) (fun hpq hqr => lt_trans hqr hpq) ?_ hu hw huw
  intro x hx
  obtain ⟨hR, hL⟩ := hloc x hx
  exact ⟨hL, hR⟩

/-- **Locally constant everywhere glues**: `φ` is constant on the interval. -/
theorem eqOn_of_locConst {φ : ℝ → ℝ} {a b : ℝ}
    (hloc : ∀ x ∈ Set.Ioo a b, x ∈ locConst φ) :
    ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, φ x = φ y := by
  have key : ∀ u ∈ Set.Ioo a b, ∀ w ∈ Set.Ioo a b, u < w → φ w = φ u := by
    intro u hu w hw huw
    refine rel_propagate (R := fun p q => q = p) (fun hpq hqr => hqr.trans hpq) ?_ hu hw huw
    intro x hx
    obtain ⟨hR, hL⟩ := hloc x hx
    constructor
    · obtain ⟨u₀, h1, h2⟩ := hL
      exact ⟨u₀, h1, fun y hy1 hy2 => (h2 y hy1 hy2).symm⟩
    · exact hR
  intro x hx y hy
  rcases lt_trichotomy x y with h | h | h
  · exact (key x hx y hy h).symm
  · rw [h]
  · exact key y hy x hx h

end Sundog.OMinimalAbstract
