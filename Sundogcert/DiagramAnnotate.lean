/-
# TS-QE, TS-2d-3 (second half, first pitch): computing the annotation.

The walk (`DiagramWalk`) consumes `(sP, plans)`; this module COMPUTES them from what
the machinery already provides. Inputs per gap/ray: the derivative's constant sign
(TS-1 `poly_sign_constant` on a root-free gap — root-freeness from "derivative roots
are samples"), the flank signs (2d-2b's transfer values at samples), and the end signs
(`BotSign`/`TopSign`, discharged from leading-coefficient data by TS-2c's
`eventually_*` lemmas). Outputs: the decision functions

- `gapPlanMono sa sb` / `gapPlanAnti sa sb` — flow or graft, SELECTED by the flank
  signs (a strict crossing grafts; anything else flows with the determined sign);

and the validity lemmas, one per (position × orientation), each discharged by exactly
one TS-2d-2c keyed zone lemma:

- `gapValid_incr`/`gapValid_anti` — bounded gap, flanks = sample signs;
- `gapValid_left_incr`/`_anti` — the left ray (`lo = none`), left flank = `BotSign`;
- `rayValid_right_incr`/`_anti` — the terminal ray, right flank = `TopSign`;
- `rayValid_line_incr`/`_anti` — the whole line (no samples), both flanks are ends;
- `gapValid_const`/`rayValid_const` — the degenerate constant-P case.

Capstone **`exists_graftData`**: if the derivative's roots (when nonzero) are among the
samples, a valid annotation exists — so `realizes_graftWalk` fires. Everything the
plans depend on (derivative gap signs, sample signs, end signs) is transfer- or
branch-readable; making them branch-CONSTANT is the descent's remaining business.
-/
import Sundogcert.DiagramWalk

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### End signs -/

/-- The sign of `spec g P` near `-∞` (`zero` reserved for the zero polynomial). -/
def BotSign (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) : SignType → Prop
  | SignType.zero => spec g P = 0
  | SignType.neg => ∃ M : ℝ, ∀ z : ℝ, z < M → (spec g P).eval z < 0
  | SignType.pos => ∃ M : ℝ, ∀ z : ℝ, z < M → 0 < (spec g P).eval z

/-- The sign of `spec g P` near `+∞`. -/
def TopSign (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) : SignType → Prop
  | SignType.zero => spec g P = 0
  | SignType.neg => ∃ M : ℝ, ∀ z : ℝ, M < z → (spec g P).eval z < 0
  | SignType.pos => ∃ M : ℝ, ∀ z : ℝ, M < z → 0 < (spec g P).eval z

theorem exists_topSign (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ ε : SignType, TopSign g P ε := by
  by_cases h0 : spec g P = 0
  · exact ⟨SignType.zero, h0⟩
  · rcases lt_trichotomy (spec g P).leadingCoeff 0 with h | h | h
    · exact ⟨SignType.neg, eventually_neg_atTop _ h⟩
    · exact absurd (Polynomial.leadingCoeff_eq_zero.mp h) h0
    · exact ⟨SignType.pos, eventually_pos_atTop _ h⟩

theorem exists_botSign (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ ε : SignType, BotSign g P ε := by
  by_cases h0 : spec g P = 0
  · exact ⟨SignType.zero, h0⟩
  · rcases lt_trichotomy ((-1 : ℝ) ^ (spec g P).natDegree * (spec g P).leadingCoeff) 0
      with h | h | h
    · exact ⟨SignType.neg, eventually_neg_atBot _ h⟩
    · exfalso
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (pow_ne_zero _ (by norm_num))
      · exact h0 (Polynomial.leadingCoeff_eq_zero.mp h1)
    · exact ⟨SignType.pos, eventually_pos_atBot _ h⟩

/-! ### Sign constancy on root-free rays and the line -/

theorem ray_sign_constant_left (p : ℝ[X]) {b : ℝ}
    (hfree : ∀ y ∈ Set.Iio b, ¬ p.IsRoot y) :
    (∀ y ∈ Set.Iio b, 0 < p.eval y) ∨ (∀ y ∈ Set.Iio b, p.eval y < 0) := by
  have hb1 : b - 1 ∈ Set.Iio b := Set.mem_Iio.mpr (by linarith)
  have hkey : ∀ y ∈ Set.Iio b, SignType.sign (p.eval y) = SignType.sign (p.eval (b - 1)) := by
    intro y hy
    have hyb : y < b := hy
    rcases le_total y (b - 1) with h | h
    · exact sign_eq_of_no_root_Icc p h fun z hz =>
        hfree z (Set.mem_Iio.mpr (lt_of_le_of_lt hz.2 (by linarith)))
    · exact (sign_eq_of_no_root_Icc p h fun z hz =>
        hfree z (Set.mem_Iio.mpr (lt_of_le_of_lt hz.2 hyb))).symm
  rcases lt_trichotomy (p.eval (b - 1)) 0 with h | h | h
  · refine Or.inr fun y hy => ?_
    have hs := hkey y hy
    rw [sign_neg h] at hs
    exact sign_eq_neg_one_iff.mp hs
  · exact absurd h (hfree _ hb1)
  · refine Or.inl fun y hy => ?_
    have hs := hkey y hy
    rw [sign_pos h] at hs
    exact sign_eq_one_iff.mp hs

theorem ray_sign_constant_right (p : ℝ[X]) {a : ℝ}
    (hfree : ∀ y ∈ Set.Ioi a, ¬ p.IsRoot y) :
    (∀ y ∈ Set.Ioi a, 0 < p.eval y) ∨ (∀ y ∈ Set.Ioi a, p.eval y < 0) := by
  have ha1 : a + 1 ∈ Set.Ioi a := Set.mem_Ioi.mpr (by linarith)
  have hkey : ∀ y ∈ Set.Ioi a, SignType.sign (p.eval y) = SignType.sign (p.eval (a + 1)) := by
    intro y hy
    have hay : a < y := hy
    rcases le_total y (a + 1) with h | h
    · exact sign_eq_of_no_root_Icc p h fun z hz =>
        hfree z (Set.mem_Ioi.mpr (lt_of_lt_of_le hay hz.1))
    · exact (sign_eq_of_no_root_Icc p h fun z hz =>
        hfree z (Set.mem_Ioi.mpr (lt_of_lt_of_le (by linarith) hz.1))).symm
  rcases lt_trichotomy (p.eval (a + 1)) 0 with h | h | h
  · refine Or.inr fun y hy => ?_
    have hs := hkey y hy
    rw [sign_neg h] at hs
    exact sign_eq_neg_one_iff.mp hs
  · exact absurd h (hfree _ ha1)
  · refine Or.inl fun y hy => ?_
    have hs := hkey y hy
    rw [sign_pos h] at hs
    exact sign_eq_one_iff.mp hs

theorem line_sign_constant (p : ℝ[X]) (hfree : ∀ y : ℝ, ¬ p.IsRoot y) :
    (∀ y : ℝ, 0 < p.eval y) ∨ (∀ y : ℝ, p.eval y < 0) := by
  have hkey : ∀ y : ℝ, SignType.sign (p.eval y) = SignType.sign (p.eval 0) := by
    intro y
    rcases le_total y 0 with h | h
    · exact sign_eq_of_no_root_Icc p h fun z _ => hfree z
    · exact (sign_eq_of_no_root_Icc p h fun z _ => hfree z).symm
  rcases lt_trichotomy (p.eval 0) 0 with h | h | h
  · refine Or.inr fun y => ?_
    have hs := hkey y
    rw [sign_neg h] at hs
    exact sign_eq_neg_one_iff.mp hs
  · exact absurd h (hfree 0)
  · refine Or.inl fun y => ?_
    have hs := hkey y
    rw [sign_pos h] at hs
    exact sign_eq_one_iff.mp hs

/-! ### Whole-line monotonicity -/

theorem strictMono_of_derivative_pos (p : ℝ[X])
    (h : ∀ x : ℝ, 0 < p.derivative.eval x) : StrictMono fun x => p.eval x :=
  fun y y' hlt =>
    strictMonoOn_of_derivative_pos p (fun z _ => h z)
      ⟨le_refl y, hlt.le⟩ ⟨hlt.le, le_refl y'⟩ hlt

theorem strictAnti_of_derivative_neg (p : ℝ[X])
    (h : ∀ x : ℝ, p.derivative.eval x < 0) : StrictAnti fun x => p.eval x :=
  fun y y' hlt =>
    strictAntiOn_of_derivative_neg p (fun z _ => h z)
      ⟨le_refl y, hlt.le⟩ ⟨hlt.le, le_refl y'⟩ hlt

/-! ### The decision functions -/

/-- The plan on an increasing stretch, selected by the flank signs. -/
def gapPlanMono (sa sb : SignType) : GapPlan :=
  if sa = SignType.neg then
    if sb = SignType.pos then GapPlan.graft SignType.neg SignType.pos
    else GapPlan.flow SignType.neg
  else GapPlan.flow SignType.pos

/-- The plan on a decreasing stretch, selected by the flank signs. -/
def gapPlanAnti (sa sb : SignType) : GapPlan :=
  if sa = SignType.pos then
    if sb = SignType.neg then GapPlan.graft SignType.pos SignType.neg
    else GapPlan.flow SignType.pos
  else GapPlan.flow SignType.neg

/-! ### Validity: bounded gaps -/

theorem some_mem_lt {a y : ℝ} (h : a < y) :
    ∀ l ∈ (some a : Option ℝ), l < y := by
  intro l hl
  rw [Option.mem_def, Option.some.injEq] at hl
  subst hl
  exact h

theorem gapValid_incr (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {a x : ℝ} (hax : a < x)
    (hmono : StrictMonoOn (fun y => (spec g P).eval y) (Set.Icc a x)) :
    GapValid g P (some a) x
      (gapPlanMono (SignType.sign ((spec g P).eval a))
        (SignType.sign ((spec g P).eval x))) := by
  by_cases hsa : SignType.sign ((spec g P).eval a) = SignType.neg
  · by_cases hsb : SignType.sign ((spec g P).eval x) = SignType.pos
    · unfold gapPlanMono
      rw [if_pos hsa, if_pos hsb]
      have ha : (spec g P).eval a < 0 := sign_eq_neg_one_iff.mp hsa
      have hb : 0 < (spec g P).eval x := sign_eq_one_iff.mp hsb
      obtain ⟨ρ, hρI, hρ0, hz1, hz2⟩ := gap_cross_mono (spec g P) hmono hax ha hb
      refine ⟨ρ, some_mem_lt hρI.1, hρI.2, hρ0, ?_, ?_⟩
      · intro y hy hyρ
        exact sign_neg (hz1 y ⟨hy a rfl, hyρ⟩)
      · intro y hρy hyx
        exact sign_pos (hz2 y ⟨hρy, hyx⟩)
    · unfold gapPlanMono
      rw [if_pos hsa, if_neg hsb]
      have hb : (spec g P).eval x ≤ 0 := not_lt.mp fun h => hsb (sign_pos h)
      intro y hy hyx
      exact sign_neg (gap_all_neg_mono (spec g P) hmono hax hb y ⟨hy a rfl, hyx⟩)
  · unfold gapPlanMono
    rw [if_neg hsa]
    have ha : 0 ≤ (spec g P).eval a := not_lt.mp fun h => hsa (sign_neg h)
    intro y hy hyx
    exact sign_pos (gap_all_pos_mono (spec g P) hmono hax ha y ⟨hy a rfl, hyx⟩)

theorem gapValid_anti (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {a x : ℝ} (hax : a < x)
    (hanti : StrictAntiOn (fun y => (spec g P).eval y) (Set.Icc a x)) :
    GapValid g P (some a) x
      (gapPlanAnti (SignType.sign ((spec g P).eval a))
        (SignType.sign ((spec g P).eval x))) := by
  by_cases hsa : SignType.sign ((spec g P).eval a) = SignType.pos
  · by_cases hsb : SignType.sign ((spec g P).eval x) = SignType.neg
    · unfold gapPlanAnti
      rw [if_pos hsa, if_pos hsb]
      have ha : 0 < (spec g P).eval a := sign_eq_one_iff.mp hsa
      have hb : (spec g P).eval x < 0 := sign_eq_neg_one_iff.mp hsb
      obtain ⟨ρ, hρI, hρ0, hz1, hz2⟩ := gap_cross_anti (spec g P) hanti hax ha hb
      refine ⟨ρ, some_mem_lt hρI.1, hρI.2, hρ0, ?_, ?_⟩
      · intro y hy hyρ
        exact sign_pos (hz1 y ⟨hy a rfl, hyρ⟩)
      · intro y hρy hyx
        exact sign_neg (hz2 y ⟨hρy, hyx⟩)
    · unfold gapPlanAnti
      rw [if_pos hsa, if_neg hsb]
      have hb : 0 ≤ (spec g P).eval x := not_lt.mp fun h => hsb (sign_neg h)
      intro y hy hyx
      exact sign_pos (gap_all_pos_anti (spec g P) hanti hax hb y ⟨hy a rfl, hyx⟩)
  · unfold gapPlanAnti
    rw [if_neg hsa]
    have ha : (spec g P).eval a ≤ 0 := not_lt.mp fun h => hsa (sign_pos h)
    intro y hy hyx
    exact sign_neg (gap_all_neg_anti (spec g P) hanti hax ha y ⟨hy a rfl, hyx⟩)

/-! ### Validity: the left ray -/

theorem gapValid_left_incr (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {x : ℝ} {εm : SignType}
    (hmono : StrictMonoOn (fun y => (spec g P).eval y) (Set.Iic x))
    (hbot : BotSign g P εm) :
    GapValid g P none x (gapPlanMono εm (SignType.sign ((spec g P).eval x))) := by
  match εm, hbot with
  | SignType.zero, hb0 =>
    exfalso
    have h1 := hmono (Set.mem_Iic.mpr (by linarith : x - 1 ≤ x))
      (Set.mem_Iic.mpr le_rfl) (by linarith : x - 1 < x)
    rw [hb0] at h1
    simp at h1
  | SignType.pos, hev =>
    unfold gapPlanMono
    rw [if_neg (by decide : ¬(SignType.pos = SignType.neg))]
    intro y _ hyx
    exact sign_pos (ray_left_all_pos_mono (spec g P) hmono hev y hyx)
  | SignType.neg, hev =>
    by_cases hsb : SignType.sign ((spec g P).eval x) = SignType.pos
    · unfold gapPlanMono
      rw [if_pos rfl, if_pos hsb]
      have hb : 0 < (spec g P).eval x := sign_eq_one_iff.mp hsb
      obtain ⟨ρ, hρx, hρ0, hz1, hz2⟩ := ray_left_cross_mono (spec g P) hmono hev hb
      refine ⟨ρ, fun l hl => by simp at hl, hρx, hρ0, ?_, ?_⟩
      · intro y _ hyρ
        exact sign_neg (hz1 y hyρ)
      · intro y hρy hyx
        exact sign_pos (hz2 y ⟨hρy, hyx⟩)
    · unfold gapPlanMono
      rw [if_pos rfl, if_neg hsb]
      have hb : (spec g P).eval x ≤ 0 := not_lt.mp fun h => hsb (sign_pos h)
      intro y _ hyx
      exact sign_neg (ray_left_all_neg_mono (spec g P) hmono hb y hyx)

theorem gapValid_left_anti (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {x : ℝ} {εm : SignType}
    (hanti : StrictAntiOn (fun y => (spec g P).eval y) (Set.Iic x))
    (hbot : BotSign g P εm) :
    GapValid g P none x (gapPlanAnti εm (SignType.sign ((spec g P).eval x))) := by
  match εm, hbot with
  | SignType.zero, hb0 =>
    exfalso
    have h1 := hanti (Set.mem_Iic.mpr (by linarith : x - 1 ≤ x))
      (Set.mem_Iic.mpr le_rfl) (by linarith : x - 1 < x)
    rw [hb0] at h1
    simp at h1
  | SignType.neg, hev =>
    unfold gapPlanAnti
    rw [if_neg (by decide : ¬(SignType.neg = SignType.pos))]
    intro y _ hyx
    exact sign_neg (ray_left_all_neg_anti (spec g P) hanti hev y hyx)
  | SignType.pos, hev =>
    by_cases hsb : SignType.sign ((spec g P).eval x) = SignType.neg
    · unfold gapPlanAnti
      rw [if_pos rfl, if_pos hsb]
      have hb : (spec g P).eval x < 0 := sign_eq_neg_one_iff.mp hsb
      obtain ⟨ρ, hρx, hρ0, hz1, hz2⟩ := ray_left_cross_anti (spec g P) hanti hev hb
      refine ⟨ρ, fun l hl => by simp at hl, hρx, hρ0, ?_, ?_⟩
      · intro y _ hyρ
        exact sign_pos (hz1 y hyρ)
      · intro y hρy hyx
        exact sign_neg (hz2 y ⟨hρy, hyx⟩)
    · unfold gapPlanAnti
      rw [if_pos rfl, if_neg hsb]
      have hb : 0 ≤ (spec g P).eval x := not_lt.mp fun h => hsb (sign_neg h)
      intro y _ hyx
      exact sign_pos (ray_left_all_pos_anti (spec g P) hanti hb y hyx)

/-! ### Validity: the terminal ray -/

theorem rayValid_right_incr (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {a : ℝ} {εp : SignType}
    (hmono : StrictMonoOn (fun y => (spec g P).eval y) (Set.Ici a))
    (htop : TopSign g P εp) :
    RayValid g P (some a) (gapPlanMono (SignType.sign ((spec g P).eval a)) εp) := by
  by_cases hsa : SignType.sign ((spec g P).eval a) = SignType.neg
  · match εp, htop with
    | SignType.zero, ht0 =>
      exfalso
      have h1 := hmono (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr (by linarith : a ≤ a + 1)) (by linarith : a < a + 1)
      rw [ht0] at h1
      simp at h1
    | SignType.pos, hev =>
      unfold gapPlanMono
      rw [if_pos hsa, if_pos rfl]
      have ha : (spec g P).eval a < 0 := sign_eq_neg_one_iff.mp hsa
      obtain ⟨ρ, haρ, hρ0, hz1, hz2⟩ := ray_right_cross_mono (spec g P) hmono ha hev
      refine ⟨ρ, some_mem_lt haρ, hρ0, ?_, ?_⟩
      · intro y hy hyρ
        exact sign_neg (hz1 y ⟨hy a rfl, hyρ⟩)
      · intro y hρy
        exact sign_pos (hz2 y hρy)
    | SignType.neg, hev =>
      unfold gapPlanMono
      rw [if_pos hsa, if_neg (by decide : ¬(SignType.neg = SignType.pos))]
      intro y hy
      exact sign_neg (ray_right_all_neg_mono (spec g P) hmono hev y (hy a rfl))
  · unfold gapPlanMono
    rw [if_neg hsa]
    have ha : 0 ≤ (spec g P).eval a := not_lt.mp fun h => hsa (sign_neg h)
    intro y hy
    exact sign_pos (ray_right_all_pos_mono (spec g P) hmono ha y (hy a rfl))

theorem rayValid_right_anti (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {a : ℝ} {εp : SignType}
    (hanti : StrictAntiOn (fun y => (spec g P).eval y) (Set.Ici a))
    (htop : TopSign g P εp) :
    RayValid g P (some a) (gapPlanAnti (SignType.sign ((spec g P).eval a)) εp) := by
  by_cases hsa : SignType.sign ((spec g P).eval a) = SignType.pos
  · match εp, htop with
    | SignType.zero, ht0 =>
      exfalso
      have h1 := hanti (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr (by linarith : a ≤ a + 1)) (by linarith : a < a + 1)
      rw [ht0] at h1
      simp at h1
    | SignType.neg, hev =>
      unfold gapPlanAnti
      rw [if_pos hsa, if_pos rfl]
      have ha : 0 < (spec g P).eval a := sign_eq_one_iff.mp hsa
      obtain ⟨ρ, haρ, hρ0, hz1, hz2⟩ := ray_right_cross_anti (spec g P) hanti ha hev
      refine ⟨ρ, some_mem_lt haρ, hρ0, ?_, ?_⟩
      · intro y hy hyρ
        exact sign_pos (hz1 y ⟨hy a rfl, hyρ⟩)
      · intro y hρy
        exact sign_neg (hz2 y hρy)
    | SignType.pos, hev =>
      unfold gapPlanAnti
      rw [if_pos hsa, if_neg (by decide : ¬(SignType.pos = SignType.neg))]
      intro y hy
      exact sign_pos (ray_right_all_pos_anti (spec g P) hanti hev y (hy a rfl))
  · unfold gapPlanAnti
    rw [if_neg hsa]
    have ha : (spec g P).eval a ≤ 0 := not_lt.mp fun h => hsa (sign_pos h)
    intro y hy
    exact sign_neg (ray_right_all_neg_anti (spec g P) hanti ha y (hy a rfl))

/-! ### Validity: the whole line -/

theorem rayValid_line_incr (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {εm εp : SignType} (hmono : StrictMono fun y => (spec g P).eval y)
    (hbot : BotSign g P εm) (htop : TopSign g P εp) :
    RayValid g P none (gapPlanMono εm εp) := by
  match εm, hbot with
  | SignType.zero, hb0 =>
    exfalso
    have h1 := hmono (show (0 : ℝ) < 1 by norm_num)
    rw [hb0] at h1
    simp at h1
  | SignType.pos, ⟨M, hM⟩ =>
    unfold gapPlanMono
    rw [if_neg (by decide : ¬(SignType.pos = SignType.neg))]
    intro y _
    have h1 : min (M - 1) (y - 1) < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h2 : min (M - 1) (y - 1) < y := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact sign_pos (lt_trans (hM _ h1) (hmono h2))
  | SignType.neg, ⟨M, hM⟩ =>
    match εp, htop with
    | SignType.zero, ht0 =>
      exfalso
      have h1 := hmono (show (0 : ℝ) < 1 by norm_num)
      rw [ht0] at h1
      simp at h1
    | SignType.neg, ⟨M', hM'⟩ =>
      unfold gapPlanMono
      rw [if_pos rfl, if_neg (by decide : ¬(SignType.neg = SignType.pos))]
      intro y _
      have h1 : M' < max (M' + 1) (y + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have h2 : y < max (M' + 1) (y + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      exact sign_neg (lt_trans (hmono h2) (hM' _ h1))
    | SignType.pos, ⟨M', hM'⟩ =>
      unfold gapPlanMono
      rw [if_pos rfl, if_pos rfl]
      have hw : min (M - 1) 0 < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hw' : M' < max (M' + 1) 1 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hlt : min (M - 1) 0 < max (M' + 1) 1 :=
        lt_of_le_of_lt (min_le_right _ _)
          (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
      obtain ⟨ρ, _hρI, hρ0⟩ := intermediate_value_Ioo hlt.le
        (spec g P).continuous.continuousOn
        (Set.mem_Ioo.mpr ⟨hM _ hw, hM' _ hw'⟩)
      refine ⟨ρ, fun l hl => by simp at hl, hρ0, ?_, ?_⟩
      · intro y _ hyρ
        have h := hmono hyρ
        exact sign_neg (hρ0 ▸ h)
      · intro y hρy
        have h := hmono hρy
        exact sign_pos (hρ0 ▸ h)

theorem rayValid_line_anti (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {εm εp : SignType} (hanti : StrictAnti fun y => (spec g P).eval y)
    (hbot : BotSign g P εm) (htop : TopSign g P εp) :
    RayValid g P none (gapPlanAnti εm εp) := by
  match εm, hbot with
  | SignType.zero, hb0 =>
    exfalso
    have h1 := hanti (show (0 : ℝ) < 1 by norm_num)
    rw [hb0] at h1
    simp at h1
  | SignType.neg, ⟨M, hM⟩ =>
    unfold gapPlanAnti
    rw [if_neg (by decide : ¬(SignType.neg = SignType.pos))]
    intro y _
    have h1 : min (M - 1) (y - 1) < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h2 : min (M - 1) (y - 1) < y := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact sign_neg (lt_trans (hanti h2) (hM _ h1))
  | SignType.pos, ⟨M, hM⟩ =>
    match εp, htop with
    | SignType.zero, ht0 =>
      exfalso
      have h1 := hanti (show (0 : ℝ) < 1 by norm_num)
      rw [ht0] at h1
      simp at h1
    | SignType.pos, ⟨M', hM'⟩ =>
      unfold gapPlanAnti
      rw [if_pos rfl, if_neg (by decide : ¬(SignType.pos = SignType.neg))]
      intro y _
      have h1 : M' < max (M' + 1) (y + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have h2 : y < max (M' + 1) (y + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      exact sign_pos (lt_trans (hM' _ h1) (hanti h2))
    | SignType.neg, ⟨M', hM'⟩ =>
      unfold gapPlanAnti
      rw [if_pos rfl, if_pos rfl]
      have hw : min (M - 1) 0 < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hw' : M' < max (M' + 1) 1 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hlt : min (M - 1) 0 < max (M' + 1) 1 :=
        lt_of_le_of_lt (min_le_right _ _)
          (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
      obtain ⟨ρ, _hρI, hρ0⟩ := intermediate_value_Ioo' hlt.le
        (spec g P).continuous.continuousOn
        (Set.mem_Ioo.mpr ⟨hM' _ hw', hM _ hw⟩)
      refine ⟨ρ, fun l hl => by simp at hl, hρ0, ?_, ?_⟩
      · intro y _ hyρ
        have h := hanti hyρ
        exact sign_pos (hρ0 ▸ h)
      · intro y hρy
        have h := hanti hρy
        exact sign_neg (hρ0 ▸ h)

/-! ### Validity: the constant case -/

theorem gapValid_const (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {k : ℝ} (hC : spec g P = Polynomial.C k) {lo : Option ℝ} {x : ℝ} :
    GapValid g P lo x (GapPlan.flow (SignType.sign k)) := by
  intro y _ _
  rw [hC, Polynomial.eval_C]

theorem rayValid_const (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {k : ℝ} (hC : spec g P = Polynomial.C k) {lo : Option ℝ} :
    RayValid g P lo (GapPlan.flow (SignType.sign k)) := by
  intro y _
  rw [hC, Polynomial.eval_C]

/-! ### The capstone: a valid annotation exists -/

/-- **The annotation computation.** If the specialized derivative's roots (when it is
nonzero) all lie among the samples, then a valid `GraftData` annotation exists — every
gap and ray gets its plan from the flank/end signs via the decision functions, and the
walk can fire. -/
theorem exists_graftData (g : Fin n → ℝ) (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (hd : spec g Pd = derivative (spec g P)) :
    ∀ (ξ : List ℝ) (lo : Option ℝ), ξ.Pairwise (· < ·) →
    (∀ x ∈ ξ, ∀ l ∈ lo, l < x) →
    (spec g Pd ≠ 0 → ∀ y : ℝ, (∀ l ∈ lo, l < y) → (spec g Pd).IsRoot y → y ∈ ξ) →
    ∃ (sP : List SignType) (plans : List GapPlan), GraftData g P lo ξ sP plans := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo _hpair _hbar hroots
    by_cases h0 : spec g Pd = 0
    · rw [hd] at h0
      exact ⟨[], [GapPlan.flow (SignType.sign ((spec g P).coeff 0))],
        rayValid_const g P (Polynomial.eq_C_of_derivative_eq_zero h0)⟩
    · rcases lo with _ | a
      · have hfree : ∀ y : ℝ, ¬ (spec g Pd).IsRoot y := by
          intro y hr
          have hmem := hroots h0 y (fun l hl => by simp at hl) hr
          simp at hmem
        obtain ⟨εm, hbot⟩ := exists_botSign g P
        obtain ⟨εp, htop⟩ := exists_topSign g P
        rcases line_sign_constant (spec g Pd) hfree with hpos | hneg
        · exact ⟨[], [gapPlanMono εm εp], rayValid_line_incr g P
            (strictMono_of_derivative_pos _ fun z => by rw [← hd]; exact hpos z)
            hbot htop⟩
        · exact ⟨[], [gapPlanAnti εm εp], rayValid_line_anti g P
            (strictAnti_of_derivative_neg _ fun z => by rw [← hd]; exact hneg z)
            hbot htop⟩
      · have hfree : ∀ y ∈ Set.Ioi a, ¬ (spec g Pd).IsRoot y := by
          intro y hy hr
          have hay : a < y := hy
          have hmem := hroots h0 y (some_mem_lt hay) hr
          simp at hmem
        obtain ⟨εp, htop⟩ := exists_topSign g P
        rcases ray_sign_constant_right (spec g Pd) hfree with hpos | hneg
        · exact ⟨[], [gapPlanMono (SignType.sign ((spec g P).eval a)) εp],
            rayValid_right_incr g P (strictMonoOn_Ici_of_derivative_pos _
              fun z hz => by rw [← hd]; exact hpos z hz) htop⟩
        · exact ⟨[], [gapPlanAnti (SignType.sign ((spec g P).eval a)) εp],
            rayValid_right_anti g P (strictAntiOn_Ici_of_derivative_neg _
              fun z hz => by rw [← hd]; exact hneg z hz) htop⟩
  | cons x xs ih =>
    intro lo hpair hbar hroots
    obtain ⟨hxlt, hpair'⟩ := List.pairwise_cons.mp hpair
    have hbarx : ∀ l ∈ lo, l < x := hbar x (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨sP', plans', hdata'⟩ := ih (some x) hpair'
      (fun z hz l hl => by
        rw [Option.mem_def, Option.some.injEq] at hl
        subst hl
        exact hxlt z hz)
      (fun hne y hy hr => by
        have hxy : x < y := hy x rfl
        rcases List.mem_cons.mp
          (hroots hne y (fun l hl => lt_trans (hbarx l hl) hxy) hr) with rfl | hmem
        · exact absurd hxy (lt_irrefl y)
        · exact hmem)
    have hplan : ∃ pl : GapPlan, GapValid g P lo x pl := by
      by_cases h0 : spec g Pd = 0
      · rw [hd] at h0
        exact ⟨_, gapValid_const g P (Polynomial.eq_C_of_derivative_eq_zero h0)⟩
      · rcases lo with _ | a
        · have hfree : ∀ y ∈ Set.Iio x, ¬ (spec g Pd).IsRoot y := by
            intro y hy hr
            have hyx : y < x := hy
            rcases List.mem_cons.mp
              (hroots h0 y (fun l hl => by simp at hl) hr) with rfl | hmem
            · exact absurd hyx (lt_irrefl y)
            · exact absurd hyx (lt_asymm (hxlt y hmem))
          obtain ⟨εm, hbot⟩ := exists_botSign g P
          rcases ray_sign_constant_left (spec g Pd) hfree with hpos | hneg
          · exact ⟨_, gapValid_left_incr g P (strictMonoOn_Iic_of_derivative_pos _
              fun z hz => by rw [← hd]; exact hpos z hz) hbot⟩
          · exact ⟨_, gapValid_left_anti g P (strictAntiOn_Iic_of_derivative_neg _
              fun z hz => by rw [← hd]; exact hneg z hz) hbot⟩
        · have hax : a < x := hbarx a rfl
          have hfree : ∀ y ∈ Set.Ioo a x, ¬ (spec g Pd).IsRoot y := by
            intro y hy hr
            rcases List.mem_cons.mp
              (hroots h0 y (some_mem_lt hy.1) hr) with rfl | hmem
            · exact absurd hy.2 (lt_irrefl y)
            · exact absurd hy.2 (lt_asymm (hxlt y hmem))
          rcases poly_sign_constant (spec g Pd) hfree with hpos | hneg
          · exact ⟨_, gapValid_incr g P hax (strictMonoOn_of_derivative_pos _
              fun z hz => by rw [← hd]; exact hpos z hz)⟩
          · exact ⟨_, gapValid_anti g P hax (strictAntiOn_of_derivative_neg _
              fun z hz => by rw [← hd]; exact hneg z hz)⟩
    obtain ⟨pl, hpl⟩ := hplan
    exact ⟨SignType.sign ((spec g P).eval x) :: sP', pl :: plans', hpl, rfl, hdata'⟩

end Sundog.TarskiQE
