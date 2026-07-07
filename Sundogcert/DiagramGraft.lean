/-
# TS-QE, TS-2d-2c: the root-insertion splice — grafting roots into gaps and rays.

The reconstruction walk (2d-3) turns a base-diagram into a `P :: base`-diagram by
inserting `P`'s roots as new samples. `P'` is a base member, so between consecutive
samples (and on the two outer rays) `P` is strictly monotone or constant: at most one
root per gap, at most one per ray. This module lands the complete graft toolkit:

- **Keyed gap zones** (`gap_all_pos_mono` … `gap_cross_anti`): on a monotone gap the
  outcome — no root with a known sign, or one root with clean zones — is SELECTED by the
  flank signs, so the walk never has to refute mismatched disjuncts of the TS-2c
  trichotomies.
- **Ray monotonicity** (`strictMonoOn_Iic_of_derivative_pos` …): derivative sign on an
  open ray gives strict monotonicity on the closed ray, by shrinking to `Icc`.
- **Keyed ray zones** (`ray_left_all_pos_mono` … `ray_right_cross_anti`): the outer
  rays, keyed by the boundary-sample sign and the end sign (TS-2c's `eventually_*`
  lemmas — computed from branch data: resolved leading-coefficient sign and degree
  parity). A crossing manufactures the far witness from the eventual bound and grafts
  exactly one root with zones on both sides.
- **The graft mechanism** (`colsFrom_insert`, `colsFrom_insert_last`,
  `colsFrom_graft_root`): inserting a new sample into the first gap (or after the last
  sample) at the `ColsFrom` level, generic in the family; the caller supplies the three
  new column equations. `colsFrom_graft_root`: for the OLD family the three columns
  simply repeat the old gap column — no member moves, only the new sample appears.

The constant case (`P'`-gap-entry zero) needs no lemma here: `spec_eq_zero_of_gap_roots`
(2d-2b) plus `eq_C_of_derivative_eq_zero` make `P` constant, so the gap never splits.

**Honest fence.** Toolkit only: the whole-diagram walk assembling these per-gap pieces
into `Realizes g (P :: F) D̂`, and the branch-uniform packaging, are 2d-3's business.
-/
import Sundogcert.DiagramAugment

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### The sign vector of an extended family -/

theorem signVec_cons (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) (g : Fin n → ℝ) (y : ℝ) :
    signVec (P :: F) g y = SignType.sign ((spec g P).eval y) :: signVec F g y := by
  rw [signVec, signVec, List.map_cons]

/-! ### Keyed gap zones: the outcome selected by the flank signs -/

theorem gap_all_pos_mono (p : ℝ[X]) {a b : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Icc a b))
    (hab : a < b) (ha : 0 ≤ p.eval a) :
    ∀ x ∈ Set.Ioo a b, 0 < p.eval x := by
  intro x hx
  exact lt_of_le_of_lt ha (hmono (Set.left_mem_Icc.mpr hab.le) ⟨hx.1.le, hx.2.le⟩ hx.1)

theorem gap_all_neg_mono (p : ℝ[X]) {a b : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Icc a b))
    (hab : a < b) (hb : p.eval b ≤ 0) :
    ∀ x ∈ Set.Ioo a b, p.eval x < 0 := by
  intro x hx
  exact lt_of_lt_of_le (hmono ⟨hx.1.le, hx.2.le⟩ (Set.right_mem_Icc.mpr hab.le) hx.2) hb

/-- A strict crossing on an increasing gap grafts exactly one root, with zones. -/
theorem gap_cross_mono (p : ℝ[X]) {a b : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Icc a b))
    (hab : a < b) (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ ρ ∈ Set.Ioo a b, p.eval ρ = 0 ∧
      (∀ x ∈ Set.Ioo a ρ, p.eval x < 0) ∧ (∀ x ∈ Set.Ioo ρ b, 0 < p.eval x) := by
  obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn
    (Set.mem_Ioo.mpr ⟨ha, hb⟩)
  refine ⟨ρ, hρI, hρ, ?_, ?_⟩
  · intro x hx
    have h := hmono ⟨hx.1.le, hx.2.le.trans hρI.2.le⟩ ⟨hρI.1.le, hρI.2.le⟩ hx.2
    exact hρ ▸ h
  · intro x hx
    have h := hmono ⟨hρI.1.le, hρI.2.le⟩ ⟨hρI.1.le.trans hx.1.le, hx.2.le⟩ hx.1
    exact hρ ▸ h

theorem gap_all_pos_anti (p : ℝ[X]) {a b : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Icc a b))
    (hab : a < b) (hb : 0 ≤ p.eval b) :
    ∀ x ∈ Set.Ioo a b, 0 < p.eval x := by
  intro x hx
  exact lt_of_le_of_lt hb (hanti ⟨hx.1.le, hx.2.le⟩ (Set.right_mem_Icc.mpr hab.le) hx.2)

theorem gap_all_neg_anti (p : ℝ[X]) {a b : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Icc a b))
    (hab : a < b) (ha : p.eval a ≤ 0) :
    ∀ x ∈ Set.Ioo a b, p.eval x < 0 := by
  intro x hx
  exact lt_of_lt_of_le (hanti (Set.left_mem_Icc.mpr hab.le) ⟨hx.1.le, hx.2.le⟩ hx.1) ha

theorem gap_cross_anti (p : ℝ[X]) {a b : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Icc a b))
    (hab : a < b) (ha : 0 < p.eval a) (hb : p.eval b < 0) :
    ∃ ρ ∈ Set.Ioo a b, p.eval ρ = 0 ∧
      (∀ x ∈ Set.Ioo a ρ, 0 < p.eval x) ∧ (∀ x ∈ Set.Ioo ρ b, p.eval x < 0) := by
  obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn
    (Set.mem_Ioo.mpr ⟨hb, ha⟩)
  refine ⟨ρ, hρI, hρ, ?_, ?_⟩
  · intro x hx
    have h := hanti ⟨hx.1.le, hx.2.le.trans hρI.2.le⟩ ⟨hρI.1.le, hρI.2.le⟩ hx.2
    exact hρ ▸ h
  · intro x hx
    have h := hanti ⟨hρI.1.le, hρI.2.le⟩ ⟨hρI.1.le.trans hx.1.le, hx.2.le⟩ hx.1
    exact hρ ▸ h

/-! ### Ray monotonicity from derivative sign -/

theorem strictMonoOn_Iic_of_derivative_pos (p : ℝ[X]) {b : ℝ}
    (h : ∀ x ∈ Set.Iio b, 0 < p.derivative.eval x) :
    StrictMonoOn (fun x => p.eval x) (Set.Iic b) := fun y hy _y' hy' hlt =>
  strictMonoOn_of_derivative_pos p (fun x hx => h x hx.2)
    ⟨le_refl y, hy⟩ ⟨hlt.le, hy'⟩ hlt

theorem strictAntiOn_Iic_of_derivative_neg (p : ℝ[X]) {b : ℝ}
    (h : ∀ x ∈ Set.Iio b, p.derivative.eval x < 0) :
    StrictAntiOn (fun x => p.eval x) (Set.Iic b) := fun y hy _y' hy' hlt =>
  strictAntiOn_of_derivative_neg p (fun x hx => h x hx.2)
    ⟨le_refl y, hy⟩ ⟨hlt.le, hy'⟩ hlt

theorem strictMonoOn_Ici_of_derivative_pos (p : ℝ[X]) {a : ℝ}
    (h : ∀ x ∈ Set.Ioi a, 0 < p.derivative.eval x) :
    StrictMonoOn (fun x => p.eval x) (Set.Ici a) := fun y hy y' _ hlt =>
  strictMonoOn_of_derivative_pos p (fun x hx => h x (lt_of_le_of_lt hy hx.1))
    ⟨le_refl y, hlt.le⟩ ⟨hlt.le, le_refl y'⟩ hlt

theorem strictAntiOn_Ici_of_derivative_neg (p : ℝ[X]) {a : ℝ}
    (h : ∀ x ∈ Set.Ioi a, p.derivative.eval x < 0) :
    StrictAntiOn (fun x => p.eval x) (Set.Ici a) := fun y hy y' _ hlt =>
  strictAntiOn_of_derivative_neg p (fun x hx => h x (lt_of_le_of_lt hy hx.1))
    ⟨le_refl y, hlt.le⟩ ⟨hlt.le, le_refl y'⟩ hlt

/-! ### Keyed left-ray zones -/

theorem ray_left_all_pos_mono (p : ℝ[X]) {b : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Iic b))
    (hev : ∃ M : ℝ, ∀ x, x < M → 0 < p.eval x) :
    ∀ x ∈ Set.Iio b, 0 < p.eval x := by
  obtain ⟨M, hM⟩ := hev
  intro x hx
  have hxb : x < b := hx
  have hwM : min (M - 1) (x - 1) < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hwx : min (M - 1) (x - 1) < x := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact lt_trans (hM _ hwM)
    (hmono (Set.mem_Iic.mpr (hwx.trans hxb).le) (Set.mem_Iic.mpr hxb.le) hwx)

theorem ray_left_all_neg_mono (p : ℝ[X]) {b : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Iic b)) (hb : p.eval b ≤ 0) :
    ∀ x ∈ Set.Iio b, p.eval x < 0 := by
  intro x hx
  have hxb : x < b := hx
  exact lt_of_lt_of_le (hmono (Set.mem_Iic.mpr hxb.le) (Set.mem_Iic.mpr le_rfl) hxb) hb

/-- **Left-ray graft (increasing)**: negative far end, positive at the boundary sample —
one root on the ray, negative below it, positive between it and the boundary. -/
theorem ray_left_cross_mono (p : ℝ[X]) {b : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Iic b))
    (hev : ∃ M : ℝ, ∀ x, x < M → p.eval x < 0) (hb : 0 < p.eval b) :
    ∃ ρ, ρ < b ∧ p.eval ρ = 0 ∧ (∀ x, x < ρ → p.eval x < 0) ∧
      (∀ x ∈ Set.Ioo ρ b, 0 < p.eval x) := by
  obtain ⟨M, hM⟩ := hev
  have hwM : min (M - 1) (b - 1) < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hwb : min (M - 1) (b - 1) < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo hwb.le p.continuous.continuousOn
    (Set.mem_Ioo.mpr ⟨hM _ hwM, hb⟩)
  refine ⟨ρ, hρI.2, hρ, ?_, ?_⟩
  · intro x hxρ
    have h := hmono (Set.mem_Iic.mpr (hxρ.trans hρI.2).le)
      (Set.mem_Iic.mpr hρI.2.le) hxρ
    exact hρ ▸ h
  · intro x hx
    have h := hmono (Set.mem_Iic.mpr hρI.2.le) (Set.mem_Iic.mpr hx.2.le) hx.1
    exact hρ ▸ h

theorem ray_left_all_neg_anti (p : ℝ[X]) {b : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Iic b))
    (hev : ∃ M : ℝ, ∀ x, x < M → p.eval x < 0) :
    ∀ x ∈ Set.Iio b, p.eval x < 0 := by
  obtain ⟨M, hM⟩ := hev
  intro x hx
  have hxb : x < b := hx
  have hwM : min (M - 1) (x - 1) < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hwx : min (M - 1) (x - 1) < x := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact lt_trans
    (hanti (Set.mem_Iic.mpr (hwx.trans hxb).le) (Set.mem_Iic.mpr hxb.le) hwx)
    (hM _ hwM)

theorem ray_left_all_pos_anti (p : ℝ[X]) {b : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Iic b)) (hb : 0 ≤ p.eval b) :
    ∀ x ∈ Set.Iio b, 0 < p.eval x := by
  intro x hx
  have hxb : x < b := hx
  exact lt_of_le_of_lt hb (hanti (Set.mem_Iic.mpr hxb.le) (Set.mem_Iic.mpr le_rfl) hxb)

/-- **Left-ray graft (decreasing)**: positive far end, negative at the boundary sample. -/
theorem ray_left_cross_anti (p : ℝ[X]) {b : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Iic b))
    (hev : ∃ M : ℝ, ∀ x, x < M → 0 < p.eval x) (hb : p.eval b < 0) :
    ∃ ρ, ρ < b ∧ p.eval ρ = 0 ∧ (∀ x, x < ρ → 0 < p.eval x) ∧
      (∀ x ∈ Set.Ioo ρ b, p.eval x < 0) := by
  obtain ⟨M, hM⟩ := hev
  have hwM : min (M - 1) (b - 1) < M := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hwb : min (M - 1) (b - 1) < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo' hwb.le p.continuous.continuousOn
    (Set.mem_Ioo.mpr ⟨hb, hM _ hwM⟩)
  refine ⟨ρ, hρI.2, hρ, ?_, ?_⟩
  · intro x hxρ
    have h := hanti (Set.mem_Iic.mpr (hxρ.trans hρI.2).le)
      (Set.mem_Iic.mpr hρI.2.le) hxρ
    exact hρ ▸ h
  · intro x hx
    have h := hanti (Set.mem_Iic.mpr hρI.2.le) (Set.mem_Iic.mpr hx.2.le) hx.1
    exact hρ ▸ h

/-! ### Keyed right-ray zones -/

theorem ray_right_all_pos_mono (p : ℝ[X]) {a : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Ici a)) (ha : 0 ≤ p.eval a) :
    ∀ x ∈ Set.Ioi a, 0 < p.eval x := by
  intro x hx
  have hax : a < x := hx
  exact lt_of_le_of_lt ha (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hax.le) hax)

theorem ray_right_all_neg_mono (p : ℝ[X]) {a : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Ici a))
    (hev : ∃ M : ℝ, ∀ x, M < x → p.eval x < 0) :
    ∀ x ∈ Set.Ioi a, p.eval x < 0 := by
  obtain ⟨M, hM⟩ := hev
  intro x hx
  have hax : a < x := hx
  have hMw : M < max (M + 1) (x + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hxw : x < max (M + 1) (x + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  exact lt_trans
    (hmono (Set.mem_Ici.mpr hax.le) (Set.mem_Ici.mpr (hax.trans hxw).le) hxw)
    (hM _ hMw)

/-- **Right-ray graft (increasing)**: negative at the boundary sample, positive far end. -/
theorem ray_right_cross_mono (p : ℝ[X]) {a : ℝ}
    (hmono : StrictMonoOn (fun x => p.eval x) (Set.Ici a))
    (ha : p.eval a < 0) (hev : ∃ M : ℝ, ∀ x, M < x → 0 < p.eval x) :
    ∃ ρ, a < ρ ∧ p.eval ρ = 0 ∧ (∀ x ∈ Set.Ioo a ρ, p.eval x < 0) ∧
      (∀ x, ρ < x → 0 < p.eval x) := by
  obtain ⟨M, hM⟩ := hev
  have hMw : M < max (M + 1) (a + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have haw : a < max (M + 1) (a + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo haw.le p.continuous.continuousOn
    (Set.mem_Ioo.mpr ⟨ha, hM _ hMw⟩)
  refine ⟨ρ, hρI.1, hρ, ?_, ?_⟩
  · intro x hx
    have h := hmono (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hρI.1.le) hx.2
    exact hρ ▸ h
  · intro x hρx
    have h := hmono (Set.mem_Ici.mpr hρI.1.le)
      (Set.mem_Ici.mpr (hρI.1.trans hρx).le) hρx
    exact hρ ▸ h

theorem ray_right_all_neg_anti (p : ℝ[X]) {a : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Ici a)) (ha : p.eval a ≤ 0) :
    ∀ x ∈ Set.Ioi a, p.eval x < 0 := by
  intro x hx
  have hax : a < x := hx
  exact lt_of_lt_of_le (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hax.le) hax) ha

theorem ray_right_all_pos_anti (p : ℝ[X]) {a : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Ici a))
    (hev : ∃ M : ℝ, ∀ x, M < x → 0 < p.eval x) :
    ∀ x ∈ Set.Ioi a, 0 < p.eval x := by
  obtain ⟨M, hM⟩ := hev
  intro x hx
  have hax : a < x := hx
  have hMw : M < max (M + 1) (x + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hxw : x < max (M + 1) (x + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  exact lt_trans (hM _ hMw)
    (hanti (Set.mem_Ici.mpr hax.le) (Set.mem_Ici.mpr (hax.trans hxw).le) hxw)

/-- **Right-ray graft (decreasing)**: positive at the boundary sample, negative far end. -/
theorem ray_right_cross_anti (p : ℝ[X]) {a : ℝ}
    (hanti : StrictAntiOn (fun x => p.eval x) (Set.Ici a))
    (ha : 0 < p.eval a) (hev : ∃ M : ℝ, ∀ x, M < x → p.eval x < 0) :
    ∃ ρ, a < ρ ∧ p.eval ρ = 0 ∧ (∀ x ∈ Set.Ioo a ρ, 0 < p.eval x) ∧
      (∀ x, ρ < x → p.eval x < 0) := by
  obtain ⟨M, hM⟩ := hev
  have hMw : M < max (M + 1) (a + 1) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have haw : a < max (M + 1) (a + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Ioo' haw.le p.continuous.continuousOn
    (Set.mem_Ioo.mpr ⟨hM _ hMw, ha⟩)
  refine ⟨ρ, hρI.1, hρ, ?_, ?_⟩
  · intro x hx
    have h := hanti (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hρI.1.le) hx.2
    exact hρ ▸ h
  · intro x hρx
    have h := hanti (Set.mem_Ici.mpr hρI.1.le)
      (Set.mem_Ici.mpr (hρI.1.trans hρx).le) hρx
    exact hρ ▸ h

/-! ### The graft mechanism at the ColsFrom level -/

theorem some_barrier {ρ y : ℝ} (h : ρ < y) :
    ∀ l ∈ (some ρ : Option ℝ), l < y := by
  intro l hl
  rw [Option.mem_def, Option.some.injEq] at hl
  subst hl
  exact h

/-- **The graft**: insert a new sample `ρ` before the first remaining sample. The first
gap column splits into `[gap, point, gap]`; the caller supplies the three new column
equations. Generic in the family. -/
theorem colsFrom_insert (g : Fin n → ℝ) (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    {lo : Option ℝ} {ρ x₂ : ℝ} {ξ : List ℝ} {cols : List (List SignType)}
    {c c₁ c₀ c₂ : List SignType}
    (h : ColsFrom g F lo (x₂ :: ξ) (c :: cols))
    (hloρ : ∀ l ∈ lo, l < ρ) (hρx : ρ < x₂)
    (h₁ : ∀ y : ℝ, (∀ l ∈ lo, l < y) → y < ρ → signVec F g y = c₁)
    (h₀ : signVec F g ρ = c₀)
    (h₂ : ∀ y : ℝ, ρ < y → y < x₂ → signVec F g y = c₂) :
    ColsFrom g F lo (ρ :: x₂ :: ξ) (c₁ :: c₀ :: c₂ :: cols) := by
  match cols, h with
  | [], h => exact h.elim
  | cpt :: rest, ⟨_hlox, _hgap, hpt, hrest⟩ =>
    refine ⟨hloρ, h₁, h₀, ?_⟩
    exact ⟨some_barrier hρx, fun y hy hyx => h₂ y (hy ρ rfl) hyx, hpt, hrest⟩

/-- **The tail graft**: append a new sample after the last one; the terminal ray splits
into `[gap, point, ray]`. -/
theorem colsFrom_insert_last (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    {lo : Option ℝ} {ρ : ℝ} {c₁ c₀ c₂ : List SignType}
    (hloρ : ∀ l ∈ lo, l < ρ)
    (h₁ : ∀ y : ℝ, (∀ l ∈ lo, l < y) → y < ρ → signVec F g y = c₁)
    (h₀ : signVec F g ρ = c₀)
    (h₂ : ∀ y : ℝ, ρ < y → signVec F g y = c₂) :
    ColsFrom g F lo [ρ] [c₁, c₀, c₂] := by
  refine ⟨hloρ, h₁, h₀, ?_⟩
  exact fun y hy => h₂ y (hy ρ rfl)

/-- **The graft receipt**: any interior point of the first gap grafts as a new sample
with the old gap column repeated three times — for the old family nothing moves, only
the sample appears. (In 2d-3 the walk runs this with `P :: F` and fresh head entries.) -/
theorem colsFrom_graft_root (g : Fin n → ℝ)
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    {lo : Option ℝ} {ρ x₂ : ℝ} {ξ : List ℝ} {cols : List (List SignType)}
    {c : List SignType}
    (h : ColsFrom g F lo (x₂ :: ξ) (c :: cols))
    (hloρ : ∀ l ∈ lo, l < ρ) (hρx : ρ < x₂) :
    ColsFrom g F lo (ρ :: x₂ :: ξ) (c :: c :: c :: cols) := by
  match cols, h with
  | [], h => exact h.elim
  | cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
    refine colsFrom_insert g F ⟨hlox, hgap, hpt, hrest⟩ hloρ hρx ?_ ?_ ?_
    · exact fun y hy hyρ => hgap y hy (hyρ.trans hρx)
    · exact hgap ρ hloρ hρx
    · exact fun y hy hyx => hgap y (fun l hl => (hloρ l hl).trans hy) hyx

end Sundog.TarskiQE
