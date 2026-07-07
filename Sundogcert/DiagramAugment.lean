/-
# TS-QE, TS-2d-2b (foothold): P-column augmentation at samples.

The augmentation pitch needs three tools and one integration receipt, landed here:

- **`realizes_project_prefix`** — a realized diagram of `F₁ ++ F₂` projects to a realized
  diagram of the prefix family `F₁` (columns truncated to the prefix length, same samples).
  With the family laid out as `base ++ remainders`, this extracts the base's diagram; a
  `dropPadding` pass then makes every sample a BASE root — remainder-only samples (whose
  full columns could not be merged, since the remainder vanishes there) disappear together
  with their remainder entries.
- **`sign_transfer_signType`** — TS-2b's three-way transfer at the `SignType` level: at any
  root of `spec g q` (live lead), `sign(P) = sign(emod q P)`.
- **`spec_eq_zero_of_gap_roots`** — a specialized polynomial vanishing on a nonempty open
  interval is zero (root finiteness): the degeneracy that turns a zero derivative-gap
  column into "P is constant".
- **`augment_foothold`** — the integration receipt: for `F' = base ++ base.map (emod · P)`
  realized at `g` with live leads on the base, there is a padding-free realized
  base-diagram at EVERY sample of which P's sign equals a remainder's sign — the transfer
  reaches every sample of the projected structure.

**Honest fence.** Foothold only: writing P's entries into the columns as diagram DATA
(branch-uniformly, via the column positions) and the gap/root-insertion splice are the
remaining pitches (2b-uniform, 2c).
-/
import Sundogcert.DiagramNormalize

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Prefix projection of diagrams -/

theorem signVec_append (F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (g : Fin n → ℝ) (y : ℝ) :
    signVec (F₁ ++ F₂) g y = signVec F₁ g y ++ signVec F₂ g y := by
  rw [signVec, signVec, signVec, List.map_append]

private theorem take_signVec_append (F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (g : Fin n → ℝ) (y : ℝ) :
    (signVec (F₁ ++ F₂) g y).take F₁.length = signVec F₁ g y := by
  rw [signVec_append]
  exact List.take_left' (by rw [signVec, List.length_map])

private theorem colsFrom_project (g : Fin n → ℝ)
    (F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (cols : List (List SignType)),
    ColsFrom g (F₁ ++ F₂) lo ξ cols →
    ColsFrom g F₁ lo ξ (cols.map (List.take F₁.length)) := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo cols hc
    match cols, hc with
    | [c], hc =>
      change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec F₁ g y = c.take F₁.length
      intro y hy
      rw [← hc y hy]
      exact (take_signVec_append F₁ F₂ g y).symm
  | cons x xs ih =>
    intro lo cols hc
    match cols, hc with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      refine ⟨hlox, ?_, ?_, ih (some x) rest hrest⟩
      · intro y hy hyx
        rw [← hgap y hy hyx]
        exact (take_signVec_append F₁ F₂ g y).symm
      · rw [← hpt]
        exact (take_signVec_append F₁ F₂ g x).symm

/-- **Prefix projection**: a realized diagram of `F₁ ++ F₂` restricts to a realized
diagram of `F₁` (columns truncated, same samples). -/
theorem realizes_project_prefix {g : Fin n → ℝ}
    {F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ))} {D : List (List SignType)}
    (h : Realizes g (F₁ ++ F₂) D) :
    Realizes g F₁ (D.map (List.take F₁.length)) := by
  obtain ⟨ξ, hpair, hroots, hcols⟩ := h
  exact ⟨ξ, hpair,
    fun P hP h0 y hy => hroots P (List.mem_append_left _ hP) h0 y hy,
    colsFrom_project g F₁ F₂ ξ none D hcols⟩

/-! ### The transfer at the SignType level -/

/-- TS-2b's transfer, as a `SignType` equation: at any root of `spec g q` with live lead,
`P` and its evenized remainder have the same sign. -/
theorem sign_transfer_signType (g : Fin n → ℝ)
    (q P : Polynomial (MvPolynomial (Fin n) ℝ))
    (hlead : MvPolynomial.eval g q.leadingCoeff ≠ 0) {ρ : ℝ}
    (hroot : (spec g q).eval ρ = 0) :
    SignType.sign ((spec g P).eval ρ) = SignType.sign ((spec g (emod q P)).eval ρ) := by
  obtain ⟨h1, h2, h3⟩ := sign_transfer g q P hlead hroot
  rcases lt_trichotomy ((spec g P).eval ρ) 0 with h | h | h
  · rw [sign_neg h, sign_neg (h3.mp h)]
  · rw [h, h2.mp h]
  · rw [sign_pos h, sign_pos (h1.mp h)]

/-! ### The gap degeneracy -/

/-- A specialized polynomial vanishing on a nonempty open interval is zero. -/
theorem spec_eq_zero_of_gap_roots (g : Fin n → ℝ)
    (Q : Polynomial (MvPolynomial (Fin n) ℝ)) {a b : ℝ} (hab : a < b)
    (h : ∀ y ∈ Set.Ioo a b, (spec g Q).eval y = 0) : spec g Q = 0 := by
  by_contra h0
  exact absurd ((Set.Ioo_infinite hab).mono (fun y hy => h y hy))
    (Set.not_infinite.mpr (Polynomial.finite_setOf_isRoot h0))

/-! ### The integration receipt -/

/-- **The 2b foothold.** For the layout `F' = base ++ base.map (emod · P)`, realized at
`g` with live base leads: there is a padding-free realized base-diagram, and at EVERY one
of its samples, `P`'s sign equals the sign of one of the remainders there — the transfer
reaches the whole projected sample structure. -/
theorem augment_foothold {g : Fin n → ℝ}
    {base : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {D : List (List SignType)}
    (hlive : ∀ q ∈ base, MvPolynomial.eval g q.leadingCoeff ≠ 0)
    (h : Realizes g (base ++ base.map (fun q => emod q P)) D) :
    ∃ D'' : List (List SignType), Realizes g base D'' ∧ PaddingFree D'' ∧
      ∃ ξ : List ℝ, ξ.Pairwise (· < ·) ∧
        (∀ Q ∈ base, spec g Q ≠ 0 → ∀ y : ℝ, (spec g Q).IsRoot y → y ∈ ξ) ∧
        ColsFrom g base none ξ D'' ∧
        ∀ x ∈ ξ, ∃ q ∈ base, (spec g q).eval x = 0 ∧
          SignType.sign ((spec g P).eval x)
            = SignType.sign ((spec g (emod q P)).eval x) := by
  have hproj := realizes_project_prefix h
  have hdrop := realizes_dropPadding hproj
  have hPF := dropPadding_paddingFree (D.map (List.take base.length))
  obtain ⟨ξ, hpair, hroots, hcols, hsamples⟩ := realizes_samples_root hPF hdrop
  refine ⟨dropPadding (D.map (List.take base.length)), hdrop, hPF,
    ξ, hpair, hroots, hcols, ?_⟩
  intro x hx
  obtain ⟨q, hq, hq0⟩ := hsamples x hx
  exact ⟨q, hq, hq0, sign_transfer_signType g q P (hlive q hq) hq0⟩

end Sundog.TarskiQE
