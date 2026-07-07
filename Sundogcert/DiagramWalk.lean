/-
# TS-QE, TS-2d-3 (first half): the whole-diagram walk.

The reconstruction assembled: from a realized diagram of `F` and a per-gap/per-sample
annotation for `P`, build the realized diagram of `P :: F` — with the new diagram an
EXPLICIT FUNCTION of diagram-level data. That function shape is the uniformity payload:
on a branch where the inputs `(sP, plans, D)` are constant, the output
`graftWalk sP plans D` is one concrete diagram valid branch-wide; only the VALIDITY
side conditions mention the point `g`.

- **`GapPlan`** — the per-gap decision: `flow s` (P keeps sign `s` across the gap/ray)
  or `graft s₁ s₂` (one root inside; signs on the two sides). `sP` lists P's sign at
  each sample. In the next stage these are read off the 2d-2b augmented data (transfer
  entries + branch end signs); here they are inputs.
- **`graftWalk`** — the walk: every old column gets P's entry prepended; a grafted gap
  column expands to `[gap, point, gap]`. Pure list function.
- **`GraftData`** — the semantic contract for `(sP, plans)`, shaped exactly like
  `ColsFrom` (Option-barrier recursion along the samples).
- **`graftWalk_colsFrom`** — the walk theorem: some sample list `ξ'` (old samples plus
  the grafted roots) realizes the walked columns for `P :: F`; old samples are kept;
  EVERY root of a nonzero `spec g P` in the region lands in `ξ'` — a root inside a
  `flow` zone forces the zone sign to `0`, so P vanishes on an interval and is the zero
  polynomial (2d-2b's degeneracy lemma).
- **`realizes_graftWalk`** — the capstone: `Realizes g (P :: F) (graftWalk sP plans D)`.
  Sortedness of `ξ'` is recovered by the new utility `colsFrom_pairwise` (a `ColsFrom`
  diagram's samples are strictly increasing and clear the barrier).

The zero polynomial needs no special case: for `spec g P = 0` the all-zero annotation
is valid, the coverage clause is guarded by `spec g P ≠ 0`, and `Realizes` exempts zero
members from root coverage.

**Honest fence.** Second half of 2d-3 still owed: computing `(sP, plans)` from the
2d-2b transfer data and branch conditions, the Dershowitz–Manna descent, and
`DiagramPartition` for every family.
-/
import Sundogcert.DiagramGraft

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### Plans: the per-gap decisions as diagram-level data -/

/-- What happens to `P` on one gap or ray: constant sign, or one grafted root. -/
inductive GapPlan where
  | flow (s : SignType)
  | graft (s₁ s₂ : SignType)

/-- Expand one old column according to the plan, with P's entries prepended. -/
def expandPlan : GapPlan → List SignType → List (List SignType)
  | GapPlan.flow s, c => [s :: c]
  | GapPlan.graft s₁ s₂, c => [s₁ :: c, (0 : SignType) :: c, s₂ :: c]

/-- The walk: expand each gap column by its plan, prepend the sample sign to each
point column. -/
def graftWalk : List SignType → List GapPlan → List (List SignType) → List (List SignType)
  | sP, plans, cols =>
    match cols with
    | [] => []
    | [c] =>
      match plans with
      | pl :: _ => expandPlan pl c
      | [] => [c]
    | c :: cpt :: rest =>
      match sP, plans with
      | s :: sP', pl :: plans' => expandPlan pl c ++ (s :: cpt) :: graftWalk sP' plans' rest
      | _, _ => c :: cpt :: rest

/-! ### Validity: the semantic contract for an annotation -/

/-- The plan is true of `P` on the bounded gap `(lo, x)`. -/
def GapValid (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (lo : Option ℝ) (x : ℝ) : GapPlan → Prop
  | GapPlan.flow s =>
      ∀ y : ℝ, (∀ l ∈ lo, l < y) → y < x → SignType.sign ((spec g P).eval y) = s
  | GapPlan.graft s₁ s₂ =>
      ∃ ρ : ℝ, (∀ l ∈ lo, l < ρ) ∧ ρ < x ∧ (spec g P).eval ρ = 0 ∧
        (∀ y : ℝ, (∀ l ∈ lo, l < y) → y < ρ → SignType.sign ((spec g P).eval y) = s₁) ∧
        (∀ y : ℝ, ρ < y → y < x → SignType.sign ((spec g P).eval y) = s₂)

/-- The plan is true of `P` on the terminal ray beyond the barrier. -/
def RayValid (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (lo : Option ℝ) : GapPlan → Prop
  | GapPlan.flow s =>
      ∀ y : ℝ, (∀ l ∈ lo, l < y) → SignType.sign ((spec g P).eval y) = s
  | GapPlan.graft s₁ s₂ =>
      ∃ ρ : ℝ, (∀ l ∈ lo, l < ρ) ∧ (spec g P).eval ρ = 0 ∧
        (∀ y : ℝ, (∀ l ∈ lo, l < y) → y < ρ → SignType.sign ((spec g P).eval y) = s₁) ∧
        (∀ y : ℝ, ρ < y → SignType.sign ((spec g P).eval y) = s₂)

/-- The full annotation contract along the samples, `ColsFrom`-shaped. -/
def GraftData (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    Option ℝ → List ℝ → List SignType → List GapPlan → Prop
  | lo, [], sP, plans =>
      match sP, plans with
      | [], [pl] => RayValid g P lo pl
      | _, _ => False
  | lo, x :: xs, sP, plans =>
      match sP, plans with
      | s :: sP', pl :: plans' =>
          GapValid g P lo x pl ∧ SignType.sign ((spec g P).eval x) = s ∧
            GraftData g P (some x) xs sP' plans'
      | _, _ => False

/-! ### Utilities -/

/-- A `ColsFrom` sample list clears its barrier and is strictly increasing. -/
theorem colsFrom_pairwise (g : Fin n → ℝ) (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (D : List (List SignType)),
    ColsFrom g F lo ξ D →
    (∀ x ∈ ξ, ∀ l ∈ lo, l < x) ∧ ξ.Pairwise (· < ·) := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo D _h
    exact ⟨fun x hx => by simp at hx, List.Pairwise.nil⟩
  | cons x xs ih =>
    intro lo D h
    match D, h with
    | c :: cpt :: rest, ⟨hlox, _hgap, _hpt, hrest⟩ =>
      obtain ⟨hbar, hpw⟩ := ih (some x) rest hrest
      have hxlt : ∀ z ∈ xs, x < z := fun z hz => hbar z hz x rfl
      refine ⟨?_, List.Pairwise.cons hxlt hpw⟩
      intro z hz l hl
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hlox l hl
      · exact lt_trans (hlox l hl) (hxlt z hz')

/-- A zone of zero signs to the right of a root kills the polynomial. -/
private theorem zone_zero_absurd (g : Fin n → ℝ)
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) (hp : spec g P ≠ 0) {y c : ℝ}
    (hyc : y < c) (hzero : ∀ z : ℝ, y < z → z < c → (spec g P).eval z = 0) : False :=
  hp (spec_eq_zero_of_gap_roots g P hyc fun z hz => hzero z hz.1 hz.2)

/-! ### The walk theorem -/

/-- **The whole-diagram walk.** A valid annotation turns a realized `F`-diagram into a
realized `P :: F`-diagram with the walked columns: some sample list `ξ'` keeps all old
samples, catches every root of a nonzero `spec g P` in the region, and carries the
column pattern `graftWalk sP plans D`. -/
theorem graftWalk_colsFrom (g : Fin n → ℝ) (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    ∀ (ξ : List ℝ) (lo : Option ℝ) (D : List (List SignType))
      (sP : List SignType) (plans : List GapPlan),
    ColsFrom g F lo ξ D → GraftData g P lo ξ sP plans →
    ∃ ξ' : List ℝ,
      ColsFrom g (P :: F) lo ξ' (graftWalk sP plans D) ∧
      (∀ x ∈ ξ, x ∈ ξ') ∧
      (∀ y : ℝ, (∀ l ∈ lo, l < y) → spec g P ≠ 0 → (spec g P).eval y = 0 → y ∈ ξ') := by
  intro ξ
  induction ξ with
  | nil =>
    intro lo D sP plans hcols hdata
    match D, hcols with
    | [c], hray =>
      match sP, plans, hdata with
      | [], [GapPlan.flow s], hval =>
        refine ⟨[], ?_, ?_, ?_⟩
        · simp only [graftWalk, expandPlan]
          change ∀ y : ℝ, (∀ l ∈ lo, l < y) → signVec (P :: F) g y = s :: c
          intro y hy
          rw [signVec_cons, hray y hy, hval y hy]
        · intro z hz
          simp at hz
        · intro y hy hp h0
          exfalso
          have hs0 : s = 0 := by rw [← hval y hy, h0, sign_zero]
          refine zone_zero_absurd g P hp (lt_add_one y) ?_
          intro z hyz _hzc
          have hz := hval z (fun l hl => lt_trans (hy l hl) hyz)
          rw [hs0] at hz
          exact sign_eq_zero_iff.mp hz
      | [], [GapPlan.graft s₁ s₂], hval =>
        obtain ⟨ρ, hloρ, hρ0, hs₁, hs₂⟩ := hval
        have hsρ : SignType.sign ((spec g P).eval ρ) = 0 := by
          rw [hρ0]
          exact sign_zero
        refine ⟨[ρ], ?_, ?_, ?_⟩
        · simp only [graftWalk, expandPlan]
          refine ⟨hloρ, ?_, ?_, ?_⟩
          · intro y hy hyρ
            rw [signVec_cons, hray y hy, hs₁ y hy hyρ]
          · rw [signVec_cons, hray ρ hloρ, hsρ]
          · change ∀ y : ℝ, (∀ l ∈ (some ρ : Option ℝ), l < y) → signVec (P :: F) g y = s₂ :: c
            intro y hy
            have hρy : ρ < y := hy ρ rfl
            rw [signVec_cons, hray y (fun l hl => lt_trans (hloρ l hl) hρy), hs₂ y hρy]
        · intro z hz
          simp at hz
        · intro y hy hp h0
          rcases lt_trichotomy y ρ with hyρ | rfl | hρy
          · exfalso
            have hs0 : s₁ = 0 := by rw [← hs₁ y hy hyρ, h0, sign_zero]
            refine zone_zero_absurd g P hp hyρ ?_
            intro z hyz hzρ
            have hz := hs₁ z (fun l hl => lt_trans (hy l hl) hyz) hzρ
            rw [hs0] at hz
            exact sign_eq_zero_iff.mp hz
          · exact List.mem_singleton_self y
          · exfalso
            have hs0 : s₂ = 0 := by rw [← hs₂ y hρy, h0, sign_zero]
            refine zone_zero_absurd g P hp (lt_add_one y) ?_
            intro z hyz _hzc
            have hz := hs₂ z (lt_trans hρy hyz)
            rw [hs0] at hz
            exact sign_eq_zero_iff.mp hz
  | cons x xs ih =>
    intro lo D sP plans hcols hdata
    match D, hcols with
    | c :: cpt :: rest, ⟨hlox, hgap, hpt, hrest⟩ =>
      match sP, plans, hdata with
      | s :: sP', GapPlan.flow s₀ :: plans', ⟨hgv, hsx, hdata'⟩ =>
        obtain ⟨ξ'', hcols'', hmem'', hcov''⟩ := ih (some x) rest sP' plans' hrest hdata'
        refine ⟨x :: ξ'', ?_, ?_, ?_⟩
        · simp only [graftWalk, expandPlan, List.cons_append, List.nil_append]
          refine ⟨hlox, ?_, ?_, hcols''⟩
          · intro y hy hyx
            rw [signVec_cons, hgap y hy hyx, hgv y hy hyx]
          · rw [signVec_cons, hpt, hsx]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (hmem'' z hz'))
        · intro y hy hp h0
          rcases lt_trichotomy y x with hyx | rfl | hxy
          · exfalso
            have hs0 : s₀ = 0 := by rw [← hgv y hy hyx, h0, sign_zero]
            refine zone_zero_absurd g P hp hyx ?_
            intro z hyz hzx
            have hz := hgv z (fun l hl => lt_trans (hy l hl) hyz) hzx
            rw [hs0] at hz
            exact sign_eq_zero_iff.mp hz
          · exact List.mem_cons.mpr (Or.inl rfl)
          · refine List.mem_cons.mpr (Or.inr (hcov'' y ?_ hp h0))
            intro l hl
            rw [Option.mem_def, Option.some.injEq] at hl
            subst hl
            exact hxy
      | s :: sP', GapPlan.graft s₁ s₂ :: plans', ⟨hgv, hsx, hdata'⟩ =>
        obtain ⟨ρ, hloρ, hρx, hρ0, hs₁, hs₂⟩ := hgv
        obtain ⟨ξ'', hcols'', hmem'', hcov''⟩ := ih (some x) rest sP' plans' hrest hdata'
        have hsρ : SignType.sign ((spec g P).eval ρ) = 0 := by
          rw [hρ0]
          exact sign_zero
        refine ⟨ρ :: x :: ξ'', ?_, ?_, ?_⟩
        · simp only [graftWalk, expandPlan, List.cons_append, List.nil_append]
          refine ⟨hloρ, ?_, ?_, ?_⟩
          · intro y hy hyρ
            rw [signVec_cons, hgap y hy (lt_trans hyρ hρx), hs₁ y hy hyρ]
          · rw [signVec_cons, hgap ρ hloρ hρx, hsρ]
          · refine ⟨some_barrier hρx, ?_, ?_, hcols''⟩
            · intro y hy hyx
              have hρy : ρ < y := hy ρ rfl
              rw [signVec_cons, hgap y (fun l hl => lt_trans (hloρ l hl) hρy) hyx,
                hs₂ y hρy hyx]
            · rw [signVec_cons, hpt, hsx]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (hmem'' z hz'))))
        · intro y hy hp h0
          rcases lt_trichotomy y ρ with hyρ | rfl | hρy
          · exfalso
            have hs0 : s₁ = 0 := by rw [← hs₁ y hy hyρ, h0, sign_zero]
            refine zone_zero_absurd g P hp hyρ ?_
            intro z hyz hzρ
            have hz := hs₁ z (fun l hl => lt_trans (hy l hl) hyz) hzρ
            rw [hs0] at hz
            exact sign_eq_zero_iff.mp hz
          · exact List.mem_cons.mpr (Or.inl rfl)
          · rcases lt_trichotomy y x with hyx | rfl | hxy
            · exfalso
              have hs0 : s₂ = 0 := by rw [← hs₂ y hρy hyx, h0, sign_zero]
              refine zone_zero_absurd g P hp hyx ?_
              intro z hyz hzx
              have hz := hs₂ z (lt_trans hρy hyz) hzx
              rw [hs0] at hz
              exact sign_eq_zero_iff.mp hz
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
            · refine List.mem_cons.mpr
                (Or.inr (List.mem_cons.mpr (Or.inr (hcov'' y ?_ hp h0))))
              intro l hl
              rw [Option.mem_def, Option.some.injEq] at hl
              subst hl
              exact hxy

/-! ### The capstone -/

/-- **The walked diagram is realized.** From a realized `F`-diagram and a valid
annotation, `P :: F` realizes `graftWalk sP plans D` — an explicit function of
diagram-level data. -/
theorem realizes_graftWalk {g : Fin n → ℝ} {P : Polynomial (MvPolynomial (Fin n) ℝ)}
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))} {ξ : List ℝ}
    {D : List (List SignType)} {sP : List SignType} {plans : List GapPlan}
    (hroots : ∀ Q ∈ F, spec g Q ≠ 0 → ∀ y : ℝ, (spec g Q).IsRoot y → y ∈ ξ)
    (hcols : ColsFrom g F none ξ D)
    (hdata : GraftData g P none ξ sP plans) :
    Realizes g (P :: F) (graftWalk sP plans D) := by
  obtain ⟨ξ', hcols', hmem, hcov⟩ :=
    graftWalk_colsFrom g P F ξ none D sP plans hcols hdata
  refine ⟨ξ', (colsFrom_pairwise g (P :: F) ξ' none (graftWalk sP plans D) hcols').2,
    ?_, hcols'⟩
  intro Q hQ hQ0 y hy
  rcases List.mem_cons.mp hQ with rfl | hQ'
  · exact hcov y (fun l hl => by simp at hl) hQ0 hy
  · exact hmem y (hroots Q hQ' hQ0 y hy)

end Sundog.TarskiQE
