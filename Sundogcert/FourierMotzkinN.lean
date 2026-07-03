/-
# O-min lane R4-B3: n-dimensional Fourier–Motzkin — eliminate the last variable.

The projection step for the n-dimensional semilinear class: `projSLN : SLN (n+1) → SLN n` with

  `(projSLN S).toSet = {g | ∃ y, Fin.snoc g y ∈ S.toSet}`   (`projSLN_toSet`)

— the `definable_proj` axiom shape for the coming `OMinStructure` instance, verbatim.

**The port.** The dims-2 architecture (`FourierMotzkin`) transfers with the atom's front value
`P := (∑ i, a (castSucc i) · g i) + c` opaque, exactly as pre-registered:

- `val_snoc` is the only place the last variable is split out (`Fin.sum_univ_castSucc`):
  the value at `snoc g y` is `P + b·y` with `b := a (last n)`.
- one linearity lemma (`combo_val`) serves the pairwise atoms **and** both substitution kinds:
  `∑ (X·u − Y·v)·g + (X·e − Y·f) = X·P_u − Y·P_v`.
- the value-level comparison lemmas are restated with opaque `P` (`pos_iff_bnd_lt`,
  `pos_iff_lt_bnd`, `pairP_lt_iff`) — cleaner than the dims-2 originals;
  `listMax`/`listMin`/`exists_witness` import verbatim from `FourierMotzkin`.
- elimination per cell: an equality pin with `b ≠ 0` substitutes (×`b²`, sign-free); otherwise
  strict atoms split by the sign of `b` into lower/upper bounds, and `∃ y` ⟺ the `y`-free part
  ∧ the division-free pairwise comparisons, with the explicit between-the-bounds witness.

The pre-registered falsifier `FMN_FRONT_LEAK` (a dims-2 proof secretly needing the concrete
`a·x + c` shape) is the thing this module tests; candidate spots were the pin identities, which
became `combo_val` + pure real algebra (`substP_gt`/`substP_eq`).

**Honest fence.** One elimination step (`n+1 → n`); iterating it per variable is B4-adjacent
bookkeeping when needed. No instance yet — that is B4.
-/
import Sundogcert.SemilinearN
import Sundogcert.FourierMotzkin

namespace Sundog.FourierMotzkinN

open Sundog.SemilinearN Sundog.FourierMotzkin

variable {n : ℕ}

/-! ### The front/last split and the shared linearity lemma -/

/-- The value at `snoc g y`: front value plus `b·y` — the only place the last variable is
split out. -/
private theorem val_snoc (a : Fin (n + 1) → ℝ) (c : ℝ) (g : Fin n → ℝ) (y : ℝ) :
    (∑ i, a i * (Fin.snoc g y : Fin (n + 1) → ℝ) i) + c
      = ((∑ i, a (Fin.castSucc i) * g i) + c) + a (Fin.last n) * y := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- The shared linearity lemma: a coefficient-combination row evaluates to the combination of
the front values. Serves the pairwise atoms and both substitution kinds. -/
private theorem combo_val (X Y : ℝ) (u v : Fin n → ℝ) (e f : ℝ) (g : Fin n → ℝ) :
    (∑ k, (X * u k - Y * v k) * g k) + (X * e - Y * f)
      = X * ((∑ k, u k * g k) + e) - Y * ((∑ k, v k * g k) + f) := by
  have h : (∑ k, (X * u k - Y * v k) * g k)
      = X * (∑ k, u k * g k) - Y * (∑ k, v k * g k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  ring

/-! ### Value-level comparison lemmas, opaque-front form -/

private theorem pos_iff_bnd_lt {P b y : ℝ} (hb : 0 < b) : 0 < P + b * y ↔ -P / b < y := by
  rw [div_lt_iff₀ hb]
  constructor <;> intro h <;> nlinarith [h]

private theorem pos_iff_lt_bnd {P b y : ℝ} (hb : b < 0) : 0 < P + b * y ↔ y < -P / b := by
  rw [lt_div_iff_of_neg hb]
  constructor <;> intro h <;> nlinarith [h]

private theorem pairP_lt_iff {Pi bi Pj bj : ℝ} (hbi : 0 < bi) (hbj : bj < 0) :
    -Pi / bi < -Pj / bj ↔ 0 < bi * Pj - bj * Pi := by
  rw [div_lt_iff₀ hbi, div_mul_eq_mul_div, lt_div_iff_of_neg hbj]
  constructor <;> intro h <;> nlinarith [h]

private theorem substP_gt {b b' P' Pp y : ℝ} (hy : Pp + b * y = 0) :
    b * b * P' - b * b' * Pp = (b * b) * (P' + b' * y) := by
  have h : Pp = -(b * y) := by linarith
  rw [h]
  ring

private theorem substP_eq {b b' P' Pp y : ℝ} (hy : Pp + b * y = 0) :
    b * P' - b' * Pp = b * (P' + b' * y) := by
  have h : Pp = -(b * y) := by linarith
  rw [h]
  ring

/-! ### The elimination data of a cell -/

/-- The `y`-free part (last coefficient zero), mapped down to `n`-variable atoms. -/
noncomputable def freePartN (C : CellN (n + 1)) : CellN n := C.filterMap fun A =>
  match A with
  | .gt a c => if a (Fin.last n) = 0 then some (.gt (fun i => a (Fin.castSucc i)) c) else none
  | .eq a c => if a (Fin.last n) = 0 then some (.eq (fun i => a (Fin.castSucc i)) c) else none

/-- The lower-bound atoms: strict, positive last coefficient. -/
noncomputable def lowersN (C : CellN (n + 1)) : List ((Fin (n + 1) → ℝ) × ℝ) :=
  C.filterMap fun A =>
    match A with
    | .gt a c => if 0 < a (Fin.last n) then some (a, c) else none
    | .eq _ _ => none

/-- The upper-bound atoms: strict, negative last coefficient. -/
noncomputable def uppersN (C : CellN (n + 1)) : List ((Fin (n + 1) → ℝ) × ℝ) :=
  C.filterMap fun A =>
    match A with
    | .gt a c => if a (Fin.last n) < 0 then some (a, c) else none
    | .eq _ _ => none

/-- The pairwise lower-vs-upper comparison atoms (division-free). -/
noncomputable def pairAtomsN (C : CellN (n + 1)) : CellN n :=
  (lowersN C).flatMap fun ti => (uppersN C).map fun tj =>
    .gt (fun k => ti.1 (Fin.last n) * tj.1 (Fin.castSucc k)
          - tj.1 (Fin.last n) * ti.1 (Fin.castSucc k))
      (ti.1 (Fin.last n) * tj.2 - tj.1 (Fin.last n) * ti.2)

/-- The first equality atom with nonzero last coefficient, if any (the pin). -/
noncomputable def eqPinN? : CellN (n + 1) → Option ((Fin (n + 1) → ℝ) × ℝ)
  | [] => none
  | .gt _ _ :: C => eqPinN? C
  | .eq a c :: C => if a (Fin.last n) ≠ 0 then some (a, c) else eqPinN? C

/-- Substitute the pinned last variable into an atom; inequalities multiply through by
`b·b > 0` (sign-free), equalities by `b`. -/
def substPinN (a : Fin (n + 1) → ℝ) (c : ℝ) : AtomN (n + 1) → AtomN n
  | .gt a' c' => .gt
      (fun k => a (Fin.last n) * a (Fin.last n) * a' (Fin.castSucc k)
        - a (Fin.last n) * a' (Fin.last n) * a (Fin.castSucc k))
      (a (Fin.last n) * a (Fin.last n) * c' - a (Fin.last n) * a' (Fin.last n) * c)
  | .eq a' c' => .eq
      (fun k => a (Fin.last n) * a' (Fin.castSucc k) - a' (Fin.last n) * a (Fin.castSucc k))
      (a (Fin.last n) * c' - a' (Fin.last n) * c)

/-- Eliminate the last variable from one cell (a single `n`-variable cell either way). -/
noncomputable def projCellN (C : CellN (n + 1)) : CellN n :=
  match eqPinN? C with
  | some (a, c) => C.map (substPinN a c)
  | none => freePartN C ++ pairAtomsN C

/-- Eliminate per cell across the presentation. -/
noncomputable def projSLN (S : SLN (n + 1)) : SLN n := S.map projCellN

/-! ### Specs of the elimination data -/

theorem eqPinN?_some {C : CellN (n + 1)} {a : Fin (n + 1) → ℝ} {c : ℝ}
    (h : eqPinN? C = some (a, c)) : AtomN.eq a c ∈ C ∧ a (Fin.last n) ≠ 0 := by
  induction C with
  | nil => simp [eqPinN?] at h
  | cons A C ih =>
    cases A with
    | gt a' c' =>
      rw [eqPinN?] at h
      obtain ⟨hm, hb⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hb⟩
    | eq a' c' =>
      by_cases hb' : a' (Fin.last n) ≠ 0
      · rw [eqPinN?, if_pos hb'] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, hb'⟩
      · rw [eqPinN?, if_neg hb'] at h
        obtain ⟨hm, hb⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hm, hb⟩

theorem eqPinN?_none {C : CellN (n + 1)} (h : eqPinN? C = none) :
    ∀ (a : Fin (n + 1) → ℝ) (c : ℝ), AtomN.eq a c ∈ C → a (Fin.last n) = 0 := by
  induction C with
  | nil =>
    intro a c hm
    exact absurd hm List.not_mem_nil
  | cons A C ih =>
    cases A with
    | gt a' c' =>
      rw [eqPinN?] at h
      intro a c hm
      rcases List.mem_cons.mp hm with heq | hm'
      · simp at heq
      · exact ih h a c hm'
    | eq a' c' =>
      by_cases hb' : a' (Fin.last n) ≠ 0
      · rw [eqPinN?, if_pos hb'] at h
        simp at h
      · rw [eqPinN?, if_neg hb'] at h
        intro a c hm
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with h1 h2
          subst h1
          exact not_ne_iff.mp hb'
        · exact ih h a c hm'

theorem mem_lowersN {C : CellN (n + 1)} {a : Fin (n + 1) → ℝ} {c : ℝ} :
    (a, c) ∈ lowersN C ↔ AtomN.gt a c ∈ C ∧ 0 < a (Fin.last n) := by
  unfold lowersN
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, hfA⟩
    cases A with
    | gt a' c' =>
      dsimp only at hfA
      by_cases h0 : 0 < a' (Fin.last n)
      · rw [if_pos h0] at hfA
        simp only [Option.some.injEq, Prod.mk.injEq] at hfA
        obtain ⟨rfl, rfl⟩ := hfA
        exact ⟨hA, h0⟩
      · rw [if_neg h0] at hfA
        simp at hfA
    | eq a' c' => simp at hfA
  · rintro ⟨hA, hb⟩
    exact ⟨.gt a c, hA, by simp [hb]⟩

theorem mem_uppersN {C : CellN (n + 1)} {a : Fin (n + 1) → ℝ} {c : ℝ} :
    (a, c) ∈ uppersN C ↔ AtomN.gt a c ∈ C ∧ a (Fin.last n) < 0 := by
  unfold uppersN
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, hfA⟩
    cases A with
    | gt a' c' =>
      dsimp only at hfA
      by_cases h0 : a' (Fin.last n) < 0
      · rw [if_pos h0] at hfA
        simp only [Option.some.injEq, Prod.mk.injEq] at hfA
        obtain ⟨rfl, rfl⟩ := hfA
        exact ⟨hA, h0⟩
      · rw [if_neg h0] at hfA
        simp at hfA
    | eq a' c' => simp at hfA
  · rintro ⟨hA, hb⟩
    exact ⟨.gt a c, hA, by simp [hb]⟩

/-! ### The substitution case -/

theorem substPinN_holds_iff {a : Fin (n + 1) → ℝ} {c : ℝ} (hb : a (Fin.last n) ≠ 0)
    {g : Fin n → ℝ} {y : ℝ}
    (hy : ((∑ i, a (Fin.castSucc i) * g i) + c) + a (Fin.last n) * y = 0)
    (A : AtomN (n + 1)) :
    (substPinN a c A).holds g ↔ A.holds (Fin.snoc g y) := by
  have hb2 : 0 < a (Fin.last n) * a (Fin.last n) := mul_self_pos.mpr hb
  cases A with
  | gt a' c' =>
    simp only [substPinN, AtomN.holds]
    rw [val_snoc, combo_val, substP_gt hy]
    exact ⟨fun h => by nlinarith [h, hb2], fun h => mul_pos hb2 h⟩
  | eq a' c' =>
    simp only [substPinN, AtomN.holds]
    rw [val_snoc, combo_val, substP_eq hy]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hb
      · exact h'
    · intro h
      rw [h, mul_zero]

/-! ### The elimination is correct -/

/-- The bound value of a strict atom with nonzero last coefficient. -/
noncomputable def bndN (g : Fin n → ℝ) (t : (Fin (n + 1) → ℝ) × ℝ) : ℝ :=
  -((∑ i, t.1 (Fin.castSucc i) * g i) + t.2) / t.1 (Fin.last n)

/-- **Fourier–Motzkin, per cell**: the projected `n`-variable cell holds at `g` iff some `y`
completes `g` in the `(n+1)`-variable cell. -/
theorem projCellN_correct (C : CellN (n + 1)) (g : Fin n → ℝ) :
    cellHoldsN (projCellN C) g ↔ ∃ y : ℝ, cellHoldsN C (Fin.snoc g y) := by
  cases hpin : eqPinN? C with
  | some t =>
    obtain ⟨a, c⟩ := t
    rw [show projCellN C = C.map (substPinN a c) by unfold projCellN; rw [hpin]]
    obtain ⟨hpinC, hb⟩ := eqPinN?_some hpin
    constructor
    · intro h1
      refine ⟨-((∑ i, a (Fin.castSucc i) * g i) + c) / a (Fin.last n), ?_⟩
      have hy : ((∑ i, a (Fin.castSucc i) * g i) + c)
          + a (Fin.last n) * (-((∑ i, a (Fin.castSucc i) * g i) + c) / a (Fin.last n)) = 0 := by
        field_simp
        ring
      intro A hA
      exact (substPinN_holds_iff hb hy A).mp (h1 _ (List.mem_map_of_mem hA))
    · rintro ⟨y, h2⟩
      have hy : ((∑ i, a (Fin.castSucc i) * g i) + c) + a (Fin.last n) * y = 0 := by
        have := h2 _ hpinC
        simp only [AtomN.holds] at this
        rw [val_snoc] at this
        exact this
      intro A₁ hA₁
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hA₁
      exact (substPinN_holds_iff hb hy A).mpr (h2 A hA)
  | none =>
    rw [show projCellN C = freePartN C ++ pairAtomsN C by unfold projCellN; rw [hpin]]
    have hnone := eqPinN?_none hpin
    constructor
    · intro h1
      have hpairwise : ∀ l ∈ (lowersN C).map (bndN g), ∀ u ∈ (uppersN C).map (bndN g),
          l < u := by
        intro l hl u hu
        obtain ⟨⟨ai, ci⟩, hlo, rfl⟩ := List.mem_map.mp hl
        obtain ⟨⟨aj, cj⟩, hup, rfl⟩ := List.mem_map.mp hu
        have hbi := (mem_lowersN.mp hlo).2
        have hbj := (mem_uppersN.mp hup).2
        have hmem : (AtomN.gt
            (fun k => ai (Fin.last n) * aj (Fin.castSucc k)
              - aj (Fin.last n) * ai (Fin.castSucc k))
            (ai (Fin.last n) * cj - aj (Fin.last n) * ci)) ∈ pairAtomsN C :=
          List.mem_flatMap.mpr ⟨(ai, ci), hlo, List.mem_map.mpr ⟨(aj, cj), hup, rfl⟩⟩
        have hatom := h1 _ (List.mem_append_right _ hmem)
        simp only [AtomN.holds] at hatom
        rw [combo_val] at hatom
        simp only [bndN]
        exact (pairP_lt_iff hbi hbj).mpr hatom
      obtain ⟨y, hlow, hup⟩ := exists_witness _ _ hpairwise
      refine ⟨y, ?_⟩
      intro A hA
      cases A with
      | gt a c =>
        rcases lt_trichotomy (a (Fin.last n)) 0 with hb | hb | hb
        · have hmem : (a, c) ∈ uppersN C := mem_uppersN.mpr ⟨hA, hb⟩
          have hlt := hup _ (List.mem_map_of_mem hmem)
          simp only [bndN] at hlt
          simp only [AtomN.holds]
          rw [val_snoc]
          exact (pos_iff_lt_bnd hb).mpr hlt
        · have hmem : (AtomN.gt (fun i => a (Fin.castSucc i)) c) ∈ freePartN C := by
            unfold freePartN
            exact List.mem_filterMap.mpr ⟨.gt a c, hA, by simp [hb]⟩
          have hfree := h1 _ (List.mem_append_left _ hmem)
          simp only [AtomN.holds] at hfree
          simp only [AtomN.holds]
          rw [val_snoc, hb]
          linarith
        · have hmem : (a, c) ∈ lowersN C := mem_lowersN.mpr ⟨hA, hb⟩
          have hlt := hlow _ (List.mem_map_of_mem hmem)
          simp only [bndN] at hlt
          simp only [AtomN.holds]
          rw [val_snoc]
          exact (pos_iff_bnd_lt hb).mpr hlt
      | eq a c =>
        have hb : a (Fin.last n) = 0 := hnone a c hA
        have hmem : (AtomN.eq (fun i => a (Fin.castSucc i)) c) ∈ freePartN C := by
          unfold freePartN
          exact List.mem_filterMap.mpr ⟨.eq a c, hA, by simp [hb]⟩
        have hfree := h1 _ (List.mem_append_left _ hmem)
        simp only [AtomN.holds] at hfree
        simp only [AtomN.holds]
        rw [val_snoc, hb]
        linarith
    · rintro ⟨y, h2⟩
      intro A₁ hA₁
      rcases List.mem_append.mp hA₁ with hf | hp
      · unfold freePartN at hf
        obtain ⟨A, hA, hfA⟩ := List.mem_filterMap.mp hf
        cases A with
        | gt a c =>
          dsimp only at hfA
          by_cases hb : a (Fin.last n) = 0
          · rw [if_pos hb] at hfA
            simp only [Option.some.injEq] at hfA
            subst hfA
            have := h2 _ hA
            simp only [AtomN.holds] at this ⊢
            rw [val_snoc, hb] at this
            linarith
          · rw [if_neg hb] at hfA
            simp at hfA
        | eq a c =>
          dsimp only at hfA
          by_cases hb : a (Fin.last n) = 0
          · rw [if_pos hb] at hfA
            simp only [Option.some.injEq] at hfA
            subst hfA
            have := h2 _ hA
            simp only [AtomN.holds] at this ⊢
            rw [val_snoc, hb] at this
            linarith
          · rw [if_neg hb] at hfA
            simp at hfA
      · unfold pairAtomsN at hp
        obtain ⟨⟨ai, ci⟩, hlo, hp'⟩ := List.mem_flatMap.mp hp
        obtain ⟨⟨aj, cj⟩, hup, rfl⟩ := List.mem_map.mp hp'
        obtain ⟨hloC, hbi⟩ := mem_lowersN.mp hlo
        obtain ⟨hupC, hbj⟩ := mem_uppersN.mp hup
        have hi := h2 _ hloC
        have hj := h2 _ hupC
        simp only [AtomN.holds] at hi hj
        rw [val_snoc] at hi hj
        simp only [AtomN.holds]
        rw [combo_val]
        nlinarith [mul_pos (neg_pos.mpr hbj) hi, mul_pos hbi hj]

/-- **Fourier–Motzkin, per presentation**: projection commutes with union. -/
theorem projSLN_correct (S : SLN (n + 1)) (g : Fin n → ℝ) :
    slHoldsN (projSLN S) g ↔ ∃ y : ℝ, slHoldsN S (Fin.snoc g y) := by
  unfold projSLN slHoldsN
  constructor
  · rintro ⟨C₁, hC₁, h⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC₁
    obtain ⟨y, hy⟩ := (projCellN_correct C g).mp h
    exact ⟨y, C, hC, hy⟩
  · rintro ⟨y, C, hC, h⟩
    exact ⟨projCellN C, List.mem_map_of_mem hC, (projCellN_correct C g).mpr ⟨y, h⟩⟩

/-- **B3 headline, in the binding `OMinStructure` axiom shape**: the projected presentation
presents exactly `{g | ∃ y, Fin.snoc g y ∈ toSet S}`. -/
theorem projSLN_toSet (S : SLN (n + 1)) :
    (projSLN S).toSet = {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ S.toSet} := by
  ext g
  exact projSLN_correct S g

end Sundog.FourierMotzkinN
