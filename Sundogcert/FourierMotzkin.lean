/-
# O-min ladder R3-semilinear (part 2): Fourier–Motzkin — projection closure, 2 → 1.

The projection theorem for the semilinear class: `projSL : SL₂ → SL₁` with

  `slHolds₁ (projSL S) x ↔ ∃ y, slHolds₂ S x y`   (`projSL_correct`)

so the projection of every 2-D semilinear set is 1-D semilinear, hence **tame**
(`proj_semilinear_tame`) — the o-minimal structure axiom "projections of definable sets are
definable", machine-checked for the semilinear reduct in dimensions 2 → 1. Together with part 1's
boolean closure this makes the semilinear class a genuine structure in dimensions 1–2.

**The elimination, per cell.** If some equality atom has a `y`-coefficient (`eqPin?`), it pins
`y = −(a·x + c)/b`: substitute into every atom (`substAtom`; multiplying through by `b·b > 0`
keeps inequalities sign-free). Otherwise the strict atoms split by the sign of the
`y`-coefficient into lower bounds `L_i(x) < y`, upper bounds `y < U_j(x)`, and `y`-free atoms;
`∃ y` holds iff the `y`-free part does and every `L_i(x) < U_j(x)` — each pairwise comparison a
strict linear atom in `x` (`pair_lt_iff`, division-free by cross-multiplication). The witness for
⟸ is explicit: strictly between the largest lower and the smallest upper bound
(`exists_witness`, four boundedness cases) — density of ℝ and strictness are what make the
midpoint work. The pre-registered falsifier `FM_WITNESS_GAP` (the witness construction fails to
close over list syntax) did **not** fire.

**Honest fence.** Dimensions 2 → 1 only; the n-dimensional elimination is the same per-variable
step iterated (named, not claimed). Everything is at the presentation level — the class of
`SL₂`-presented sets — with semantics-level correctness; no claim about which sets admit such
presentations (the ReLU-`Net 2` bridge is the named follow-on).
-/
import Sundogcert.Semilinear

namespace Sundog.FourierMotzkin

open Sundog.OMinimalOne Sundog.Semilinear

/-! ### List max/min with explicit seeds -/

def listMax (v : ℝ) : List ℝ → ℝ
  | [] => v
  | w :: ws => listMax (max v w) ws

def listMin (v : ℝ) : List ℝ → ℝ
  | [] => v
  | w :: ws => listMin (min v w) ws

theorem le_listMax_left (v : ℝ) (l : List ℝ) : v ≤ listMax v l := by
  induction l generalizing v with
  | nil => simp [listMax]
  | cons w ws ih => exact le_trans (le_max_left v w) (ih (max v w))

theorem le_listMax_of_mem {u v : ℝ} {l : List ℝ} (h : u ∈ l) : u ≤ listMax v l := by
  induction l generalizing v with
  | nil => exact absurd h List.not_mem_nil
  | cons w ws ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_trans (le_max_right v u) (le_listMax_left _ _)
    · exact ih h'

theorem listMax_lt {v z : ℝ} {l : List ℝ} (hv : v < z) (hl : ∀ u ∈ l, u < z) :
    listMax v l < z := by
  induction l generalizing v with
  | nil => exact hv
  | cons w ws ih =>
    exact ih (max_lt hv (hl w List.mem_cons_self))
      (fun u hu => hl u (List.mem_cons_of_mem _ hu))

theorem listMin_le_left (v : ℝ) (l : List ℝ) : listMin v l ≤ v := by
  induction l generalizing v with
  | nil => simp [listMin]
  | cons w ws ih => exact le_trans (ih (min v w)) (min_le_left v w)

theorem listMin_le_of_mem {u v : ℝ} {l : List ℝ} (h : u ∈ l) : listMin v l ≤ u := by
  induction l generalizing v with
  | nil => exact absurd h List.not_mem_nil
  | cons w ws ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_trans (listMin_le_left (min v u) ws) (min_le_right v u)
    · exact ih h'

theorem lt_listMin {v z : ℝ} {l : List ℝ} (hv : z < v) (hl : ∀ u ∈ l, z < u) :
    z < listMin v l := by
  induction l generalizing v with
  | nil => exact hv
  | cons w ws ih =>
    exact ih (lt_min hv (hl w List.mem_cons_self))
      (fun u hu => hl u (List.mem_cons_of_mem _ hu))

/-- **The witness between the bounds.** Given pairwise `l < u` across two finite families, there
is a `y` strictly above every lower and strictly below every upper bound — density of ℝ, four
boundedness cases. This is the ⟸ heart of Fourier–Motzkin. -/
theorem exists_witness (lows ups : List ℝ)
    (h : ∀ l ∈ lows, ∀ u ∈ ups, l < u) :
    ∃ y : ℝ, (∀ l ∈ lows, l < y) ∧ (∀ u ∈ ups, y < u) := by
  rcases lows with _ | ⟨l₀, ls⟩ <;> rcases ups with _ | ⟨u₀, us⟩
  · exact ⟨0, by simp, by simp⟩
  · refine ⟨listMin u₀ us - 1, by simp, ?_⟩
    intro u hu
    have hge : listMin u₀ us ≤ u := by
      rcases List.mem_cons.mp hu with rfl | h'
      · exact listMin_le_left _ _
      · exact listMin_le_of_mem h'
    linarith
  · refine ⟨listMax l₀ ls + 1, ?_, by simp⟩
    intro l hl
    have hle : l ≤ listMax l₀ ls := by
      rcases List.mem_cons.mp hl with rfl | h'
      · exact le_listMax_left _ _
      · exact le_listMax_of_mem h'
    linarith
  · have hmm : listMax l₀ ls < listMin u₀ us := by
      apply listMax_lt
      · apply lt_listMin
        · exact h l₀ List.mem_cons_self u₀ List.mem_cons_self
        · intro u hu
          exact h l₀ List.mem_cons_self u (List.mem_cons_of_mem _ hu)
      · intro l hl
        apply lt_listMin
        · exact h l (List.mem_cons_of_mem _ hl) u₀ List.mem_cons_self
        · intro u hu
          exact h l (List.mem_cons_of_mem _ hl) u (List.mem_cons_of_mem _ hu)
    refine ⟨(listMax l₀ ls + listMin u₀ us) / 2, ?_, ?_⟩
    · intro l hl
      have hle : l ≤ listMax l₀ ls := by
        rcases List.mem_cons.mp hl with rfl | h'
        · exact le_listMax_left _ _
        · exact le_listMax_of_mem h'
      linarith
    · intro u hu
      have hge : listMin u₀ us ≤ u := by
        rcases List.mem_cons.mp hu with rfl | h'
        · exact listMin_le_left _ _
        · exact listMin_le_of_mem h'
      linarith

/-! ### Bound normal forms for strict atoms -/

/-- The bound value of a strict atom with nonzero `y`-coefficient. -/
noncomputable def bnd (x : ℝ) (t : ℝ × ℝ × ℝ) : ℝ := -(t.1 * x + t.2.2) / t.2.1

theorem holds_iff_bnd_lt {a b c x y : ℝ} (hb : 0 < b) :
    (Atom₂.gt a b c).holds x y ↔ -(a * x + c) / b < y := by
  simp only [Atom₂.holds]
  rw [div_lt_iff₀ hb]
  constructor <;> intro h <;> nlinarith [h]

theorem holds_iff_lt_bnd {a b c x y : ℝ} (hb : b < 0) :
    (Atom₂.gt a b c).holds x y ↔ y < -(a * x + c) / b := by
  simp only [Atom₂.holds]
  rw [lt_div_iff_of_neg hb]
  constructor <;> intro h <;> nlinarith [h]

/-- **The pairwise comparison is division-free** (cross-multiplication with the sign bookkeeping
absorbed into the coefficients). -/
theorem pair_lt_iff {ai bi ci aj bj cj x : ℝ} (hbi : 0 < bi) (hbj : bj < 0) :
    -(ai * x + ci) / bi < -(aj * x + cj) / bj ↔
      0 < (bi * aj - bj * ai) * x + (bi * cj - bj * ci) := by
  rw [div_lt_iff₀ hbi, div_mul_eq_mul_div, lt_div_iff_of_neg hbj]
  constructor <;> intro h <;> nlinarith [h]

/-! ### The elimination data of a cell -/

/-- The `y`-free part, mapped down to 1-D atoms. -/
noncomputable def freePart (C : Cell₂) : Cell₁ := C.filterMap fun A =>
  match A with
  | .gt a b c => if b = 0 then some (.gt a c) else none
  | .eq a b c => if b = 0 then some (.eq a c) else none

/-- The lower-bound atoms: strict, positive `y`-coefficient. -/
noncomputable def lowers (C : Cell₂) : List (ℝ × ℝ × ℝ) := C.filterMap fun A =>
  match A with
  | .gt a b c => if 0 < b then some (a, b, c) else none
  | .eq _ _ _ => none

/-- The upper-bound atoms: strict, negative `y`-coefficient. -/
noncomputable def uppers (C : Cell₂) : List (ℝ × ℝ × ℝ) := C.filterMap fun A =>
  match A with
  | .gt a b c => if b < 0 then some (a, b, c) else none
  | .eq _ _ _ => none

/-- The pairwise lower-vs-upper comparison atoms (the Fourier–Motzkin core). -/
noncomputable def pairAtoms (C : Cell₂) : Cell₁ :=
  (lowers C).flatMap fun ti => (uppers C).map fun tj =>
    .gt (ti.2.1 * tj.1 - tj.2.1 * ti.1) (ti.2.1 * tj.2.2 - tj.2.1 * ti.2.2)

/-- The first equality atom with a nonzero `y`-coefficient, if any (the pin). -/
noncomputable def eqPin? : Cell₂ → Option (ℝ × ℝ × ℝ)
  | [] => none
  | .gt _ _ _ :: C => eqPin? C
  | .eq a b c :: C => if b ≠ 0 then some (a, b, c) else eqPin? C

/-- Substitute the pinned `y = −(a·x+c)/b` into an atom; inequalities are multiplied through by
`b·b > 0` (sign-free), equalities by `b`. -/
def substAtom (a b c : ℝ) : Atom₂ → Atom₁
  | .gt a' b' c' => .gt (b * b * a' - b * b' * a) (b * b * c' - b * b' * c)
  | .eq a' b' c' => .eq (b * a' - b' * a) (b * c' - b' * c)

/-- Fourier–Motzkin elimination of `y` from one cell (a single 1-D cell either way). -/
noncomputable def projCell (C : Cell₂) : Cell₁ :=
  match eqPin? C with
  | some (a, b, c) => C.map (substAtom a b c)
  | none => freePart C ++ pairAtoms C

/-- Projection of a semilinear presentation: eliminate per cell. -/
noncomputable def projSL (S : SL₂) : SL₁ := S.map projCell

/-! ### Specs of the elimination data -/

theorem eqPin?_some {C : Cell₂} {a b c : ℝ} (h : eqPin? C = some (a, b, c)) :
    Atom₂.eq a b c ∈ C ∧ b ≠ 0 := by
  induction C with
  | nil => simp [eqPin?] at h
  | cons A C ih =>
    cases A with
    | gt a' b' c' =>
      rw [eqPin?] at h
      obtain ⟨hm, hb⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hb⟩
    | eq a' b' c' =>
      by_cases hb' : b' ≠ 0
      · rw [eqPin?, if_pos hb'] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self, hb'⟩
      · rw [eqPin?, if_neg hb'] at h
        obtain ⟨hm, hb⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hm, hb⟩

theorem eqPin?_none {C : Cell₂} (h : eqPin? C = none) :
    ∀ a b c : ℝ, Atom₂.eq a b c ∈ C → b = 0 := by
  induction C with
  | nil =>
    intro a b c hm
    exact absurd hm List.not_mem_nil
  | cons A C ih =>
    cases A with
    | gt a' b' c' =>
      rw [eqPin?] at h
      intro a b c hm
      rcases List.mem_cons.mp hm with heq | hm'
      · simp at heq
      · exact ih h a b c hm'
    | eq a' b' c' =>
      by_cases hb' : b' ≠ 0
      · rw [eqPin?, if_pos hb'] at h
        simp at h
      · rw [eqPin?, if_neg hb'] at h
        intro a b c hm
        rcases List.mem_cons.mp hm with heq | hm'
        · injection heq with h1 h2 h3
          subst h2
          exact not_ne_iff.mp hb'
        · exact ih h a b c hm'

theorem mem_lowers {C : Cell₂} {a b c : ℝ} :
    (a, b, c) ∈ lowers C ↔ Atom₂.gt a b c ∈ C ∧ 0 < b := by
  unfold lowers
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, hfA⟩
    cases A with
    | gt a' b' c' =>
      dsimp only at hfA
      by_cases h0 : 0 < b'
      · rw [if_pos h0] at hfA
        simp only [Option.some.injEq, Prod.mk.injEq] at hfA
        obtain ⟨rfl, rfl, rfl⟩ := hfA
        exact ⟨hA, h0⟩
      · rw [if_neg h0] at hfA
        simp at hfA
    | eq a' b' c' => simp at hfA
  · rintro ⟨hA, hb⟩
    exact ⟨.gt a b c, hA, by simp [hb]⟩

theorem mem_uppers {C : Cell₂} {a b c : ℝ} :
    (a, b, c) ∈ uppers C ↔ Atom₂.gt a b c ∈ C ∧ b < 0 := by
  unfold uppers
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨A, hA, hfA⟩
    cases A with
    | gt a' b' c' =>
      dsimp only at hfA
      by_cases h0 : b' < 0
      · rw [if_pos h0] at hfA
        simp only [Option.some.injEq, Prod.mk.injEq] at hfA
        obtain ⟨rfl, rfl, rfl⟩ := hfA
        exact ⟨hA, h0⟩
      · rw [if_neg h0] at hfA
        simp at hfA
    | eq a' b' c' => simp at hfA
  · rintro ⟨hA, hb⟩
    exact ⟨.gt a b c, hA, by simp [hb]⟩

/-! ### The substitution case -/

theorem substAtom_holds_iff {a b c x y : ℝ} (hb : b ≠ 0) (hy : a * x + b * y + c = 0)
    (A : Atom₂) : (substAtom a b c A).holds x ↔ A.holds x y := by
  have hb2 : 0 < b * b := mul_self_pos.mpr hb
  cases A with
  | gt a' b' c' =>
    simp only [substAtom, Atom₁.holds, Atom₂.holds]
    have hkey : (b * b * a' - b * b' * a) * x + (b * b * c' - b * b' * c)
        = (b * b) * (a' * x + b' * y + c') := by
      linear_combination (-(b * b')) * hy
    rw [hkey]
    exact ⟨fun h => by nlinarith [h, hb2], fun h => mul_pos hb2 h⟩
  | eq a' b' c' =>
    simp only [substAtom, Atom₁.holds, Atom₂.holds]
    have hkey : (b * a' - b' * a) * x + (b * c' - b' * c) = b * (a' * x + b' * y + c') := by
      linear_combination (-b') * hy
    rw [hkey]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hb
      · exact h'
    · intro h
      rw [h, mul_zero]

/-! ### The elimination is correct -/

/-- **Fourier–Motzkin, per cell**: the projected 1-D cell holds at `x` iff some `y` completes
`x` in the 2-D cell. -/
theorem projCell_correct (C : Cell₂) (x : ℝ) :
    cellHolds₁ (projCell C) x ↔ ∃ y, cellHolds₂ C x y := by
  cases hpin : eqPin? C with
  | some t =>
    obtain ⟨a, b, c⟩ := t
    rw [show projCell C = C.map (substAtom a b c) by unfold projCell; rw [hpin]]
    obtain ⟨hpinC, hb⟩ := eqPin?_some hpin
    constructor
    · intro h1
      refine ⟨-(a * x + c) / b, ?_⟩
      have hy : a * x + b * (-(a * x + c) / b) + c = 0 := by
        field_simp
        ring
      intro A hA
      exact (substAtom_holds_iff hb hy A).mp (h1 _ (List.mem_map_of_mem hA))
    · rintro ⟨y, h2⟩
      have hy : a * x + b * y + c = 0 := h2 _ hpinC
      intro A₁ hA₁
      obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hA₁
      exact (substAtom_holds_iff hb hy A).mpr (h2 A hA)
  | none =>
    rw [show projCell C = freePart C ++ pairAtoms C by unfold projCell; rw [hpin]]
    have hnone := eqPin?_none hpin
    constructor
    · intro h1
      have hpairwise : ∀ l ∈ (lowers C).map (bnd x), ∀ u ∈ (uppers C).map (bnd x), l < u := by
        intro l hl u hu
        obtain ⟨⟨ai, bi, ci⟩, hlo, rfl⟩ := List.mem_map.mp hl
        obtain ⟨⟨aj, bj, cj⟩, hup, rfl⟩ := List.mem_map.mp hu
        have hbi := (mem_lowers.mp hlo).2
        have hbj := (mem_uppers.mp hup).2
        have hmem : (Atom₁.gt (bi * aj - bj * ai) (bi * cj - bj * ci)) ∈ pairAtoms C :=
          List.mem_flatMap.mpr ⟨(ai, bi, ci), hlo,
            List.mem_map.mpr ⟨(aj, bj, cj), hup, rfl⟩⟩
        have hatom := h1 _ (List.mem_append_right _ hmem)
        simp only [Atom₁.holds] at hatom
        simp only [bnd]
        exact (pair_lt_iff hbi hbj).mpr hatom
      obtain ⟨y, hlow, hup⟩ := exists_witness _ _ hpairwise
      refine ⟨y, ?_⟩
      intro A hA
      cases A with
      | gt a b c =>
        rcases lt_trichotomy b 0 with hb | hb | hb
        · have hmem : (a, b, c) ∈ uppers C := mem_uppers.mpr ⟨hA, hb⟩
          have := hup _ (List.mem_map_of_mem hmem)
          simp only [bnd] at this
          exact (holds_iff_lt_bnd hb).mpr this
        · subst hb
          have hmem : Atom₁.gt a c ∈ freePart C := by
            unfold freePart
            exact List.mem_filterMap.mpr ⟨.gt a 0 c, hA, by simp⟩
          have := h1 _ (List.mem_append_left _ hmem)
          simp only [Atom₁.holds] at this
          simp only [Atom₂.holds]
          linarith
        · have hmem : (a, b, c) ∈ lowers C := mem_lowers.mpr ⟨hA, hb⟩
          have := hlow _ (List.mem_map_of_mem hmem)
          simp only [bnd] at this
          exact (holds_iff_bnd_lt hb).mpr this
      | eq a b c =>
        have hb : b = 0 := hnone a b c hA
        subst hb
        have hmem : Atom₁.eq a c ∈ freePart C := by
          unfold freePart
          exact List.mem_filterMap.mpr ⟨.eq a 0 c, hA, by simp⟩
        have := h1 _ (List.mem_append_left _ hmem)
        simp only [Atom₁.holds] at this
        simp only [Atom₂.holds]
        linarith
    · rintro ⟨y, h2⟩
      intro A₁ hA₁
      rcases List.mem_append.mp hA₁ with hf | hp
      · unfold freePart at hf
        obtain ⟨A, hA, hfA⟩ := List.mem_filterMap.mp hf
        cases A with
        | gt a b c =>
          dsimp only at hfA
          by_cases hb : b = 0
          · rw [if_pos hb] at hfA
            simp only [Option.some.injEq] at hfA
            subst hfA
            subst hb
            have := h2 _ hA
            simp only [Atom₂.holds] at this
            simp only [Atom₁.holds]
            linarith
          · rw [if_neg hb] at hfA
            simp at hfA
        | eq a b c =>
          dsimp only at hfA
          by_cases hb : b = 0
          · rw [if_pos hb] at hfA
            simp only [Option.some.injEq] at hfA
            subst hfA
            subst hb
            have := h2 _ hA
            simp only [Atom₂.holds] at this
            simp only [Atom₁.holds]
            linarith
          · rw [if_neg hb] at hfA
            simp at hfA
      · unfold pairAtoms at hp
        obtain ⟨⟨ai, bi, ci⟩, hlo, hp'⟩ := List.mem_flatMap.mp hp
        obtain ⟨⟨aj, bj, cj⟩, hup, rfl⟩ := List.mem_map.mp hp'
        obtain ⟨hloC, hbi⟩ := mem_lowers.mp hlo
        obtain ⟨hupC, hbj⟩ := mem_uppers.mp hup
        have hi := h2 _ hloC
        have hj := h2 _ hupC
        simp only [Atom₂.holds] at hi hj
        simp only [Atom₁.holds]
        nlinarith [mul_pos (neg_pos.mpr hbj) hi, mul_pos hbi hj]

/-- **Fourier–Motzkin, per presentation**: projection commutes with union. -/
theorem projSL_correct (S : SL₂) (x : ℝ) :
    slHolds₁ (projSL S) x ↔ ∃ y, slHolds₂ S x y := by
  unfold projSL slHolds₁ slHolds₂
  constructor
  · rintro ⟨C₁, hC₁, h⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC₁
    obtain ⟨y, hy⟩ := (projCell_correct C x).mp h
    exact ⟨y, C, hC, hy⟩
  · rintro ⟨y, C, hC, h⟩
    exact ⟨projCell C, List.mem_map_of_mem hC, (projCell_correct C x).mpr ⟨y, h⟩⟩

/-- **R3-semilinear headline: the projection axiom.** The projection of every 2-D semilinear set
is 1-D semilinear, hence tame — the o-minimal structure axiom for the semilinear reduct,
dimensions 2 → 1, machine-checked. -/
theorem proj_semilinear_tame (S : SL₂) : Tame {x | ∃ y, slHolds₂ S x y} := by
  have h : {x : ℝ | ∃ y, slHolds₂ S x y} = {x | slHolds₁ (projSL S) x} := by
    ext x
    exact (projSL_correct S x).symm
  rw [h]
  exact slHolds₁_tame (projSL S)

end Sundog.FourierMotzkin
