/-
# O-min lane R4-C1b: the sign partition — a finite cut-set with one behavior class per gap.

The six one-sided sign-class sets of a definable function (`rightAbove`/`rightBelow`/`rightEq`
and the left mirrors) are tame — each an instance of one of two formula **templates**
(`tame_right_template`/`tame_left_template`), so the six proofs are two-liners. The two-sided
local-behavior sets need **no new formulas**: neighbor-sense locally-increasing is exactly
`rightAbove ∩ leftBelow` (`locInc`), and likewise `locDec`, `locConst` — tame by intersection.
The bad set is the complement of the three.

Headline (`sign_partition`): there is a **finite cut-set** `F` — the four frontiers — such that
on every `F`-free open interval, exactly one of `locConst` / `locInc` / `locDec` / `badSet`
holds at *every* point: the four sets cover ℝ, each is full-or-empty on the gap
(`full_or_empty_on_window` = R2-N's `preconnected_split`), and the midpoint elects the class.

Also banked for C1d: the pointwise covers `right_sign_cover` / `left_sign_cover` (C1a's
trichotomies as set equalities).

**Honest fence.** The partition, not the theorem: gluing the good classes is C1c; showing the
bad set is finite (killing the bad gaps) is C1d.
-/
import Sundogcert.OMinimalTrichotomy

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalNormalForm

/-! ### Local snoc helpers (literal indices) -/

private theorem snocA (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocB (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 1 = y := by
  simp [Fin.snoc]

private theorem snocC (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocD (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocE (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 2 = y := by
  simp [Fin.snoc]

/-! ### One more formula combinator: value equality through the graph -/

namespace Fml

/-- `φ(x_i) = φ(x_j)`, with one `∃` over two graph atoms. -/
def eqGraph {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n) :
    Fml S n :=
  .ex (.and (graphAt hφ (Fin.castSucc i) (Fin.last n))
    (graphAt hφ (Fin.castSucc j) (Fin.last n)))

@[simp] theorem eval_eqGraph {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ)
    (i j : Fin n) (f : Fin n → ℝ) : (eqGraph hφ i j).eval f ↔ φ (f i) = φ (f j) := by
  simp only [eqGraph, eval, eval_graphAt, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨p, h1, h2⟩
    exact h1.trans h2.symm
  · intro h
    exact ⟨φ (f j), h, rfl⟩

end Fml

open Fml

/-! ### The two window templates -/

/-- Right-window template: `{x | ∃ v > x, ∀ y ∈ (x,v), Q x y}` is tame for any formula body
evaluating to `Q` on coordinates `(0, 2)`. -/
theorem tame_right_template {S : OMinStructure} (body : Fml S 3) {Q : ℝ → ℝ → Prop}
    (hbody : ∀ g : Fin 3 → ℝ, body.eval g ↔ Q (g 0) (g 2)) :
    Tame {x : ℝ | ∃ v, x < v ∧ ∀ y, x < y → y < v → Q x y} := by
  have h := Fml.tame_one (S := S)
    (Fml.ex (.and (ltAt 0 1) (Fml.all ((Fml.and (ltAt 0 2) (ltAt 2 1)).imp body))))
  have e : {x : ℝ | ∃ v, x < v ∧ ∀ y, x < y → y < v → Q x y}
      = {x : ℝ | Fml.eval (S := S) (n := 1)
          (Fml.ex (.and (ltAt 0 1) (Fml.all ((Fml.and (ltAt 0 2) (ltAt 2 1)).imp body))))
          (fun _ => x)} := by
    ext x
    simp only [Set.mem_setOf_eq, Fml.eval, eval_ltAt, eval_all, eval_imp, hbody,
      snocA, snocB, snocC, snocD, snocE, and_imp]
  rw [e]
  exact h

/-- Left-window template: `{x | ∃ u < x, ∀ y ∈ (u,x), Q x y}` is tame for any formula body
evaluating to `Q` on coordinates `(0, 2)`. -/
theorem tame_left_template {S : OMinStructure} (body : Fml S 3) {Q : ℝ → ℝ → Prop}
    (hbody : ∀ g : Fin 3 → ℝ, body.eval g ↔ Q (g 0) (g 2)) :
    Tame {x : ℝ | ∃ u, u < x ∧ ∀ y, u < y → y < x → Q x y} := by
  have h := Fml.tame_one (S := S)
    (Fml.ex (.and (ltAt 1 0) (Fml.all ((Fml.and (ltAt 1 2) (ltAt 2 0)).imp body))))
  have e : {x : ℝ | ∃ u, u < x ∧ ∀ y, u < y → y < x → Q x y}
      = {x : ℝ | Fml.eval (S := S) (n := 1)
          (Fml.ex (.and (ltAt 1 0) (Fml.all ((Fml.and (ltAt 1 2) (ltAt 2 0)).imp body))))
          (fun _ => x)} := by
    ext x
    simp only [Set.mem_setOf_eq, Fml.eval, eval_ltAt, eval_all, eval_imp, hbody,
      snocA, snocB, snocC, snocD, snocE, and_imp]
  rw [e]
  exact h

/-! ### The six one-sided sign-class sets -/

variable (φ : ℝ → ℝ)

/-- Eventually above `φ x` on a right window. -/
def rightAbove : Set ℝ := {x | ∃ v, x < v ∧ ∀ y, x < y → y < v → φ x < φ y}

/-- Eventually below `φ x` on a right window. -/
def rightBelow : Set ℝ := {x | ∃ v, x < v ∧ ∀ y, x < y → y < v → φ y < φ x}

/-- Eventually equal to `φ x` on a right window. -/
def rightEq : Set ℝ := {x | ∃ v, x < v ∧ ∀ y, x < y → y < v → φ y = φ x}

/-- Below `φ x` on a left window (rising into `x`). -/
def leftBelow : Set ℝ := {x | ∃ u, u < x ∧ ∀ y, u < y → y < x → φ y < φ x}

/-- Above `φ x` on a left window (falling into `x`). -/
def leftAbove : Set ℝ := {x | ∃ u, u < x ∧ ∀ y, u < y → y < x → φ x < φ y}

/-- Equal to `φ x` on a left window. -/
def leftEq : Set ℝ := {x | ∃ u, u < x ∧ ∀ y, u < y → y < x → φ y = φ x}

variable {φ}

theorem tame_rightAbove {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame (rightAbove φ) :=
  tame_right_template (ltGraph hφ 0 2) (fun g => eval_ltGraph hφ 0 2 g)

theorem tame_rightBelow {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame (rightBelow φ) :=
  tame_right_template (ltGraph hφ 2 0) (fun g => eval_ltGraph hφ 2 0 g)

theorem tame_rightEq {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame (rightEq φ) :=
  tame_right_template (eqGraph hφ 2 0) (fun g => eval_eqGraph hφ 2 0 g)

theorem tame_leftBelow {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame (leftBelow φ) :=
  tame_left_template (ltGraph hφ 2 0) (fun g => eval_ltGraph hφ 2 0 g)

theorem tame_leftAbove {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame (leftAbove φ) :=
  tame_left_template (ltGraph hφ 0 2) (fun g => eval_ltGraph hφ 0 2 g)

theorem tame_leftEq {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame (leftEq φ) :=
  tame_left_template (eqGraph hφ 2 0) (fun g => eval_eqGraph hφ 2 0 g)

/-! ### The pointwise covers (C1a's trichotomies as set equalities) -/

theorem right_sign_cover {S : OMinStructure} (hφ : S.DefinableFun φ) :
    rightAbove φ ∪ rightBelow φ ∪ rightEq φ = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true, rightAbove, rightBelow, rightEq,
    Set.mem_setOf_eq]
  rcases eventual_right_sign hφ x with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem left_sign_cover {S : OMinStructure} (hφ : S.DefinableFun φ) :
    leftBelow φ ∪ leftAbove φ ∪ leftEq φ = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true, leftBelow, leftAbove, leftEq,
    Set.mem_setOf_eq]
  rcases eventual_left_sign hφ x with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-! ### The two-sided behavior classes (intersections — no new formulas) -/

variable (φ)

/-- Neighbor-sense locally constant at `x`. -/
def locConst : Set ℝ := rightEq φ ∩ leftEq φ

/-- Neighbor-sense locally increasing at `x` (left neighbors below, right neighbors above). -/
def locInc : Set ℝ := rightAbove φ ∩ leftBelow φ

/-- Neighbor-sense locally decreasing at `x`. -/
def locDec : Set ℝ := rightBelow φ ∩ leftAbove φ

/-- The bad set: no coherent two-sided behavior. -/
def badSet : Set ℝ := (locConst φ ∪ locInc φ ∪ locDec φ)ᶜ

variable {φ}

theorem tame_locConst {S : OMinStructure} (hφ : S.DefinableFun φ) : Tame (locConst φ) :=
  tame_inter (tame_rightEq hφ) (tame_leftEq hφ)

theorem tame_locInc {S : OMinStructure} (hφ : S.DefinableFun φ) : Tame (locInc φ) :=
  tame_inter (tame_rightAbove hφ) (tame_leftBelow hφ)

theorem tame_locDec {S : OMinStructure} (hφ : S.DefinableFun φ) : Tame (locDec φ) :=
  tame_inter (tame_rightBelow hφ) (tame_leftAbove hφ)

theorem tame_badSet {S : OMinStructure} (hφ : S.DefinableFun φ) : Tame (badSet φ) :=
  tame_compl (tame_union (tame_union (tame_locConst hφ) (tame_locInc hφ)) (tame_locDec hφ))

/-! ### Full-or-empty on frontier-free windows, and the partition -/

/-- A frontier-free open window is entirely inside or entirely outside any set
(R2-N's `preconnected_split`, window form). -/
theorem full_or_empty_on_window {A : Set ℝ} {a b : ℝ}
    (hmiss : ∀ y ∈ Set.Ioo a b, y ∉ frontier A) :
    Set.Ioo a b ⊆ A ∨ Set.Ioo a b ∩ A = ∅ :=
  preconnected_split Set.ordConnected_Ioo.isPreconnected hmiss

/-- **The sign partition (C1b headline).** A finite cut-set `F` such that on every `F`-free
open interval, one behavior class — locally constant, locally increasing, locally decreasing,
or bad — holds at every point of the interval. -/
theorem sign_partition {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) :
    ∃ F : Finset ℝ, ∀ a b : ℝ, a < b → (∀ s ∈ F, s ∉ Set.Ioo a b) →
      Set.Ioo a b ⊆ locConst φ ∨ Set.Ioo a b ⊆ locInc φ ∨ Set.Ioo a b ⊆ locDec φ ∨
      Set.Ioo a b ⊆ badSet φ := by
  classical
  have hc := tame_locConst hφ
  have hi := tame_locInc hφ
  have hd := tame_locDec hφ
  have hb := tame_badSet hφ
  have hFfin : (frontier (locConst φ) ∪ frontier (locInc φ) ∪ frontier (locDec φ)
      ∪ frontier (badSet φ)).Finite := ((hc.union hi).union hd).union hb
  refine ⟨hFfin.toFinset, ?_⟩
  intro a b hab hgap
  have hmiss : ∀ A : Set ℝ, frontier A ⊆ frontier (locConst φ) ∪ frontier (locInc φ)
      ∪ frontier (locDec φ) ∪ frontier (badSet φ) →
      Set.Ioo a b ⊆ A ∨ Set.Ioo a b ∩ A = ∅ := by
    intro A hA
    apply full_or_empty_on_window
    intro y hy hyfr
    have hyF : y ∈ hFfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hA hyfr
    exact hgap y hyF hy
  have hmid : (a + b) / 2 ∈ Set.Ioo a b := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  rcases hmiss (locConst φ) (fun z hz =>
      Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hz))) with hfull | hemp1
  · exact Or.inl hfull
  rcases hmiss (locInc φ) (fun z hz =>
      Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hz))) with hfull | hemp2
  · exact Or.inr (Or.inl hfull)
  rcases hmiss (locDec φ) (fun z hz =>
      Set.mem_union_left _ (Set.mem_union_right _ hz)) with hfull | hemp3
  · exact Or.inr (Or.inr (Or.inl hfull))
  rcases hmiss (badSet φ) (fun z hz => Set.mem_union_right _ hz) with hfull | hemp4
  · exact Or.inr (Or.inr (Or.inr hfull))
  exfalso
  by_cases hmem : (a + b) / 2 ∈ locConst φ ∪ locInc φ ∪ locDec φ
  · rcases hmem with (h | h) | h
    · have hc' : (a + b) / 2 ∈ Set.Ioo a b ∩ locConst φ := ⟨hmid, h⟩
      rw [hemp1] at hc'
      exact hc'
    · have hc' : (a + b) / 2 ∈ Set.Ioo a b ∩ locInc φ := ⟨hmid, h⟩
      rw [hemp2] at hc'
      exact hc'
    · have hc' : (a + b) / 2 ∈ Set.Ioo a b ∩ locDec φ := ⟨hmid, h⟩
      rw [hemp3] at hc'
      exact hc'
  · have hc' : (a + b) / 2 ∈ Set.Ioo a b ∩ badSet φ := ⟨hmid, hmem⟩
    rw [hemp4] at hc'
    exact hc'

end Sundog.OMinimalAbstract
