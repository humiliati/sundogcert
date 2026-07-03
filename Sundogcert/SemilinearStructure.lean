/-
# O-min lane R4-B4: the assembled instance — the semilinear o-minimal structure.

`semilinearStructure : OMinStructure` — **the first machine-checked nontrivial o-minimal
structure**: `Definable A := A has an n-variable semilinear presentation`. Classically this is
quantifier elimination for the ordered ℝ-vector space (divisible ordered abelian groups): the
booleans are B1, substitution (cylinders/permutations/diagonals) is B2, projection is B3's
Fourier–Motzkin, the atoms are one-cell presentations, and the o-minimality axiom lands through
the R3 dimension-one bridge (`slHolds₁_tame`).

With the instance, R4-A's abstract theorems become facts about a real structure, for free:
`semilinear_s1_eq_tame` (the dimension-one definables of the semilinear structure are exactly
the tame sets) and `semilinear_defFun_tame` (level sets of semilinear-definable functions are
tame). This discharges R4-A's non-vacuity fence and R3's "n-dim = named, not claimed" fence.

**Honest fence.** The canonical instance, not the last word: the "ReLU-`Net n` superlevel sets
are semilinear" bridge (which would make the ReLU structure itself an instance) remains the
named follow-on; the abstract Monotonicity Theorem and cell decomposition are R4-C/D.
-/
import Sundogcert.FourierMotzkinN
import Sundogcert.OMinimalStructure

namespace Sundog.SemilinearInstance

open Sundog.SemilinearN Sundog.FourierMotzkinN Sundog.OMinimalAbstract Sundog.OMinimalOne

variable {n : ℕ}

/-- Semilinear definability: the set has an `n`-variable presentation. -/
def SLDefinable (A : Set (Fin n → ℝ)) : Prop := ∃ S : SLN n, A = S.toSet

/-! ### Small evaluation and `toSet` helpers -/

theorem slHoldsN_nil (x : Fin n → ℝ) : ¬ slHoldsN ([] : SLN n) x := by
  rintro ⟨C, hC, -⟩
  exact absurd hC List.not_mem_nil

theorem slHoldsN_singleton (C : CellN n) (x : Fin n → ℝ) :
    slHoldsN [C] x ↔ cellHoldsN C x := by
  rw [slHoldsN_cons]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (slHoldsN_nil x)
  · exact Or.inl

theorem toSet_nil : SLN.toSet ([] : SLN n) = ∅ := by
  ext x
  simp only [SLN.toSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact slHoldsN_nil x

theorem toSet_compl (S : SLN n) : (slComplN S).toSet = S.toSetᶜ := by
  ext x
  simp only [SLN.toSet, Set.mem_setOf_eq, Set.mem_compl_iff]
  exact slComplN_holds S x

theorem toSet_union (S T : SLN n) : (slUnionN S T).toSet = S.toSet ∪ T.toSet := by
  ext x
  simp only [SLN.toSet, Set.mem_setOf_eq, Set.mem_union]
  exact slUnionN_holds S T x

/-! ### The dimension-one bridge to R3 -/

def atomToOne : AtomN 1 → Sundog.Semilinear.Atom₁
  | .gt a c => .gt (a 0) c
  | .eq a c => .eq (a 0) c

theorem atomToOne_holds (A : AtomN 1) (x : ℝ) :
    (atomToOne A).holds x ↔ A.holds (fun _ => x) := by
  cases A with
  | gt a c =>
    simp [atomToOne, Sundog.Semilinear.Atom₁.holds, AtomN.holds]
  | eq a c =>
    simp [atomToOne, Sundog.Semilinear.Atom₁.holds, AtomN.holds]

def cellToOne (C : CellN 1) : Sundog.Semilinear.Cell₁ := C.map atomToOne

theorem cellToOne_holds (C : CellN 1) (x : ℝ) :
    Sundog.Semilinear.cellHolds₁ (cellToOne C) x ↔ cellHoldsN C (fun _ => x) := by
  unfold cellToOne Sundog.Semilinear.cellHolds₁ cellHoldsN
  constructor
  · intro h A hA
    exact (atomToOne_holds A x).mp (h _ (List.mem_map_of_mem hA))
  · intro h A₁ hA₁
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hA₁
    exact (atomToOne_holds A x).mpr (h A hA)

def slToOne (S : SLN 1) : Sundog.Semilinear.SL₁ := S.map cellToOne

theorem slToOne_holds (S : SLN 1) (x : ℝ) :
    Sundog.Semilinear.slHolds₁ (slToOne S) x ↔ slHoldsN S (fun _ => x) := by
  unfold slToOne Sundog.Semilinear.slHolds₁ slHoldsN
  constructor
  · rintro ⟨C₁, hC₁, h⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC₁
    exact ⟨C, hC, (cellToOne_holds C x).mp h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨cellToOne C, List.mem_map_of_mem hC, (cellToOne_holds C x).mpr h⟩

/-- Dimension-one semilinear sets are tame (via the R3 landing). -/
theorem tame_dim_one_sl (S : SLN 1) : Tame {x : ℝ | slHoldsN S (fun _ => x)} := by
  have h : {x : ℝ | slHoldsN S (fun _ => x)}
      = {x | Sundog.Semilinear.slHolds₁ (slToOne S) x} := by
    ext x
    exact (slToOne_holds S x).symm
  rw [h]
  exact Sundog.Semilinear.slHolds₁_tame (slToOne S)

/-! ### The instance -/

/-- **The semilinear o-minimal structure** — the first machine-checked nontrivial instance of
`OMinStructure`. Booleans = B1, substitution = B2, projection = B3's Fourier–Motzkin, atoms =
one-cell presentations, o-minimality = the R3 dimension-one landing. -/
def semilinearStructure : OMinStructure where
  Definable := SLDefinable
  definable_empty := ⟨[], toSet_nil.symm⟩
  definable_compl := by
    intro n A h
    obtain ⟨S, rfl⟩ := h
    exact ⟨slComplN S, (toSet_compl S).symm⟩
  definable_union := by
    intro n A B hA hB
    obtain ⟨S, rfl⟩ := hA
    obtain ⟨T, rfl⟩ := hB
    exact ⟨slUnionN S T, (toSet_union S T).symm⟩
  definable_subst := by
    intro m n σ A h
    obtain ⟨S, rfl⟩ := h
    exact ⟨substSLN σ S, (substSLN_toSet σ S).symm⟩
  definable_proj := by
    intro n A h
    obtain ⟨S, rfl⟩ := h
    exact ⟨projSLN S, (projSLN_toSet S).symm⟩
  definable_lt := by
    refine ⟨[[.gt ![-1, 1] 0]], ?_⟩
    ext f
    simp only [SLN.toSet, Set.mem_setOf_eq, slHoldsN_singleton, cellHoldsN_singleton,
      AtomN.holds, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith
  definable_singleton := by
    intro r
    refine ⟨[[.eq ![1] (-r)]], ?_⟩
    ext f
    simp only [SLN.toSet, Set.mem_setOf_eq, slHoldsN_singleton, cellHoldsN_singleton,
      AtomN.holds, Fin.sum_univ_one, Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith
  tame_dim_one := by
    intro A h
    obtain ⟨S, rfl⟩ := h
    exact tame_dim_one_sl S

/-! ### The instantiated payoffs (R4-A's abstract theorems, now about a real structure) -/

/-- **Non-vacuity + the instantiated capstone**: the dimension-one definable sets of the
semilinear structure are exactly the tame sets. -/
theorem semilinear_s1_eq_tame (T : Set ℝ) :
    semilinearStructure.Definable (toOne T) ↔ Tame T :=
  s1_eq_tame semilinearStructure T

/-- Level sets of semilinear-definable functions are tame — R4-A's tameness payoff,
instantiated. -/
theorem semilinear_defFun_tame {φ : ℝ → ℝ}
    (hφ : semilinearStructure.DefinableFun φ) (r : ℝ) : Tame {x : ℝ | φ x = r} :=
  defFun_tame_level semilinearStructure hφ r

end Sundog.SemilinearInstance
