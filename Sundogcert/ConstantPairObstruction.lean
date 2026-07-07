/-
# The constant-pair obstruction: E3-emptiness as a theorem (casino C-03 follow-up)

SUNDOG_V_CASINO Run 2, C-03 day-2 named follow-up (`internal/casino/artifacts/C-03/
E3_EMPTINESS_THEOREM.md` in the sundog repo). The day-2 enumeration found the E3
ensemble — XOR-free monomial products f = m₁·m₂ — has ZERO measurable draws against
the registered quadratic-mixing shadow (0/30,625). This module proves that emptiness,
in full generality: every n, every wiring, every monomial degree.

## What is PROVED here

* `measurableVia_const_pair` — the obstruction: if a shadow co-fibers the two constant
  inputs (`Φ 0 = Φ 1`), every Φ-measurable readout agrees at them. The measurable
  algebra of such a shadow lies in the hyperplane {f | f 0̄ = f 1̄}.
* `quadMix_zero_eq_one` — every quadratic-mixing shadow (components
  `x (a j) + ∏ i ∈ T j, x i`, mixing monomials nonempty) co-fibers the constants:
  both map to 0̄. Degenerate wirings included (a repeated index just squares away).
* `mono_not_measurableVia` / `quadMix_mono_not_measurable` — no nonempty XOR-free
  monomial `∏ i ∈ S, x i` is measurable for any such shadow: the monomial separates
  the co-fibered constants (0 at 0̄, 1 at 1̄).
* `mono_mul` — products of monomials are monomials (`mono S · mono T = mono (S ∪ T)`,
  by idempotence in `ZMod 2`), so the E3 draw shape m₁·m₂ is covered verbatim:
  `quadMix_e3_draw_not_measurable`.

## FENCE (what this does NOT say)

The obstruction is a TWO-POINT invariant, not an algebra-match statement. It explains
all of E3's emptiness but none of E2's structure: E2 forms `x a + x b · x c` vanish at
BOTH constants, pass the obstruction, and do inhabit the fourth corner (the day-2
witnesses). The match-conditional fence on C-03 rests on the E2-internal census
(0 accidental inhabitants), which this module neither proves nor touches. The honest
reading is recorded in the memo: E3 was a weak contrast control; the sharp control
(E4, products of two-variable parities) is registered there and not yet run.
-/
import Mathlib

namespace Sundog.ConstantPairObstruction

variable {n m : ℕ}

/-- `f` is measurable for the shadow `Φ`: constant on every `Φ`-fiber. -/
def MeasurableVia (Φ : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (f : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ x y, Φ x = Φ y → f x = f y

/-- **The constant-pair obstruction.** If the shadow co-fibers the two constant inputs,
every measurable readout agrees at them: the measurable algebra lies in the hyperplane
`{f | f 0̄ = f 1̄}`. -/
theorem measurableVia_const_pair {Φ : (Fin n → ZMod 2) → (Fin m → ZMod 2)}
    (h : Φ 0 = Φ 1) {f : (Fin n → ZMod 2) → ZMod 2} (hf : MeasurableVia Φ f) :
    f 0 = f 1 :=
  hf 0 1 h

/-- The XOR-free monomial `∏ i ∈ S, x i` (an E3 factor; over `ZMod 2`, AND = ·). -/
def mono (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ZMod 2 := ∏ i ∈ S, x i

@[simp] theorem mono_zero {S : Finset (Fin n)} (hS : S.Nonempty) :
    mono S (0 : Fin n → ZMod 2) = 0 := by
  obtain ⟨i, hi⟩ := hS
  exact Finset.prod_eq_zero hi (Pi.zero_apply i)

@[simp] theorem mono_one (S : Finset (Fin n)) :
    mono S (1 : Fin n → ZMod 2) = 1 := by
  simp [mono]

/-- Squares are idempotent in `ZMod 2`, so a monomial squared is itself. -/
theorem mono_sq (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    mono S x * mono S x = mono S x := by
  have h2 : ∀ a : ZMod 2, a * a = a := by decide
  simp only [mono, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => h2 (x i)

/-- Absorption: a monomial over a subset is absorbed by the larger monomial. -/
theorem mono_mul_of_subset {S B : Finset (Fin n)} (hB : B ⊆ S) (x : Fin n → ZMod 2) :
    mono S x * mono B x = mono S x := by
  have hsplit : mono (S \ B) x * mono B x = mono S x := Finset.prod_sdiff hB
  calc mono S x * mono B x
      = mono (S \ B) x * (mono B x * mono B x) := by rw [← hsplit]; ring
    _ = mono (S \ B) x * mono B x := by rw [mono_sq]
    _ = mono S x := hsplit

/-- **Products of monomials are monomials** — the E3 draw shape `m₁ · m₂` is the
monomial on the union of supports. -/
theorem mono_mul (S T : Finset (Fin n)) (x : Fin n → ZMod 2) :
    mono S x * mono T x = mono (S ∪ T) x := by
  have h := Finset.prod_union_inter (s₁ := S) (s₂ := T) (f := x)
  calc mono S x * mono T x
      = mono (S ∪ T) x * mono (S ∩ T) x := h.symm
    _ = mono (S ∪ T) x :=
        mono_mul_of_subset (Finset.inter_subset_left.trans Finset.subset_union_left) x

/-- **No nonempty XOR-free monomial is measurable for a constant-pair-degenerate
shadow**: the monomial separates the co-fibered constants. -/
theorem mono_not_measurableVia {Φ : (Fin n → ZMod 2) → (Fin m → ZMod 2)}
    (h : Φ 0 = Φ 1) {S : Finset (Fin n)} (hS : S.Nonempty) :
    ¬ MeasurableVia Φ (mono S) := by
  intro hf
  have := measurableVia_const_pair h hf
  rw [mono_zero hS, mono_one] at this
  exact zero_ne_one this

/-! ## The quadratic-mixing shadow class (the registered day-2 family) -/

/-- The quadratic-mixing shadow: component `j` reads `x (a j) + ∏ i ∈ T j, x i`
(head coordinate XOR a mixing monomial). The registered day-2 instance is
`n = 10`, `m = 6`, `a = id`, `T j` a pair; the class allows any wiring, any
nonempty mixing monomials — degenerate repeated indices included. -/
def quadMix (a : Fin m → Fin n) (T : Fin m → Finset (Fin n))
    (x : Fin n → ZMod 2) : Fin m → ZMod 2 :=
  fun j => x (a j) + mono (T j) x

/-- **Every quadratic-mixing shadow co-fibers the constants** (both map to `0̄`):
at `0̄` each component is `0 + 0`; at `1̄` it is `1 + 1 = 0` in `ZMod 2`. -/
theorem quadMix_zero_eq_one {a : Fin m → Fin n} {T : Fin m → Finset (Fin n)}
    (hT : ∀ j, (T j).Nonempty) :
    quadMix a T 0 = quadMix a T 1 := by
  funext j
  simp only [quadMix, mono_zero (hT j), mono_one, Pi.zero_apply, Pi.one_apply]
  decide

/-- **E3-emptiness, monomial form (the theorem).** No nonempty XOR-free monomial is
measurable for any quadratic-mixing shadow — every `n`, every wiring, every degree.
The day-2 enumeration's 0/30,625 is the `n = 10`, registered-wiring, degree ≤ 6
shadow of this statement. -/
theorem quadMix_mono_not_measurable {a : Fin m → Fin n} {T : Fin m → Finset (Fin n)}
    (hT : ∀ j, (T j).Nonempty) {S : Finset (Fin n)} (hS : S.Nonempty) :
    ¬ MeasurableVia (quadMix a T) (mono S) :=
  mono_not_measurableVia (quadMix_zero_eq_one hT) hS

/-- **E3-emptiness, draw form.** The E3 ensemble draws `f = m₁ · m₂` (products of two
nonempty XOR-free monomials); no draw is measurable for any quadratic-mixing shadow. -/
theorem quadMix_e3_draw_not_measurable {a : Fin m → Fin n} {T : Fin m → Finset (Fin n)}
    (hT : ∀ j, (T j).Nonempty) {S₁ S₂ : Finset (Fin n)} (hS₁ : S₁.Nonempty) :
    ¬ MeasurableVia (quadMix a T) (fun x => mono S₁ x * mono S₂ x) := by
  have hfun : (fun x => mono S₁ x * mono S₂ x) = mono (S₁ ∪ S₂) := by
    funext x; exact mono_mul S₁ S₂ x
  rw [hfun]
  exact quadMix_mono_not_measurable hT (hS₁.mono Finset.subset_union_left)

/-! ## The registered day-2 instance (n = 10, seed-1 wiring) -/

/-- The exact day-2 shadow: heads `x_0 … x_5`, mixing pairs
`(4,5), (7,9), (0,1), (8,9), (2,3), (8,4)` (numpy `default_rng(1)` wiring, verified
in `e3_emptiness_check.py`). -/
def dayTwoShadow : (Fin 10 → ZMod 2) → (Fin 6 → ZMod 2) :=
  quadMix (fun j => ⟨j.val, by omega⟩)
    ![{4, 5}, {7, 9}, {0, 1}, {8, 9}, {2, 3}, {8, 4}]

/-- The artifact's instance, pinned: no nonempty monomial is `dayTwoShadow`-measurable.
This subsumes all 30,625 E3 draws of the day-2 run (and all 1023 monomial supports
checked directly by `e3_emptiness_check.py`). -/
theorem dayTwoShadow_mono_not_measurable {S : Finset (Fin 10)} (hS : S.Nonempty) :
    ¬ MeasurableVia dayTwoShadow (mono S) :=
  quadMix_mono_not_measurable (by decide) hS

end Sundog.ConstantPairObstruction
