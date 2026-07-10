/-
# Dimension-one Mish tameness — the third non-monotone activation, two exp scales.

`mish(x) = x·tanh(softplus(x)) = x·tanh(ln(1 + eˣ))`. Non-monotone (min near `x ≈ −1.19`),
and the HARDEST activation of the series: `tanh∘softplus` carries TWO exponential scales
(`eˣ` and `e^{2x}`), so neither the GELU differentiate-to-polynomial route nor SiLU's
one-step transform closes it directly. But the Rolle ENGINE still works, applied deeper.

The rational form (`tanh(ln(1+eˣ)) = (e^{2x}+2eˣ)/(e^{2x}+2eˣ+2)`) turns the equation into

  `mish(x) = c  ⟺  G(x) := (x−c)e^{2x} + 2(x−c)eˣ − 2c = 0`.

`G' = eˣ·h₁` with `h₁ = (2x−2c+1)eˣ + 2(x−c+1)`, and `h₁'' = (2x−2c+5)eˣ` has zero set
`{c − 5/2}` (single point). So the Rolle counting lemma, applied down the chain
`{h₁''=0} → {h₁'=0} → {h₁=0} = {G'=0} → {G=0} = {mish=c}`, gives finite fibers — hence
`mish_dnf_tame`, unconditional. Three engine applications instead of SiLU's one: the
Rolle depth tracks the number of exponential scales.

*Pre-registered falsifiers*: `MISH_TWO_SCALES` (the two exp scales block the one-step
routes — confirmed, hence the deeper chain) and `MISH_ROLLE_BOTTOMS` (`h₁''` bottoms out at
a single point) — cleared.
-/
import Sundogcert.FiniteFiberRolle
import Sundogcert.FiniteFiberTame
import Sundogcert.SoftplusTame
import Sundogcert.TanhTame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Sundog.OMinimalMish

open Sundog.OMinimalOne Sundog.OMinimalFiber Sundog.OMinimalSigmoid
  Sundog.OMinimalSoftplus Sundog.OMinimalTanh

/-! ### Mish and its rational form -/

/-- The Mish activation `mish(x) = x·tanh(softplus(x))`. -/
noncomputable def mish (x : ℝ) : ℝ := x * Real.tanh (softplus x)

theorem mish_continuous : Continuous mish :=
  continuous_id.mul (tanh_continuous.comp softplus_continuous)

theorem tanh_softplus (x : ℝ) :
    Real.tanh (softplus x)
    = (Real.exp x * Real.exp x + 2 * Real.exp x)
      / (Real.exp x * Real.exp x + 2 * Real.exp x + 2) := by
  have hpos : (0 : ℝ) < 1 + Real.exp x := by positivity
  have hne : (1 : ℝ) + Real.exp x ≠ 0 := ne_of_gt hpos
  unfold softplus
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg,
    Real.exp_log hpos]
  field_simp
  ring

theorem mish_rational (x : ℝ) :
    mish x = x * (Real.exp x * Real.exp x + 2 * Real.exp x)
      / (Real.exp x * Real.exp x + 2 * Real.exp x + 2) := by
  unfold mish
  rw [tanh_softplus]
  ring

/-! ### The equation transform -/

/-- `G(x) = (x−c)e^{2x} + 2(x−c)eˣ − 2c` (with `e^{2x}` written `eˣ·eˣ`). -/
noncomputable def G (c x : ℝ) : ℝ :=
  (x - c) * (Real.exp x * Real.exp x) + 2 * ((x - c) * Real.exp x) - 2 * c

theorem mish_eq_iff (c x : ℝ) : mish x = c ↔ G c x = 0 := by
  have hden : (0 : ℝ) < Real.exp x * Real.exp x + 2 * Real.exp x + 2 := by positivity
  rw [mish_rational, div_eq_iff (ne_of_gt hden)]
  unfold G
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-! ### The derivative chain -/

/-- A linear function's derivative. -/
theorem hlin (a b x : ℝ) : HasDerivAt (fun y : ℝ => a * y + b) a x := by
  simpa using HasDerivAt.add_const b (HasDerivAt.const_mul a (hasDerivAt_id x))

/-- `G' = eˣ·h₁`. -/
noncomputable def G' (c x : ℝ) : ℝ :=
  Real.exp x * Real.exp x * (2 * x + (1 - 2 * c)) + 2 * Real.exp x * (x + (1 - c))

noncomputable def h1 (c x : ℝ) : ℝ :=
  Real.exp x * (2 * x + (1 - 2 * c)) + 2 * (x + (1 - c))
noncomputable def h1p (c x : ℝ) : ℝ := Real.exp x * (2 * x + (3 - 2 * c)) + 2
noncomputable def h1pp (c x : ℝ) : ℝ := Real.exp x * (2 * x + (5 - 2 * c))

theorem hG (c x : ℝ) : HasDerivAt (G c) (G' c x) x := by
  have hE := Real.hasDerivAt_exp x
  have hEE : HasDerivAt (fun y => Real.exp y * Real.exp y)
      (Real.exp x * Real.exp x + Real.exp x * Real.exp x) x := HasDerivAt.mul hE hE
  have hxc : HasDerivAt (fun y : ℝ => y - c) 1 x := HasDerivAt.sub_const c (hasDerivAt_id x)
  have hraw : HasDerivAt (G c)
      ((1 * (Real.exp x * Real.exp x)
          + (x - c) * (Real.exp x * Real.exp x + Real.exp x * Real.exp x))
        + 2 * (1 * Real.exp x + (x - c) * Real.exp x)) x :=
    HasDerivAt.sub_const (2 * c)
      (HasDerivAt.add (HasDerivAt.mul hxc hEE)
        (HasDerivAt.const_mul 2 (HasDerivAt.mul hxc hE)))
  have heq : (1 * (Real.exp x * Real.exp x)
        + (x - c) * (Real.exp x * Real.exp x + Real.exp x * Real.exp x))
      + 2 * (1 * Real.exp x + (x - c) * Real.exp x) = G' c x := by unfold G'; ring
  rwa [heq] at hraw

theorem hh1 (c x : ℝ) : HasDerivAt (h1 c) (h1p c x) x := by
  have hE := Real.hasDerivAt_exp x
  have hid : HasDerivAt (fun y : ℝ => y + (1 - c)) 1 x :=
    HasDerivAt.add_const (1 - c) (hasDerivAt_id x)
  have hraw : HasDerivAt (h1 c)
      ((Real.exp x * (2 * x + (1 - 2 * c)) + Real.exp x * 2) + 2 * 1) x :=
    HasDerivAt.add (HasDerivAt.mul hE (hlin 2 (1 - 2 * c) x))
      (HasDerivAt.const_mul 2 hid)
  have heq : (Real.exp x * (2 * x + (1 - 2 * c)) + Real.exp x * 2) + 2 * 1 = h1p c x := by
    unfold h1p; ring
  rwa [heq] at hraw

theorem hh1p (c x : ℝ) : HasDerivAt (h1p c) (h1pp c x) x := by
  have hE := Real.hasDerivAt_exp x
  have hraw : HasDerivAt (h1p c) (Real.exp x * (2 * x + (3 - 2 * c)) + Real.exp x * 2) x :=
    HasDerivAt.add_const 2 (HasDerivAt.mul hE (hlin 2 (3 - 2 * c) x))
  have heq : Real.exp x * (2 * x + (3 - 2 * c)) + Real.exp x * 2 = h1pp c x := by
    unfold h1pp; ring
  rwa [heq] at hraw

/-! ### The chain bottoms out at one point -/

theorem h1pp_zeros (c : ℝ) : {x : ℝ | h1pp c x = 0}.Finite := by
  apply Set.Finite.subset (Set.finite_singleton (c - 5 / 2))
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  unfold h1pp at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact absurd h (Real.exp_ne_zero x)
  · rw [Set.mem_singleton_iff]; linarith

theorem h1p_zeros (c : ℝ) : {x : ℝ | h1p c x = 0}.Finite :=
  finite_fiber_of_finite_deriv_zeros (hh1p c) (h1pp_zeros c) 0

theorem h1_zeros (c : ℝ) : {x : ℝ | h1 c x = 0}.Finite :=
  finite_fiber_of_finite_deriv_zeros (hh1 c) (h1p_zeros c) 0

theorem G'_zeros (c : ℝ) : {x : ℝ | G' c x = 0}.Finite := by
  have hset : {x : ℝ | G' c x = 0} = {x : ℝ | h1 c x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    have hfac : G' c x = Real.exp x * h1 c x := by unfold G' h1; ring
    rw [hfac]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (Real.exp_ne_zero x)
      · exact h'
    · intro h; rw [h, mul_zero]
  rw [hset]; exact h1_zeros c

/-! ### Fibers finite, and tameness -/

theorem mishFibersFinite (c : ℝ) : {x : ℝ | mish x = c}.Finite := by
  have hset : {x : ℝ | mish x = c} = {x : ℝ | G c x = 0} := by
    ext x; simp only [Set.mem_setOf_eq, mish_eq_iff]
  rw [hset]
  exact finite_fiber_of_finite_deriv_zeros (hG c) (G'_zeros c) 0

theorem mish_affine_fiber_finite {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    {x : ℝ | mish (a * x + b) = c}.Finite := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  have e : {x : ℝ | mish (a * x + b) = c} = (fun x => a * x + b) ⁻¹' {y | mish y = c} := rfl
  rw [e]
  exact (mishFibersFinite c).preimage haff.injOn

theorem mish_affine_continuous (a b : ℝ) : Continuous fun x => mish (a * x + b) :=
  mish_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem mish_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | mish (a * x + b) < r} :=
  tame_sublevel_of_finite (mish_affine_continuous a b) (mish_affine_fiber_finite ha b r)

theorem mish_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < mish (a * x + b)} :=
  tame_superlevel_of_finite (mish_affine_continuous a b) (mish_affine_fiber_finite ha b r)

theorem mish_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | mish (a * x + b) ≤ r} :=
  tame_le_of_finite (mish_affine_continuous a b) (mish_affine_fiber_finite ha b r)

theorem mish_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ mish (a * x + b)} :=
  tame_ge_of_finite (mish_affine_continuous a b) (mish_affine_fiber_finite ha b r)

theorem mish_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | mish (a * x + b) = r} :=
  tame_level_of_finite (mish_affine_fiber_finite ha b r)

/-- A two-sided Mish band is tame. -/
theorem mish_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < mish (a * x + b) ∧ mish (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (mish_gt_tame ha b r₁) (mish_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable Mish bands is tame. -/
theorem mish_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < mish (s.1 * x + s.2.1) ∧
          mish (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact mish_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalMish
