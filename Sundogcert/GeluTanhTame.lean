/-
# Dimension-one GELU-tanh (the tanh approximation) tameness.

`gelu_tanh(x) = ½·x·(1 + tanh(c·(x + a·x³)))`, `c = √(2/π)`, `a = 0.044715` — the widely
used tanh approximation of GELU. Non-monotone (Rolle route). The cubic inside `tanh` is
the new structure, but it works FOR us: via `1 + tanh(v) = 2/(1 + e^{−2v})`, this is
`x·σ(w)` with `w = 2c(x + a x³)`, so the SiLU-style equation transform gives

  `gelu_tanh(x) = C  ⟺  (x − C)·e^{w(x)} = C`,

and `g_C(x) = (x − C)e^{w}` has `g_C' = e^{w}·(1 + (x − C)·w')` where
`1 + (x − C)·w'` is a **cubic polynomial** in `x` (`w' = 2c(1 + 3a x²)`). A nonzero cubic
has ≤ 3 roots, so `{g_C' = 0}` is finite — ONE Rolle step gives `{gelu_tanh = C}` finite,
hence `gelu_tanh_dnf_tame`, unconditional. The cubic-in-the-exponent turns the critical
equation polynomial: a third way to feed the Rolle engine.

*Pre-registered falsifier* `GELU_TANH_CUBIC_CRITICAL` (the transformed critical equation is
a cubic polynomial, finite roots) — cleared.
-/
import Sundogcert.FiniteFiberRolle
import Sundogcert.FiniteFiberTame
import Sundogcert.TanhTame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace Sundog.OMinimalGeluTanh

open Sundog.OMinimalOne Sundog.OMinimalFiber Sundog.OMinimalSigmoid Sundog.OMinimalTanh

/-! ### Constants -/

noncomputable def gtc : ℝ := Real.sqrt (2 / Real.pi)
def gta : ℝ := 0.044715

theorem gtc_pos : 0 < gtc := Real.sqrt_pos.mpr (by positivity)
theorem gta_pos : 0 < gta := by unfold gta; norm_num

/-! ### GELU-tanh and its scaled cubic argument -/

/-- `w(x) = 2c(x + a x³)`. -/
noncomputable def w (x : ℝ) : ℝ := 2 * gtc * (x + gta * x ^ 3)
/-- `w'(x) = 2c(1 + 3a x²)`. -/
noncomputable def wd (x : ℝ) : ℝ := 2 * gtc * (1 + 3 * gta * x ^ 2)

/-- The tanh approximation `gelu_tanh(x) = ½·x·(1 + tanh(c(x + a x³)))`. -/
noncomputable def gelu_tanh (x : ℝ) : ℝ :=
  1 / 2 * x * (1 + Real.tanh (gtc * (x + gta * x ^ 3)))

theorem gelu_tanh_continuous : Continuous gelu_tanh := by
  unfold gelu_tanh
  exact (continuous_const.mul continuous_id).mul
    (continuous_const.add (tanh_continuous.comp
      (continuous_const.mul (continuous_id.add (continuous_const.mul (continuous_pow 3))))))

/-! ### `1 + tanh` as an exponential -/

theorem tanh_add_one (v : ℝ) : 1 + Real.tanh v = 2 / (1 + Real.exp (-(2 * v))) := by
  have hev : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have h1 : (0 : ℝ) < Real.exp v + Real.exp (-v) := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq,
    show -(2 * v) = -v + -v by ring, Real.exp_add]
  field_simp
  nlinarith [hev, Real.exp_pos v, Real.exp_pos (-v)]

/-! ### The equation transform -/

theorem gelu_tanh_rational (x : ℝ) : gelu_tanh x = x / (1 + Real.exp (-(w x))) := by
  have hd : (0 : ℝ) < 1 + Real.exp (-(w x)) := by positivity
  unfold gelu_tanh
  rw [tanh_add_one, show 2 * (gtc * (x + gta * x ^ 3)) = w x by unfold w; ring]
  field_simp

theorem gelu_tanh_eq_iff (C : ℝ) (x : ℝ) :
    gelu_tanh x = C ↔ (x - C) * Real.exp (w x) = C := by
  have hexp : (0 : ℝ) < Real.exp (w x) := Real.exp_pos _
  have hd : (1 : ℝ) + Real.exp (-(w x)) ≠ 0 := by positivity
  rw [gelu_tanh_rational, div_eq_iff hd]
  have hnw : Real.exp (-(w x)) = (Real.exp (w x))⁻¹ := Real.exp_neg _
  rw [hnw]
  constructor
  · intro h
    have : x = C + C * (Real.exp (w x))⁻¹ := by linear_combination h
    field_simp at this ⊢
    linear_combination this
  · intro h
    field_simp at h ⊢
    linear_combination h

/-! ### The transformed function and its cubic critical equation -/

/-- `g_C(x) = (x − C)·e^{w(x)}`. -/
noncomputable def g (C x : ℝ) : ℝ := (x - C) * Real.exp (w x)
/-- `g_C'(x) = e^{w}·(1 + (x − C)·w')`. -/
noncomputable def gd (C x : ℝ) : ℝ := Real.exp (w x) * (1 + (x - C) * wd x)

theorem hw (x : ℝ) : HasDerivAt w (wd x) x := by
  have hraw : HasDerivAt w
      (2 * gtc * (1 + gta * ((3 : ℕ) * x ^ (3 - 1) * 1))) x :=
    HasDerivAt.const_mul (2 * gtc)
      (HasDerivAt.add (hasDerivAt_id x)
        (HasDerivAt.const_mul gta (HasDerivAt.pow (hasDerivAt_id x) 3)))
  have heq : 2 * gtc * (1 + gta * ((3 : ℕ) * x ^ (3 - 1) * 1)) = wd x := by
    unfold wd; push_cast; ring
  rwa [heq] at hraw

theorem hg (C x : ℝ) : HasDerivAt (g C) (gd C x) x := by
  have hexpw : HasDerivAt (fun y => Real.exp (w y)) (Real.exp (w x) * wd x) x :=
    HasDerivAt.comp x (Real.hasDerivAt_exp (w x)) (hw x)
  have hxc : HasDerivAt (fun y : ℝ => y - C) 1 x := HasDerivAt.sub_const C (hasDerivAt_id x)
  have hraw : HasDerivAt (g C)
      (1 * Real.exp (w x) + (x - C) * (Real.exp (w x) * wd x)) x :=
    HasDerivAt.mul hxc hexpw
  have heq : 1 * Real.exp (w x) + (x - C) * (Real.exp (w x) * wd x) = gd C x := by
    unfold gd; ring
  rwa [heq] at hraw

/-- The critical equation `1 + (x − C)·w' = 0` is a cubic — finitely many roots. -/
theorem cubic_zeros (d : ℝ) : {x : ℝ | 1 + (x - d) * wd x = 0}.Finite := by
  have hgc : 0 < gtc := gtc_pos
  have hga : 0 < gta := gta_pos
  set k3 := 6 * gtc * gta with hk3
  set k2 := -(6 * gtc * gta * d) with hk2
  set k1 := 2 * gtc with hk1
  set k0 := 1 - 2 * gtc * d with hk0
  set P : Polynomial ℝ :=
    Polynomial.C k3 * Polynomial.X ^ 3 + Polynomial.C k2 * Polynomial.X ^ 2
      + Polynomial.C k1 * Polynomial.X + Polynomial.C k0 with hP
  have hcoeff : P.coeff 3 = k3 := by
    simp [hP, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hPne : P ≠ 0 := by
    intro h; rw [h, Polynomial.coeff_zero] at hcoeff
    exact (ne_of_gt (show (0 : ℝ) < k3 by rw [hk3]; positivity)) hcoeff.symm
  have heval : ∀ x : ℝ, 1 + (x - d) * wd x = P.eval x := by
    intro x; unfold wd; rw [hP]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, hk3, hk2, hk1, hk0]
    ring
  have hset : {x : ℝ | 1 + (x - d) * wd x = 0} = {x | P.eval x = 0} := by
    ext x; simp only [Set.mem_setOf_eq, heval x]
  rw [hset]; exact P.finite_setOf_isRoot hPne

theorem gd_zeros (C : ℝ) : {x : ℝ | gd C x = 0}.Finite := by
  have hset : {x : ℝ | gd C x = 0} = {x : ℝ | 1 + (x - C) * wd x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    unfold gd
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (Real.exp_ne_zero _)
      · exact h'
    · intro h; rw [h, mul_zero]
  rw [hset]; exact cubic_zeros C

/-! ### Fibers finite -/

theorem geluTanhFibersFinite (C : ℝ) : {x : ℝ | gelu_tanh x = C}.Finite := by
  have hset : {x : ℝ | gelu_tanh x = C} = {x : ℝ | g C x = C} := by
    ext x; simp only [Set.mem_setOf_eq, gelu_tanh_eq_iff]; rfl
  rw [hset]
  exact finite_fiber_of_finite_deriv_zeros (fun x => hg C x) (gd_zeros C) C

theorem gelu_tanh_affine_fiber_finite {a : ℝ} (ha : a ≠ 0) (b C : ℝ) :
    {x : ℝ | gelu_tanh (a * x + b) = C}.Finite := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  have e : {x : ℝ | gelu_tanh (a * x + b) = C}
      = (fun x => a * x + b) ⁻¹' {y | gelu_tanh y = C} := rfl
  rw [e]
  exact (geluTanhFibersFinite C).preimage haff.injOn

/-! ### The dimension-one GELU-tanh class is tame -/

theorem gelu_tanh_affine_continuous (a b : ℝ) :
    Continuous fun x => gelu_tanh (a * x + b) :=
  gelu_tanh_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem gelu_tanh_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu_tanh (a * x + b) < r} :=
  tame_sublevel_of_finite (gelu_tanh_affine_continuous a b)
    (gelu_tanh_affine_fiber_finite ha b r)

theorem gelu_tanh_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < gelu_tanh (a * x + b)} :=
  tame_superlevel_of_finite (gelu_tanh_affine_continuous a b)
    (gelu_tanh_affine_fiber_finite ha b r)

theorem gelu_tanh_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu_tanh (a * x + b) ≤ r} :=
  tame_le_of_finite (gelu_tanh_affine_continuous a b)
    (gelu_tanh_affine_fiber_finite ha b r)

theorem gelu_tanh_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ gelu_tanh (a * x + b)} :=
  tame_ge_of_finite (gelu_tanh_affine_continuous a b)
    (gelu_tanh_affine_fiber_finite ha b r)

theorem gelu_tanh_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | gelu_tanh (a * x + b) = r} :=
  tame_level_of_finite (gelu_tanh_affine_fiber_finite ha b r)

/-- A two-sided GELU-tanh band is tame. -/
theorem gelu_tanh_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < gelu_tanh (a * x + b) ∧ gelu_tanh (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (gelu_tanh_gt_tame ha b r₁) (gelu_tanh_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable GELU-tanh bands is tame. -/
theorem gelu_tanh_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ)) (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < gelu_tanh (s.1 * x + s.2.1) ∧
          gelu_tanh (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact gelu_tanh_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalGeluTanh
