/-
# Multivariate monomials: products of coordinates as a ReLU net (Slate-4 U-1a)

The first rung of the multivariate cube lift. A multivariate monomial `∏ⱼ x_{iⱼ}` over `[0,1]ⁿ` is a
*product of input coordinates* (with repetition), so it is a clamped multiply-chain reading the
inputs — exactly `MonomialEval`'s construction, but multiplying a fresh coordinate `x_i` at each
step instead of the same `x`.

* **`prodTrop m L`** — the circuit for the product over the index list `L : List (Fin n)`: `prodTrop
  m [] = 1`, `prodTrop m (i :: rest) = mult(x_i, clamp(prodTrop m rest))`.
* **`prodTrop_approx`** — `|∏ⱼ x_{iⱼ} − prodTrop m L| ≤ |L|·δ` on `[0,1]ⁿ`, `δ = 3/(4·4^m)`: the
  multiply errors accumulate linearly, the clamp keeps each running product in `[0,1]`.

New machinery: `subst2N` (the `2 → n` substitution, generalizing `MonomialEval.subst2`). Reuses the
multiply gate (`MultiplyGate.multTrop`/`mult_approx`/`graft`) and the clamp
(`MonomialEval.clamp01`).
-/
import Sundogcert.MonomialEval

namespace Sundog.MvMonomial

open Sundog.CircuitNet Sundog.MultiplyGate Sundog.MonomialEval

/-! ### Two-input substitution into an `n`-input circuit -/

/-- Replace `var 0`/`var 1` of a 2-input circuit with `n`-input circuits `a`/`b`. -/
def subst2N {n : ℕ} : Trop 2 → Trop n → Trop n → Trop n
  | .var i, a, b => if i = 0 then a else b
  | .const c, _, _ => .const c
  | .add x y, a, b => .add (subst2N x a b) (subst2N y a b)
  | .scale c x, a, b => .scale c (subst2N x a b)
  | .max x y, a, b => .max (subst2N x a b) (subst2N y a b)

theorem subst2N_eval {n : ℕ} (e : Trop 2) (a b : Trop n) (x : Fin n → ℝ) :
    (subst2N e a b).eval x = e.eval ![a.eval x, b.eval x] := by
  induction e with
  | var i => fin_cases i <;> simp [subst2N, Trop.eval_var]
  | const c => simp [subst2N, Trop.eval_const]
  | add p q ihp ihq => simp [subst2N, Trop.eval_add, ihp, ihq]
  | scale c p ih => simp [subst2N, Trop.eval_scale, ih]
  | max p q ihp ihq => simp [subst2N, Trop.eval_max, ihp, ihq]

/-! ### The product value and circuit -/

/-- The value `∏ⱼ x_{iⱼ}` of the index list `L`. -/
def prodVal {n : ℕ} : List (Fin n) → (Fin n → ℝ) → ℝ
  | [], _ => 1
  | i :: rest, x => x i * prodVal rest x

/-- The product stays in `[0,1]` when every coordinate does. -/
theorem prodVal_mem {n : ℕ} (L : List (Fin n)) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : prodVal L x ∈ Set.Icc (0 : ℝ) 1 := by
  induction L with
  | nil => simp [prodVal]
  | cons i rest ih =>
    rw [Set.mem_Icc] at ih ⊢
    obtain ⟨h0, h1⟩ := ih
    obtain ⟨hi0, hi1⟩ := hx i
    simp only [prodVal]
    refine ⟨mul_nonneg hi0 h0, ?_⟩
    calc x i * prodVal rest x ≤ 1 * 1 := mul_le_mul hi1 h1 h0 (by norm_num)
      _ = 1 := by ring

/-- The product circuit: a clamped multiply-chain over the coordinate list. -/
noncomputable def prodTrop {n : ℕ} (m : ℕ) : List (Fin n) → Trop n
  | [] => Trop.const 1
  | i :: rest => subst2N (multTrop m) (Trop.var i) (graft clampGate (prodTrop m rest))

/-- **Multivariate monomial error bound.** On `[0,1]ⁿ`, `prodTrop m L` approximates `∏ⱼ x_{iⱼ}`
with error `≤ |L|·(3/(4·4^m))` — the `|L|` multiplies accumulate linearly, the clamp caps each
step's amplification at `≤ 1`. -/
theorem prodTrop_approx {n : ℕ} (m : ℕ) (L : List (Fin n)) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    |prodVal L x - (prodTrop m L).eval x| ≤ L.length * (3 / (4 * 4 ^ m)) := by
  induction L with
  | nil => simp [prodVal, prodTrop, Trop.eval_const]
  | cons i rest ih =>
    set Pr := (prodTrop m rest).eval x with hPr
    have heval : (prodTrop m (i :: rest)).eval x
        = (multTrop m).eval ![x i, clamp01 Pr] := by
      simp only [prodTrop, subst2N_eval, graft_eval, clampGate_eval, Trop.eval_var, hPr]
    have hcm := clamp01_mem Pr
    have hrest_mem := prodVal_mem rest x hx
    have hmult : |x i * clamp01 Pr - (multTrop m).eval ![x i, clamp01 Pr]| ≤ 3 / (4 * 4 ^ m) := by
      have := mult_approx m ![x i, clamp01 Pr] (by simpa using hx i) (by simpa using hcm)
      simpa using this
    have hfirst : |x i * prodVal rest x - x i * clamp01 Pr| ≤ rest.length * (3 / (4 * 4 ^ m)) := by
      have hcontract : |prodVal rest x - clamp01 Pr| ≤ |prodVal rest x - Pr| := by
        rw [abs_sub_comm (prodVal rest x) (clamp01 Pr), abs_sub_comm (prodVal rest x) Pr]
        exact clamp01_contract Pr (prodVal rest x) hrest_mem.1 hrest_mem.2
      calc |x i * prodVal rest x - x i * clamp01 Pr|
            = |x i| * |prodVal rest x - clamp01 Pr| := by rw [← mul_sub, abs_mul]
        _ ≤ 1 * |prodVal rest x - clamp01 Pr| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              rw [abs_of_nonneg (hx i).1]; exact (hx i).2
        _ = |prodVal rest x - clamp01 Pr| := one_mul _
        _ ≤ |prodVal rest x - Pr| := hcontract
        _ ≤ rest.length * (3 / (4 * 4 ^ m)) := ih
    rw [heval]
    calc |prodVal (i :: rest) x - (multTrop m).eval ![x i, clamp01 Pr]|
          ≤ |x i * prodVal rest x - x i * clamp01 Pr|
            + |x i * clamp01 Pr - (multTrop m).eval ![x i, clamp01 Pr]| := by
            rw [show prodVal (i :: rest) x = x i * prodVal rest x from rfl]
            exact abs_sub_le _ _ _
      _ ≤ rest.length * (3 / (4 * 4 ^ m)) + 3 / (4 * 4 ^ m) := add_le_add hfirst hmult
      _ = (↑(i :: rest).length) * (3 / (4 * 4 ^ m)) := by
            simp only [List.length_cons]; push_cast; ring

end Sundog.MvMonomial
