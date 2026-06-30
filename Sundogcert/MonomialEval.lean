/-
# Iterating the multiply gate: monomials x^d at the polynomial rate (S3-4, continuation)

`MultiplyGate` gives an ε-approximate two-input multiply gate at `O(log 1/ε)` depth. Chaining it
gives **monomials**: `x^d = x · x · … · x`, the next rung of arXiv:2606.26705 Cor 5.1.

Two honest subtleties, both handled:
* **Domain.** The multiply gate is valid on `[0,1]²`, but the running approximant can drift just
  outside `[0,1]`. So each step **clamps** the running value to `[0,1]` with a fixed 2-ReLU gadget
  `clamp01 t = max t 0 − max (t−1) 0` (the metric projection onto `[0,1]`). Clamping is a
  *contraction toward `[0,1]`* (`clamp01_contract`): since the true `x^k ∈ [0,1]`, it never
  increases the error, and it restores the gate's valid domain.
* **Error accumulation.** Each multiply adds at most `δ = 3/(4·4^m)`; with the contraction the
  errors add *linearly*: `|x^{k+1} − powTrop m k| ≤ k·δ` (`powTrop_approx`). So degree `d = k+1` at
  error `ε` needs `m = O(log(d/ε))` and depth `O(d · log(d/ε))` — the Cor 5.1 polynomial rate.

Honest boundary: this is the **monomial** `x^d`. A general polynomial via Horner (coefficients +
the `a_i + x·(…)` shape) and then a general target (partition of unity) are the staged
continuations, named `MONOMIAL_TO_POLY_INCOMPLETE`.
-/
import Sundogcert.MultiplyGate

namespace Sundog.MonomialEval

open Sundog.CircuitNet Sundog.RegionCount Sundog.SawtoothApprox Sundog.MultiplyGate

/-! ### The clamp gadget (metric projection onto [0,1]) -/

/-- `clamp01 t = max t 0 − max (t−1) 0` — the projection of `t` onto `[0,1]` (`0` below, `t` inside,
`1` above), as a difference of two ReLUs. -/
def clamp01 (t : ℝ) : ℝ := max t 0 - max (t - 1) 0

theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]; unfold clamp01
  rcases le_total 0 t with h0 | h0
  · rcases le_total 1 t with h1 | h1
    · rw [max_eq_left h0, max_eq_left (by linarith : (0 : ℝ) ≤ t - 1)]; constructor <;> linarith
    · rw [max_eq_left h0, max_eq_right (by linarith : t - 1 ≤ 0)]; constructor <;> linarith
  · rw [max_eq_right h0, max_eq_right (by linarith : t - 1 ≤ 0)]; constructor <;> linarith

/-- **Clamping is a contraction toward `[0,1]`.** For any target `y ∈ [0,1]`, clamping `t` can only
move it closer to `y`. -/
theorem clamp01_contract (t y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |clamp01 t - y| ≤ |t - y| := by
  have hsq : (clamp01 t - y) ^ 2 ≤ (t - y) ^ 2 := by
    unfold clamp01
    rcases le_total t 0 with h0 | h0
    · rcases le_total t 1 with h1 | h1
      · rw [max_eq_right h0, max_eq_right (by linarith : t - 1 ≤ 0)]; nlinarith
      · rw [max_eq_right h0, max_eq_right (by linarith : t - 1 ≤ 0)]; nlinarith
    · rcases le_total t 1 with h1 | h1
      · rw [max_eq_left h0, max_eq_right (by linarith : t - 1 ≤ 0)]; nlinarith
      · rw [max_eq_left h0, max_eq_left (by linarith : (0 : ℝ) ≤ t - 1)]; nlinarith
  calc |clamp01 t - y| = Real.sqrt ((clamp01 t - y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((t - y) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |t - y| := Real.sqrt_sq_eq_abs _

/-- The clamp as a 1-input tropical circuit: `max(x,0) + (−1)·max(x−1,0)`. -/
def clampGate : Trop 1 :=
  .add (.max (.var 0) (.const 0)) (.scale (-1) (.max (.add (.var 0) (.const (-1))) (.const 0)))

theorem clampGate_eval (w : Fin 1 → ℝ) : clampGate.eval w = clamp01 (w 0) := by
  simp only [clampGate, Trop.eval_add, Trop.eval_max, Trop.eval_scale, Trop.eval_var,
    Trop.eval_const, clamp01]
  ring_nf

/-- Clamp the running circuit `e` to `[0,1]` (graft the clamp gadget onto `e`). -/
def clampTrop (e : Trop 1) : Trop 1 := graft clampGate e

theorem clampTrop_eval (e : Trop 1) (w : Fin 1 → ℝ) :
    (clampTrop e).eval w = clamp01 (e.eval w) := by
  rw [clampTrop, graft_eval, clampGate_eval]

/-! ### Two-input substitution (compose a 2-input circuit with two 1-input expressions) -/

/-- Replace `var 0`/`var 1` of a 2-input circuit `e` with 1-input circuits `a`/`b`, giving the
1-input composite `x ↦ e(a x, b x)`. -/
def subst2 : Trop 2 → Trop 1 → Trop 1 → Trop 1
  | .var i, a, b => if i = 0 then a else b
  | .const c, _, _ => .const c
  | .add x y, a, b => .add (subst2 x a b) (subst2 y a b)
  | .scale c x, a, b => .scale c (subst2 x a b)
  | .max x y, a, b => .max (subst2 x a b) (subst2 y a b)

theorem subst2_eval (e : Trop 2) (a b : Trop 1) (w : Fin 1 → ℝ) :
    (subst2 e a b).eval w = e.eval ![a.eval w, b.eval w] := by
  induction e with
  | var i => fin_cases i <;> simp [subst2, Trop.eval_var]
  | const c => simp [subst2, Trop.eval_const]
  | add x y ihx ihy => simp [subst2, Trop.eval_add, ihx, ihy]
  | scale c x ih => simp [subst2, Trop.eval_scale, ih]
  | max x y ihx ihy => simp [subst2, Trop.eval_max, ihx, ihy]

theorem subst2_depth_le (e : Trop 2) (a b : Trop 1) :
    (subst2 e a b).depth ≤ e.depth + max a.depth b.depth := by
  have hMa : a.depth ≤ max a.depth b.depth := le_max_left _ _
  have hMb : b.depth ≤ max a.depth b.depth := le_max_right _ _
  generalize hM : max a.depth b.depth = M at *
  induction e with
  | var i =>
    simp only [subst2, Trop.depth]
    split_ifs <;> omega
  | const c => simp [subst2, Trop.depth]
  | add x y ihx ihy => simp only [subst2, Trop.depth, Nat.max_def]; split_ifs <;> omega
  | scale c x ih => simp only [subst2, Trop.depth]; omega
  | max x y ihx ihy => simp only [subst2, Trop.depth, Nat.max_def]; split_ifs <;> omega

/-! ### The monomial circuit -/

/-- `powTrop m k` computes `≈ x^(k+1)` (k multiplications): `powTrop m 0 = x`, and
`powTrop m (k+1) = mult(x, clamp(powTrop m k))`. -/
noncomputable def powTrop (m : ℕ) : ℕ → Trop 1
  | 0 => Trop.var 0
  | (k + 1) => subst2 (multTrop m) (Trop.var 0) (clampTrop (powTrop m k))

/-- **Monomial error bound.** On `[0,1]`, `powTrop m k` approximates `x^(k+1)` with error `≤ k·δ`,
`δ = 3/(4·4^m)` — the `k` multiply errors accumulate *linearly* (the clamp contraction keeps each
step's amplification at `≤ 1`). -/
theorem powTrop_approx (m k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ (k + 1) - (powTrop m k).eval (fun _ => x)| ≤ k * (3 / (4 * 4 ^ m)) := by
  induction k with
  | zero => simp [powTrop, Trop.eval_var]
  | succ k ih =>
    set Pk := (powTrop m k).eval (fun _ => x) with hPk
    have heval : (powTrop m (k + 1)).eval (fun _ => x)
        = (multTrop m).eval ![x, clamp01 Pk] := by
      simp only [powTrop, subst2_eval, clampTrop_eval, Trop.eval_var, hPk]
    have hxd : x ^ (k + 1) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨pow_nonneg hx.1 _, pow_le_one₀ hx.1 hx.2⟩
    have hcm := clamp01_mem Pk
    -- the multiply error
    have hmult : |x * clamp01 Pk - (multTrop m).eval ![x, clamp01 Pk]| ≤ 3 / (4 * 4 ^ m) := by
      have := mult_approx m ![x, clamp01 Pk] (by simpa using hx) (by simpa using hcm)
      simpa using this
    -- the exact step error, bounded by the previous error via the clamp contraction
    have hfirst : |x ^ (k + 1 + 1) - x * clamp01 Pk| ≤ k * (3 / (4 * 4 ^ m)) := by
      have hcontract : |x ^ (k + 1) - clamp01 Pk| ≤ |x ^ (k + 1) - Pk| := by
        rw [abs_sub_comm (x ^ (k + 1)) (clamp01 Pk), abs_sub_comm (x ^ (k + 1)) Pk]
        exact clamp01_contract Pk (x ^ (k + 1)) hxd.1 hxd.2
      have hpow : x ^ (k + 1 + 1) = x * x ^ (k + 1) := by ring
      calc |x ^ (k + 1 + 1) - x * clamp01 Pk|
            = |x| * |x ^ (k + 1) - clamp01 Pk| := by rw [hpow, ← mul_sub, abs_mul]
        _ ≤ 1 * |x ^ (k + 1) - clamp01 Pk| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [abs_of_nonneg hx.1]; exact hx.2
        _ = |x ^ (k + 1) - clamp01 Pk| := one_mul _
        _ ≤ |x ^ (k + 1) - Pk| := hcontract
        _ ≤ k * (3 / (4 * 4 ^ m)) := ih
    rw [heval]
    set E := (multTrop m).eval ![x, clamp01 Pk] with hE
    calc |x ^ (k + 1 + 1) - E|
          ≤ |x ^ (k + 1 + 1) - x * clamp01 Pk| + |x * clamp01 Pk - E| := abs_sub_le _ _ _
      _ ≤ k * (3 / (4 * 4 ^ m)) + 3 / (4 * 4 ^ m) := add_le_add hfirst hmult
      _ = (↑(k + 1)) * (3 / (4 * 4 ^ m)) := by push_cast; ring

/-- **Linear depth in the degree.** `powTrop m k` has depth `≤ k·((Rcirc m).depth + 12)` — each of
the `k` multiply+clamp steps adds `O(m)`. -/
theorem powTrop_depth (m k : ℕ) : (powTrop m k).depth ≤ k * ((Rcirc m).depth + 12) := by
  induction k with
  | zero => simp [powTrop, Trop.depth]
  | succ k ih =>
    -- one multiply+clamp step adds at most `(Rcirc m).depth + 12` (a linear, k-free bound)
    have hstep : (powTrop m (k + 1)).depth
        ≤ (powTrop m k).depth + ((Rcirc m).depth + 12) := by
      have hsub := subst2_depth_le (multTrop m) (Trop.var (0 : Fin 1)) (clampTrop (powTrop m k))
      have hgr := graft_depth_le clampGate (powTrop m k)
      have hcg : clampGate.depth = 4 := rfl
      have hmt := multTrop_depth m
      have hv : (Trop.var (0 : Fin 1)).depth = 0 := rfl
      simp only [powTrop, clampTrop, Nat.max_def] at hsub ⊢
      split_ifs at hsub <;> omega
    calc (powTrop m (k + 1)).depth
          ≤ (powTrop m k).depth + ((Rcirc m).depth + 12) := hstep
      _ ≤ k * ((Rcirc m).depth + 12) + ((Rcirc m).depth + 12) := Nat.add_le_add_right ih _
      _ = (k + 1) * ((Rcirc m).depth + 12) := by ring

/-! ### The ReLU net and the polynomial-rate statement -/

/-- The two-input-free ReLU net for `x^(k+1)`: the monomial circuit, compiled. -/
noncomputable def powNet (m k : ℕ) : Net 1 := compile (powTrop m k)

theorem powNet_approx (m k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ (k + 1) - realize1N (powNet m k) x| ≤ k * (3 / (4 * 4 ^ m)) := by
  have h : realize1N (powNet m k) x = (powTrop m k).eval (fun _ => x) := by
    rw [powNet, realize1_compile]; rfl
  rw [h]; exact powTrop_approx m k x hx

theorem powNet_depth (m k : ℕ) : (powNet m k).depth ≤ 4 * (k * ((Rcirc m).depth + 12)) := by
  calc (powNet m k).depth ≤ 4 * (powTrop m k).depth := compile_depth_le (powTrop m k)
    _ ≤ 4 * (k * ((Rcirc m).depth + 12)) := by have := powTrop_depth m k; omega

/-- **The polynomial rate for monomials.** For degree `d = k+1` and any `ε > 0`, an explicit ReLU
net computes `x^d` on `[0,1]` to error `≤ ε`, of depth `O(k · m)` where `k·(3/(4·4^m)) ≤ ε`. With
`m = O(log(d/ε))` this is depth `O(d · log(d/ε))` — arXiv:2606.26705 Cor 5.1's polynomial rate. -/
theorem pow_poly_rate (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Net 1),
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |x ^ (k + 1) - realize1N g x| ≤ ε) ∧
      g.depth ≤ 4 * (k * ((Rcirc m).depth + 12)) ∧
      (k : ℝ) * (3 / (4 * 4 ^ m)) ≤ ε := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 * k / ε) (by norm_num : (1 : ℝ) < 4)
  refine ⟨m, powNet m k, fun x hx => le_trans (powNet_approx m k x hx) ?_, powNet_depth m k, ?_⟩
  all_goals {
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [div_lt_iff₀ (by positivity)] at hm
    rw [show (k : ℝ) * (3 / (4 * 4 ^ m)) = 3 * k / (4 * 4 ^ m) by ring, div_le_iff₀ (by positivity)]
    nlinarith [hm, hε.le, hk]
  }

end Sundog.MonomialEval
