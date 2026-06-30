/-
# Multivariate polynomials as a ReLU net (Slate-4 U-1b)

The second rung of the cube lift. A multivariate polynomial is a finite sum of scaled monomials; in
the (representation-free) form `terms : List (ℝ × List (Fin n))` — each entry a coefficient and a
monomial index-list — the value is `Σ c · ∏ⱼ x_{iⱼ}` and the circuit is `Σ c · (prodTrop L)`. The
linear combination is exact (tropical scale+add); only the monomials are nonlinear, so the error is
just the sum of the per-monomial errors.

* **`mvPolyTrop_approx`** — `|mvPolyVal terms x − net| ≤ (Σ |c|·|L|)·δ` on `[0,1]ⁿ`.
* **`mv_poly_polylog`** — any such polynomial to `ε` by an explicit `Net n` (the polynomial rate).

Honest boundary: this is the multivariate analogue of `PolyEval`, in the lane's own coefficient-list
representation. Bridging mathlib's `MvPolynomial` and the cube's Stone–Weierstrass density is U-1c.
-/
import Sundogcert.MvMonomial

namespace Sundog.MvPolyEval

open Sundog.CircuitNet Sundog.MvMonomial

/-- The polynomial value `Σ c · ∏ⱼ x_{iⱼ}` over a coefficient/monomial-list term list. -/
def mvPolyVal {n : ℕ} : List (ℝ × List (Fin n)) → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | (c, L) :: rest, x => c * prodVal L x + mvPolyVal rest x

/-- The polynomial circuit `Σ c · prodTrop L` (exact scale+add over the monomial circuits). -/
noncomputable def mvPolyTrop {n : ℕ} (m : ℕ) : List (ℝ × List (Fin n)) → Trop n
  | [] => Trop.const 0
  | (c, L) :: rest => Trop.add (Trop.scale c (prodTrop m L)) (mvPolyTrop m rest)

/-- The error budget `Σ |c|·|L|`. -/
def errBoundMv {n : ℕ} : List (ℝ × List (Fin n)) → ℝ
  | [] => 0
  | (c, L) :: rest => |c| * L.length + errBoundMv rest

theorem errBoundMv_nonneg {n : ℕ} (terms : List (ℝ × List (Fin n))) : 0 ≤ errBoundMv terms := by
  induction terms with
  | nil => simp [errBoundMv]
  | cons hd rest ih =>
    obtain ⟨c, L⟩ := hd
    simp only [errBoundMv]
    exact add_nonneg (mul_nonneg (abs_nonneg c) (by positivity)) ih

/-- **Multivariate polynomial error bound.** On `[0,1]ⁿ`, the monomial-sum circuit approximates the
polynomial value with error `≤ (Σ |c|·|L|)·δ` — the per-monomial errors add. -/
theorem mvPolyTrop_approx {n : ℕ} (m : ℕ) (terms : List (ℝ × List (Fin n))) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    |mvPolyVal terms x - (mvPolyTrop m terms).eval x| ≤ errBoundMv terms * (3 / (4 * 4 ^ m)) := by
  induction terms with
  | nil => simp [mvPolyVal, mvPolyTrop, errBoundMv, Trop.eval_const]
  | cons hd rest ih =>
    obtain ⟨c, L⟩ := hd
    simp only [mvPolyVal, mvPolyTrop, errBoundMv, Trop.eval_add, Trop.eval_scale]
    have hmono := prodTrop_approx m L x hx
    set PT := (prodTrop m L).eval x with hPT
    set RT := (mvPolyTrop m rest).eval x with hRT
    have htri : |c * prodVal L x + mvPolyVal rest x - (c * PT + RT)|
        ≤ |c * prodVal L x - c * PT| + |mvPolyVal rest x - RT| := by
      have he : c * prodVal L x + mvPolyVal rest x - (c * PT + RT)
          = (c * prodVal L x - c * PT) + (mvPolyVal rest x - RT) := by ring
      rw [he]; exact abs_add_le _ _
    have hc : |c * prodVal L x - c * PT| ≤ |c| * ((L.length : ℝ) * (3 / (4 * 4 ^ m))) := by
      rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left hmono (abs_nonneg c)
    calc |c * prodVal L x + mvPolyVal rest x - (c * PT + RT)|
          ≤ |c * prodVal L x - c * PT| + |mvPolyVal rest x - RT| := htri
      _ ≤ |c| * ((L.length : ℝ) * (3 / (4 * 4 ^ m))) + errBoundMv rest * (3 / (4 * 4 ^ m)) :=
            add_le_add hc ih
      _ = (|c| * L.length + errBoundMv rest) * (3 / (4 * 4 ^ m)) := by ring

/-- The polynomial's ReLU net. -/
noncomputable def mvPolyNet {n : ℕ} (m : ℕ) (terms : List (ℝ × List (Fin n))) : Net n :=
  compile (mvPolyTrop m terms)

theorem mvPolyNet_approx {n : ℕ} (m : ℕ) (terms : List (ℝ × List (Fin n))) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    |mvPolyVal terms x - (mvPolyNet m terms).eval x| ≤ errBoundMv terms * (3 / (4 * 4 ^ m)) := by
  rw [mvPolyNet, compile_eval]
  exact mvPolyTrop_approx m terms x hx

/-- **The multivariate polynomial rate.** For any term list and `ε > 0`, an explicit `Net n`
computes the polynomial on `[0,1]ⁿ` to error `≤ ε`. -/
theorem mv_poly_polylog {n : ℕ} (terms : List (ℝ × List (Fin n))) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Net n),
      (∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
        |mvPolyVal terms x - g.eval x| ≤ ε) ∧
      errBoundMv terms * (3 / (4 * 4 ^ m)) ≤ ε := by
  have hB : 0 ≤ errBoundMv terms := errBoundMv_nonneg terms
  obtain ⟨m, hm⟩ :=
    pow_unbounded_of_one_lt (3 * (errBoundMv terms + 1) / (4 * ε)) (by norm_num : (1 : ℝ) < 4)
  have hδ : errBoundMv terms * (3 / (4 * 4 ^ m)) ≤ ε := by
    rw [div_lt_iff₀ (by positivity)] at hm
    rw [show errBoundMv terms * (3 / (4 * 4 ^ m))
        = 3 * errBoundMv terms / (4 * 4 ^ m) by ring, div_le_iff₀ (by positivity)]
    nlinarith [hm, hε.le, hB]
  exact ⟨m, mvPolyNet m terms, fun x hx => le_trans (mvPolyNet_approx m terms x hx) hδ, hδ⟩

end Sundog.MvPolyEval
