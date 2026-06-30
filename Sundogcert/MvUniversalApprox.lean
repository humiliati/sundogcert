/-
# The multivariate cube capstone: every continuous f on [0,1]ⁿ is ReLU-approximable (Slate-4 U-1c/d)

Closes the multivariate cube lift. Two halves:

* **Bridge (U-1c).** A mathlib `MvPolynomial (Fin n) ℝ` becomes a `MvPolyEval` term list `toTerms q`,
  with `mvPolyVal (toTerms q) x = MvPolynomial.eval x q` (`toTerms_eval`) — so the U-1b evaluator
  computes any mathlib multivariate polynomial.
* **Capstone (U-1d).** Density of polynomial functions on the compact cube — via the **general
  Stone–Weierstrass** theorem applied to the range of `MvPolynomial.aeval (coordinate maps)`, which
  separates points — yields a concrete `MvPolynomial` `ε/2`-close to `f`; `mv_poly_polylog` gives a
  net `ε/2`-close to it; the triangle inequality finishes.

The single imported analytic input is Stone–Weierstrass (mathlib). The constructive half (polynomial
→ net) is the machine-checked U-1a/b.
-/
import Sundogcert.MvPolyEval
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.MvPolynomial

namespace Sundog.MvUniversalApprox

open Sundog.CircuitNet Sundog.MvMonomial Sundog.MvPolyEval

/-! ### Bridge: a mathlib `MvPolynomial` as a `MvPolyEval` term list -/

/-- `prodVal` distributes over list append. -/
theorem prodVal_append {n : ℕ} (L₁ L₂ : List (Fin n)) (x : Fin n → ℝ) :
    prodVal (L₁ ++ L₂) x = prodVal L₁ x * prodVal L₂ x := by
  induction L₁ with
  | nil => simp [prodVal]
  | cons i rest ih => simp only [List.cons_append, prodVal, ih]; ring

/-- `prodVal` of a replicated coordinate is the power. -/
theorem prodVal_replicate {n : ℕ} (k : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    prodVal (List.replicate k i) x = x i ^ k := by
  induction k with
  | zero => simp [prodVal]
  | succ k ih => rw [List.replicate_succ, prodVal, ih, pow_succ]; ring

/-- `prodVal` of a `flatMap` is the product of the per-element `prodVal`s. -/
theorem prodVal_flatMap {n : ℕ} (g : Fin n → List (Fin n)) (L : List (Fin n)) (x : Fin n → ℝ) :
    prodVal (L.flatMap g) x = (L.map (fun a => prodVal (g a) x)).prod := by
  induction L with
  | nil => simp [prodVal]
  | cons a rest ih =>
    rw [List.flatMap_cons, prodVal_append, ih, List.map_cons, List.prod_cons]

/-- The monomial `d : Fin n →₀ ℕ` as an index list: each coordinate `i` repeated `d i` times. -/
def monoList {n : ℕ} (d : Fin n →₀ ℕ) : List (Fin n) :=
  (List.finRange n).flatMap (fun i => List.replicate (d i) i)

/-- The list realizes the monomial value `∏ᵢ xᵢ^(dᵢ)`. -/
theorem monoList_prodVal {n : ℕ} (d : Fin n →₀ ℕ) (x : Fin n → ℝ) :
    prodVal (monoList d) x = ∏ i, x i ^ d i := by
  rw [monoList, prodVal_flatMap]
  simp only [prodVal_replicate]
  exact (Finset.prod_univ_def (fun i => x i ^ d i)).symm

/-- `mvPolyVal` as an explicit list sum. -/
theorem mvPolyVal_eq_sum {n : ℕ} (terms : List (ℝ × List (Fin n))) (x : Fin n → ℝ) :
    mvPolyVal terms x = (terms.map (fun t => t.1 * prodVal t.2 x)).sum := by
  induction terms with
  | nil => simp [mvPolyVal]
  | cons hd rest ih => obtain ⟨c, L⟩ := hd; simp only [mvPolyVal, List.map_cons, List.sum_cons, ih]

/-- The term list of a mathlib multivariate polynomial: `(coeff d, monomial-list d)` over the
support. -/
noncomputable def toTerms {n : ℕ} (q : MvPolynomial (Fin n) ℝ) : List (ℝ × List (Fin n)) :=
  q.support.toList.map (fun d => (q.coeff d, monoList d))

/-- **The bridge.** The U-1b evaluator on `toTerms q` is exactly `MvPolynomial.eval`. -/
theorem toTerms_eval {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    mvPolyVal (toTerms q) x = MvPolynomial.eval x q := by
  rw [mvPolyVal_eq_sum, toTerms, List.map_map]
  rw [MvPolynomial.eval_eq']
  rw [← Finset.sum_toList]
  apply congrArg
  apply List.map_congr_left
  intro d _
  simp only [Function.comp, monoList_prodVal]

end Sundog.MvUniversalApprox
