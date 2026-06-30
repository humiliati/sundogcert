/-
# The multivariate cube capstone: every continuous f on [0,1]ⁿ is ReLU-approximable (Slate-4 U-1c/d)

Closes the multivariate cube lift. Two halves:

* **Bridge (U-1c).** A mathlib `MvPolynomial (Fin n) ℝ` becomes a `MvPolyEval` term list
  `toTerms q`, with `mvPolyVal (toTerms q) x = MvPolynomial.eval x q` (`toTerms_eval`) — so the
  U-1b evaluator computes any mathlib multivariate polynomial.
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
  exact (Fin.prod_univ_def (fun i => x i ^ d i)).symm

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
  rw [mvPolyVal_eq_sum, toTerms, List.map_map, Finset.sum_map_toList, MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro d _
  simp only [Function.comp_apply, monoList_prodVal]

/-! ### The cube, its polynomial subalgebra, and Stone–Weierstrass density -/

/-- The cube `[0,1]ⁿ` as a `Set.pi` (robustly compact). -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

instance instCompactCube (n : ℕ) : CompactSpace ↥(cube n) :=
  isCompact_iff_compactSpace.mp (isCompact_univ_pi (fun _ => isCompact_Icc))

/-- Coordinate `i` as a continuous function on the cube. -/
def coord {n : ℕ} (i : Fin n) : C(↥(cube n), ℝ) :=
  ⟨fun p => (p : Fin n → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩

/-- The subalgebra of polynomial functions in the coordinates: the range of `aeval` on the
coordinate maps. -/
noncomputable def coordAlg (n : ℕ) : Subalgebra ℝ C(↥(cube n), ℝ) :=
  (MvPolynomial.aeval (coord (n := n))).range

/-- Evaluating the polynomial function `aeval coord q` at a cube point is `MvPolynomial.eval`. -/
theorem aeval_coord_apply {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (p : ↥(cube n)) :
    (MvPolynomial.aeval (coord (n := n)) q) p = MvPolynomial.eval (p : Fin n → ℝ) q := by
  have h := MvPolynomial.comp_aeval_apply (ContinuousMap.evalAlgHom (R := ℝ) (S := ℝ) p)
    (f := coord (n := n)) q
  simp only [ContinuousMap.evalAlgHom_apply] at h
  rw [h]; rfl

/-- The coordinate subalgebra separates points: distinct cube points differ in some coordinate. -/
theorem coordAlg_separatesPoints {n : ℕ} : (coordAlg n).SeparatesPoints := by
  intro x y hxy
  have hne : (x : Fin n → ℝ) ≠ (y : Fin n → ℝ) := fun h => hxy (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine ⟨⇑(coord i), ⟨coord i, ⟨MvPolynomial.X i, MvPolynomial.aeval_X coord i⟩, rfl⟩, ?_⟩
  exact hi

/-- **Stone–Weierstrass on the cube.** Polynomial functions in the coordinates are dense. -/
theorem coordAlg_dense {n : ℕ} : (coordAlg n).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ coordAlg_separatesPoints

/-! ### The capstone: every continuous function on the cube is ReLU-approximable -/

/-- **Multivariate universal approximation.** Every continuous `f` on `[0,1]ⁿ` is uniformly
ε-approximable by an explicit ReLU `Net n` (the compiled monomial-basis polynomial net). The only
imported analytic input is Stone–Weierstrass; the polynomial→net step is the machine-checked
U-1a/b/c. -/
theorem continuous_relu_approximable_cube {n : ℕ} (f : C(↥(cube n), ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (q : MvPolynomial (Fin n) ℝ),
      ∀ p : ↥(cube n), |f p - (mvPolyNet m (toTerms q)).eval (p : Fin n → ℝ)| ≤ ε := by
  -- Stone–Weierstrass: a polynomial `ε/2`-close to `f`.
  have hclo : f ∈ closure ((coordAlg n : Subalgebra ℝ C(↥(cube n), ℝ)) :
      Set C(↥(cube n), ℝ)) := by
    have h2 : f ∈ (coordAlg n).topologicalClosure := by rw [coordAlg_dense]; exact Algebra.mem_top
    exact h2
  obtain ⟨g, hg_mem, hg_dist⟩ := Metric.mem_closure_iff.mp hclo (ε / 2) (by positivity)
  obtain ⟨q, hq⟩ := hg_mem
  rw [ContinuousMap.dist_lt_iff (by positivity)] at hg_dist
  -- a net `ε/2`-close to that polynomial.
  have hB : 0 ≤ errBoundMv (toTerms q) := errBoundMv_nonneg _
  obtain ⟨m, hm⟩ :=
    pow_unbounded_of_one_lt (3 * (errBoundMv (toTerms q) + 1) / (4 * (ε / 2)))
      (by norm_num : (1 : ℝ) < 4)
  have hδ : errBoundMv (toTerms q) * (3 / (4 * 4 ^ m)) ≤ ε / 2 := by
    rw [div_lt_iff₀ (by positivity)] at hm
    rw [show errBoundMv (toTerms q) * (3 / (4 * 4 ^ m))
        = 3 * errBoundMv (toTerms q) / (4 * 4 ^ m) by ring, div_le_iff₀ (by positivity)]
    nlinarith [hm, hε.le, hB]
  refine ⟨m, q, fun p => ?_⟩
  have hgp : g p = MvPolynomial.eval (p : Fin n → ℝ) q := by rw [← hq]; exact aeval_coord_apply q p
  have h1 : |f p - MvPolynomial.eval (p : Fin n → ℝ) q| ≤ ε / 2 := by
    have hd := hg_dist p
    rw [Real.dist_eq, hgp] at hd
    linarith [hd]
  have h2 : |MvPolynomial.eval (p : Fin n → ℝ) q
      - (mvPolyNet m (toTerms q)).eval (p : Fin n → ℝ)| ≤ ε / 2 := by
    rw [← toTerms_eval]
    exact le_trans (mvPolyNet_approx m (toTerms q) (p : Fin n → ℝ)
      (fun i => p.2 i (Set.mem_univ i))) hδ
  calc |f p - (mvPolyNet m (toTerms q)).eval (p : Fin n → ℝ)|
        ≤ |f p - MvPolynomial.eval (p : Fin n → ℝ) q|
          + |MvPolynomial.eval (p : Fin n → ℝ) q
            - (mvPolyNet m (toTerms q)).eval (p : Fin n → ℝ)| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by ring

end Sundog.MvUniversalApprox
