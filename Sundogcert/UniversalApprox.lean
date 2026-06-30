/-
# The general-continuous capstone: every continuous function on [0,1] is ReLU-approximable

This closes the constructive arc of arXiv:2606.26705 (x² → multiply → monomial → polynomial). The
final rung is **universal approximation**: every continuous `f : [0,1] → ℝ` is uniformly
ε-approximable by an explicit ReLU net.

The route is the honest one — polynomials are the bridge:

* **`polyEval_approx`** (the new machine-checked content) — *every polynomial* `q` is uniformly
  ε-approximable on `[0,1]` by the explicit ReLU net `polyNet m (coeffList q)`, via the bridge
  `polyVal_coeffList : polyVal (coeffList q) x = q.eval x` (relating a mathlib `Polynomial` to
  `PolyEval`'s coefficient-list value) composed with `PolyEval.polyNet_approx`.
* **`continuous_relu_approximable`** (the capstone) — every `f ∈ C([0,1], ℝ)` is uniformly
  ε-approximable by such a net. The single imported analytic input is the **Stone–Weierstrass
  theorem** (`polynomialFunctions_closure_eq_top`, mathlib): polynomials are dense in `C([0,1], ℝ)`.
  Given a polynomial `ε/2`-close to `f` (Weierstrass) and a net `ε/2`-close to that polynomial
  (`polyEval_approx`), the triangle inequality finishes.

So the constructive half — turning the dense object (a polynomial) into a ReLU net, uniformly and
explicitly — is fully machine-checked here; density itself is cited from mathlib. Nothing in this
file is `POLY_TO_GENERAL_INCOMPLETE` any longer; that marker is discharged.
-/
import Sundogcert.PolyEval
import Mathlib.Topology.ContinuousMap.Weierstrass

namespace Sundog.UniversalApprox

open Sundog.CircuitNet Sundog.RegionCount Sundog.SawtoothApprox Sundog.PolyEval

/-! ### Bridge: a mathlib `Polynomial` as a `PolyEval` coefficient list -/

/-- The coefficient list `[q.coeff 0, …, q.coeff (natDegree q)]` of a polynomial. -/
noncomputable def coeffList (q : Polynomial ℝ) : List ℝ :=
  (List.range (q.natDegree + 1)).map (fun i => q.coeff i)

/-- The Horner fold's value of a singleton-appended list peels the top monomial. -/
theorem polyValFrom_append_singleton (i : ℕ) (L : List ℝ) (a x : ℝ) :
    polyValFrom i (L ++ [a]) x = polyValFrom i L x + a * x ^ (i + L.length) := by
  induction L generalizing i with
  | nil => simp [polyValFrom]
  | cons c cs ih =>
    simp only [List.cons_append, polyValFrom, List.length_cons]
    rw [ih (i + 1)]
    have he : i + 1 + cs.length = i + (cs.length + 1) := by omega
    rw [he]; ring

/-- `polyVal` of a mapped `range` is the explicit finite sum `Σⱼ g j · xʲ`. -/
theorem polyVal_range_map (n : ℕ) (g : ℕ → ℝ) (x : ℝ) :
    polyVal ((List.range n).map g) x = ∑ i ∈ Finset.range n, g i * x ^ i := by
  unfold polyVal
  induction n with
  | zero => simp [polyValFrom]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      polyValFrom_append_singleton, List.length_map, List.length_range, Finset.sum_range_succ, ih]
    simp

/-- **The bridge.** `PolyEval`'s value on `coeffList q` is exactly `q.eval`. -/
theorem polyVal_coeffList (q : Polynomial ℝ) (x : ℝ) : polyVal (coeffList q) x = q.eval x := by
  rw [coeffList, polyVal_range_map]
  exact (Polynomial.eval_eq_sum_range x).symm

/-! ### Every polynomial is uniformly approximable by an explicit ReLU net -/

/-- **Polynomials → ReLU nets, uniformly.** For any polynomial `q` and `ε > 0`, the explicit ReLU
net `polyNet m (coeffList q)` approximates `q` to error `≤ ε` everywhere on `[0,1]`. -/
theorem polyEval_approx (q : Polynomial ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |q.eval x - realize1N (polyNet m (coeffList q)) x| ≤ ε := by
  set B := errBound 0 (coeffList q) with hBdef
  have hB : 0 ≤ B := errBound_nonneg 0 (coeffList q)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 * (B + 1) / (4 * ε)) (by norm_num : (1 : ℝ) < 4)
  have hδ : B * (3 / (4 * 4 ^ m)) ≤ ε := by
    rw [div_lt_iff₀ (by positivity)] at hm
    have hrw : B * (3 / (4 * 4 ^ m)) = 3 * B / (4 * 4 ^ m) := by ring
    rw [hrw, div_le_iff₀ (by positivity)]
    nlinarith [hm, hε.le, hB]
  refine ⟨m, fun x hx => ?_⟩
  calc |q.eval x - realize1N (polyNet m (coeffList q)) x|
        = |polyVal (coeffList q) x - realize1N (polyNet m (coeffList q)) x| := by
          rw [polyVal_coeffList]
    _ ≤ B * (3 / (4 * 4 ^ m)) := polyNet_approx m (coeffList q) x hx
    _ ≤ ε := hδ

/-! ### The capstone: universal approximation (Weierstrass + `polyEval_approx`) -/

/-- **Universal approximation.** Every continuous `f : [0,1] → ℝ` is uniformly ε-approximable by an
explicit ReLU net (the compiled monomial-basis polynomial net `polyNet m (coeffList q)`). The only
imported analytic input is the Stone–Weierstrass theorem; the polynomial-to-net step is the
machine-checked `polyEval_approx`. -/
theorem continuous_relu_approximable
    (f : C(↥(Set.Icc (0 : ℝ) 1), ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (q : Polynomial ℝ), ∀ x : ↥(Set.Icc (0 : ℝ) 1),
      |f x - realize1N (polyNet m (coeffList q)) (x : ℝ)| ≤ ε := by
  haveI : Nonempty ↥(Set.Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  -- (1) Stone–Weierstrass: a polynomial `ε/2`-close to `f`.
  have hclo : f ∈ closure
      (polynomialFunctions (Set.Icc (0 : ℝ) 1) : Set C(↥(Set.Icc (0 : ℝ) 1), ℝ)) := by
    have h2 : f ∈ (polynomialFunctions (Set.Icc (0 : ℝ) 1)).topologicalClosure := by
      rw [polynomialFunctions_closure_eq_top]; exact Algebra.mem_top
    exact h2
  obtain ⟨pf, hpf_mem, hpf_dist⟩ := Metric.mem_closure_iff.mp hclo (ε / 2) (by positivity)
  rw [polynomialFunctions_coe] at hpf_mem
  obtain ⟨q, hq⟩ := hpf_mem
  rw [ContinuousMap.dist_lt_iff (by positivity)] at hpf_dist
  -- (2) `polyEval_approx`: a net `ε/2`-close to that polynomial.
  obtain ⟨m, hnet⟩ := polyEval_approx q (ε / 2) (by positivity)
  refine ⟨m, q, fun x => ?_⟩
  have hfx : |f x - pf x| < ε / 2 := by have := hpf_dist x; rwa [Real.dist_eq] at this
  have hpfx : pf x = q.eval (x : ℝ) := by
    rw [← hq]; simp [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply]
  -- (3) triangle inequality.
  calc |f x - realize1N (polyNet m (coeffList q)) (x : ℝ)|
        ≤ |f x - pf x| + |pf x - realize1N (polyNet m (coeffList q)) (x : ℝ)| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 :=
          add_le_add (le_of_lt hfx) (by rw [hpfx]; exact hnet x x.2)
    _ = ε := by ring

end Sundog.UniversalApprox
