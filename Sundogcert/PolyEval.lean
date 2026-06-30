/-
# General polynomials at the polynomial rate (S3-4, continuation past monomials)

`MonomialEval` gives `x^d` as a ReLU net of depth `O(d·log 1/ε)`. A general polynomial
`p(x) = Σ aᵢ xⁱ` is then a *linear combination* of those monomial nets — and crucially the
combination needs no new approximation:

* **Why not Horner-as-a-circuit.** The textbook Horner scheme `aᵢ + x·rₙ` would feed the running
  value `rₙ` into the multiply gate, but `rₙ` is not bounded in `[0,1]`, so the gate's domain
  assumption fails. Instead we keep the *value* defined by the Horner fold (which equals `Σ aᵢ xⁱ`)
  but build the *circuit* in the **monomial basis**: `Σ aᵢ · (xⁱ net)`. The only nonlinear
  pieces are the `xⁱ` (each kept in `[0,1]` by `MonomialEval`'s clamp); the `Σ aᵢ · (·)` is an
  *exact* tropical scale+add, so no domain question arises.

* **`polyTrop_approx`** — `|p(x) − net(x)| ≤ (Σᵢ |aᵢ|·i) · δ`, `δ = 3/(4·4^m)`: the per-monomial
  errors (`|aᵢ|·i·δ`) add up. The bound `errBound` is the exact `Σ |aᵢ|·i`.
* **`polyTrop_depth`** — `≤ (#coeffs)·((Rcirc m).depth + 13)`, i.e. `O(deg · m)`.
* **`poly_polylog`** — for any `ε > 0`, an explicit ReLU net computing `p` on `[0,1]` to error
  `ε` at depth `O(deg · log 1/ε)` — arXiv:2606.26705 Cor 5.1's rate, for an arbitrary polynomial.

Honest boundary: this is the full **polynomial** rate. The remaining step to a general continuous
target is the partition-of-unity / local-Taylor assembly, named `POLY_TO_GENERAL_INCOMPLETE`.
-/
import Sundogcert.MonomialEval

namespace Sundog.PolyEval

open Sundog.CircuitNet Sundog.RegionCount Sundog.SawtoothApprox Sundog.MultiplyGate
open Sundog.MonomialEval

/-! ### The monomial `xⁱ` (a `const 1` for `i = 0`, else the `MonomialEval` chain) -/

/-- Circuit for `xⁱ`: `const 1` when `i = 0`, else the degree-`i` monomial `powTrop m (i-1)`. -/
noncomputable def monoTrop (m : ℕ) : ℕ → Trop 1
  | 0 => Trop.const 1
  | (i + 1) => powTrop m i

theorem monoTrop_approx (m i : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ i - (monoTrop m i).eval (fun _ => x)| ≤ (i : ℝ) * (3 / (4 * 4 ^ m)) := by
  cases i with
  | zero => simp [monoTrop, Trop.eval_const]
  | succ i =>
    simp only [monoTrop]
    refine le_trans (powTrop_approx m i x hx) ?_
    have : (0 : ℝ) ≤ 3 / (4 * 4 ^ m) := by positivity
    push_cast
    nlinarith [this]

theorem monoTrop_depth (m i : ℕ) : (monoTrop m i).depth ≤ i * ((Rcirc m).depth + 12) := by
  cases i with
  | zero => simp [monoTrop, Trop.depth]
  | succ i =>
    simp only [monoTrop]
    exact le_trans (powTrop_depth m i) (Nat.mul_le_mul (Nat.le_succ i) (le_refl _))

/-! ### The polynomial: value (Horner fold), circuit (monomial sum), and error budget -/

/-- `polyValFrom i [c, …] x = c·xⁱ + …` — the Horner fold; `polyValFrom 0 coeffs x = Σⱼ cⱼ xʲ`. -/
def polyValFrom : ℕ → List ℝ → ℝ → ℝ
  | _, [], _ => 0
  | i, (c :: cs), x => c * x ^ i + polyValFrom (i + 1) cs x

/-- The monomial-basis circuit `Σⱼ cⱼ · (x^(i+j) net)`. -/
noncomputable def polyTropFrom (m : ℕ) : ℕ → List ℝ → Trop 1
  | _, [] => Trop.const 0
  | i, (c :: cs) => Trop.add (Trop.scale c (monoTrop m i)) (polyTropFrom m (i + 1) cs)

/-- The exact error budget `Σⱼ |cⱼ|·(i+j)`. -/
def errBound : ℕ → List ℝ → ℝ
  | _, [] => 0
  | i, (c :: cs) => |c| * i + errBound (i + 1) cs

theorem errBound_nonneg (i : ℕ) (coeffs : List ℝ) : 0 ≤ errBound i coeffs := by
  induction coeffs generalizing i with
  | nil => simp [errBound]
  | cons c cs ih =>
    simp only [errBound]
    exact add_nonneg (mul_nonneg (abs_nonneg c) (Nat.cast_nonneg i)) (ih (i + 1))

/-- **Polynomial error bound.** The monomial-sum circuit approximates the Horner value with error
`≤ (Σ |cⱼ|·(i+j))·δ` — the per-monomial errors add. -/
theorem polyTropFrom_approx (m : ℕ) (coeffs : List ℝ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i, |polyValFrom i coeffs x - (polyTropFrom m i coeffs).eval (fun _ => x)|
        ≤ errBound i coeffs * (3 / (4 * 4 ^ m)) := by
  induction coeffs with
  | nil => intro i; simp [polyValFrom, polyTropFrom, errBound, Trop.eval_const]
  | cons c cs ih =>
    intro i
    simp only [polyValFrom, polyTropFrom, errBound, Trop.eval_add, Trop.eval_scale]
    have hmono : |x ^ i - (monoTrop m i).eval (fun _ => x)| ≤ (i : ℝ) * (3 / (4 * 4 ^ m)) :=
      monoTrop_approx m i x hx
    have hih := ih (i + 1)
    set MV := (monoTrop m i).eval (fun _ => x)
    set PV := (polyTropFrom m (i + 1) cs).eval (fun _ => x)
    have htri : |c * x ^ i + polyValFrom (i + 1) cs x - (c * MV + PV)|
        ≤ |c * x ^ i - c * MV| + |polyValFrom (i + 1) cs x - PV| := by
      have he : c * x ^ i + polyValFrom (i + 1) cs x - (c * MV + PV)
          = (c * x ^ i - c * MV) + (polyValFrom (i + 1) cs x - PV) := by ring
      rw [he]; exact abs_add_le _ _
    have hc : |c * x ^ i - c * MV| ≤ |c| * ((i : ℝ) * (3 / (4 * 4 ^ m))) := by
      rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left hmono (abs_nonneg c)
    calc |c * x ^ i + polyValFrom (i + 1) cs x - (c * MV + PV)|
          ≤ |c * x ^ i - c * MV| + |polyValFrom (i + 1) cs x - PV| := htri
      _ ≤ |c| * ((i : ℝ) * (3 / (4 * 4 ^ m))) + errBound (i + 1) cs * (3 / (4 * 4 ^ m)) :=
            add_le_add hc hih
      _ = (|c| * i + errBound (i + 1) cs) * (3 / (4 * 4 ^ m)) := by ring

/-- **Linear-in-degree depth.** -/
theorem polyTropFrom_depth (m : ℕ) (coeffs : List ℝ) :
    ∀ i, (polyTropFrom m i coeffs).depth
        ≤ coeffs.length + (i + coeffs.length) * ((Rcirc m).depth + 12) := by
  induction coeffs with
  | nil => intro i; simp [polyTropFrom, Trop.depth]
  | cons c cs ih =>
    intro i
    simp only [polyTropFrom, Trop.depth, List.length_cons]
    set C := (Rcirc m).depth + 12 with hC
    have hmono : (monoTrop m i).depth ≤ i * C := monoTrop_depth m i
    have hih : (polyTropFrom m (i + 1) cs).depth ≤ cs.length + (i + 1 + cs.length) * C := ih (i + 1)
    have hk1 : 1 + (monoTrop m i).depth ≤ cs.length + (i + (cs.length + 1)) * C := by
      have hexp : (i + (cs.length + 1)) * C = i * C + (cs.length + 1) * C := by ring
      have hpos : 1 ≤ (cs.length + 1) * C := by
        have : 1 * 1 ≤ (cs.length + 1) * C := Nat.mul_le_mul (by omega) (by omega)
        omega
      omega
    have hk2 : (polyTropFrom m (i + 1) cs).depth ≤ cs.length + (i + (cs.length + 1)) * C := by
      have : (i + 1 + cs.length) * C = (i + (cs.length + 1)) * C := by ring
      omega
    calc 1 + max (1 + (monoTrop m i).depth) ((polyTropFrom m (i + 1) cs).depth)
          ≤ 1 + (cs.length + (i + (cs.length + 1)) * C) := by
            have := max_le hk1 hk2; omega
      _ = (cs.length + 1) + (i + (cs.length + 1)) * C := by ring

/-! ### Top-level polynomial and the polynomial-rate statement -/

/-- The polynomial value `Σⱼ cⱼ xʲ`. -/
def polyVal (coeffs : List ℝ) (x : ℝ) : ℝ := polyValFrom 0 coeffs x

/-- The monomial-basis ReLU-circuit for the polynomial. -/
noncomputable def polyTrop (m : ℕ) (coeffs : List ℝ) : Trop 1 := polyTropFrom m 0 coeffs

theorem polyTrop_approx (m : ℕ) (coeffs : List ℝ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |polyVal coeffs x - (polyTrop m coeffs).eval (fun _ => x)|
      ≤ errBound 0 coeffs * (3 / (4 * 4 ^ m)) :=
  polyTropFrom_approx m coeffs x hx 0

theorem polyTrop_depth (m : ℕ) (coeffs : List ℝ) :
    (polyTrop m coeffs).depth ≤ coeffs.length * ((Rcirc m).depth + 13) := by
  calc (polyTrop m coeffs).depth
        ≤ coeffs.length + (0 + coeffs.length) * ((Rcirc m).depth + 12) :=
          polyTropFrom_depth m coeffs 0
    _ = coeffs.length * ((Rcirc m).depth + 13) := by ring

/-- The polynomial's ReLU net. -/
noncomputable def polyNet (m : ℕ) (coeffs : List ℝ) : Net 1 := compile (polyTrop m coeffs)

theorem polyNet_approx (m : ℕ) (coeffs : List ℝ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |polyVal coeffs x - realize1N (polyNet m coeffs) x|
      ≤ errBound 0 coeffs * (3 / (4 * 4 ^ m)) := by
  have h : realize1N (polyNet m coeffs) x = (polyTrop m coeffs).eval (fun _ => x) := by
    rw [polyNet, realize1_compile]; rfl
  rw [h]; exact polyTrop_approx m coeffs x hx

theorem polyNet_depth (m : ℕ) (coeffs : List ℝ) :
    (polyNet m coeffs).depth ≤ 4 * (coeffs.length * ((Rcirc m).depth + 13)) := by
  calc (polyNet m coeffs).depth
        ≤ 4 * (polyTrop m coeffs).depth := compile_depth_le (polyTrop m coeffs)
    _ ≤ 4 * (coeffs.length * ((Rcirc m).depth + 13)) := by have := polyTrop_depth m coeffs; omega

/-- **The polynomial rate.** For any coefficient list and any `ε > 0`, an explicit ReLU net computes
the polynomial `Σ cⱼ xʲ` on `[0,1]` to error `≤ ε`, of depth `O(deg · m)` where the error budget
times `3/(4·4^m) ≤ ε`. With `m = O(log(deg/ε))` this is depth `O(deg · log 1/ε)` — arXiv:2606.26705
Cor 5.1's polynomial rate, for an arbitrary polynomial. -/
theorem poly_polylog (coeffs : List ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Net 1),
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |polyVal coeffs x - realize1N g x| ≤ ε) ∧
      g.depth ≤ 4 * (coeffs.length * ((Rcirc m).depth + 13)) ∧
      errBound 0 coeffs * (3 / (4 * 4 ^ m)) ≤ ε := by
  have hB : 0 ≤ errBound 0 coeffs := errBound_nonneg 0 coeffs
  obtain ⟨m, hm⟩ :=
    pow_unbounded_of_one_lt (3 * (errBound 0 coeffs + 1) / (4 * ε)) (by norm_num : (1 : ℝ) < 4)
  have hδ : errBound 0 coeffs * (3 / (4 * 4 ^ m)) ≤ ε := by
    rw [div_lt_iff₀ (by positivity)] at hm
    rw [show errBound 0 coeffs * (3 / (4 * 4 ^ m)) = 3 * errBound 0 coeffs / (4 * 4 ^ m) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith [hm, hε.le, hB]
  exact ⟨m, polyNet m coeffs, fun x hx => le_trans (polyNet_approx m coeffs x hx) hδ,
    polyNet_depth m coeffs, hδ⟩

end Sundog.PolyEval
