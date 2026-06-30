/-
# Toward the general analytic gate: an ε-multiplication gate at log depth (S3-4, continuation)

`SawtoothApprox` approximates `x²` to any `ε` by a ReLU net of depth `O(log 1/ε)` (the polylog
rate). The pivotal step from "one analytic gate" to "all of them" is **multiplication**: by
polarization,
  `x·y = ((x+y)² − x² − y²) / 2`,
so three (rescaled) copies of the `x²` net give an ε-approximate multiply gate. Multiplication is
the hinge of Yarotsky's general construction — with an ε-multiply gate you get every polynomial
(product/Horner trees), and by Weierstrass every continuous function. This module lands the gate:

* **`mult_approx`** — `|x·y − multTrop m (x,y)| ≤ 3 / (4·4^m)` on `[0,1]²` (three `x²` errors plus
  the exact polarization identity; the `(x+y)²` term rescaled, `(x+y)² = 4·((x+y)/2)²`).
* **`multTrop_depth`** — depth `≤ (Rcirc m).depth + 6`, i.e. `O(m)` (the three `x²` circuits grafted
  into the linear forms add only constant depth).
* **`mult_polylog`** — for any `ε > 0`, an explicit two-input ReLU net computing `x·y` to error `ε`
  at depth `O(log 1/ε)`.

Honest boundary: this is the *multiplication* gate (the hinge), reusing the `x²` polylog engine.
The full Cor 5.1 for a general target still needs the polynomial assembly + partition-of-unity
layer on top — that is the staged continuation, named `MULT_TO_GENERAL_INCOMPLETE`.
-/
import Sundogcert.SawtoothApprox

namespace Sundog.MultiplyGate

open Sundog.CircuitNet Sundog.RegionCount Sundog.DepthSeparation Sundog.SawtoothApprox

/-! ### Grafting a 1-input circuit into an n-input expression (function composition) -/

/-- Substitute the `n`-input expression `g` for the single input of a 1-input circuit `e`,
producing an `n`-input circuit that computes `e ∘ g`. (The `n`-ary generalization of
`DepthSeparation.subst0`.) -/
def graft {n : ℕ} : Trop 1 → Trop n → Trop n
  | .var _, g => g
  | .const c, _ => .const c
  | .add a b, g => .add (graft a g) (graft b g)
  | .scale c a, g => .scale c (graft a g)
  | .max a b, g => .max (graft a g) (graft b g)

theorem graft_eval {n : ℕ} (e : Trop 1) (g : Trop n) (x : Fin n → ℝ) :
    (graft e g).eval x = e.eval (fun _ => g.eval x) := by
  induction e with
  | var i => simp [graft, Trop.eval_var]
  | const c => simp [graft, Trop.eval_const]
  | add a b iha ihb => simp [graft, Trop.eval_add, iha, ihb]
  | scale c a ih => simp [graft, Trop.eval_scale, ih]
  | max a b iha ihb => simp [graft, Trop.eval_max, iha, ihb]

theorem graft_depth_le {n : ℕ} (e : Trop 1) (g : Trop n) :
    (graft e g).depth ≤ e.depth + g.depth := by
  induction e with
  | var i => simp [graft, Trop.depth]
  | const c => simp [graft, Trop.depth]
  | add a b iha ihb => simp only [graft, Trop.depth, Nat.max_def]; split_ifs <;> omega
  | scale c a ih => simp only [graft, Trop.depth]; omega
  | max a b iha ihb => simp only [graft, Trop.depth, Nat.max_def]; split_ifs <;> omega

/-! ### The multiplication gate -/

/-- The linear form `(x + y) / 2` as a 2-input tropical circuit. -/
noncomputable def halfSum : Trop 2 := .scale (1 / 2) (.add (.var 0) (.var 1))

/-- The ε-multiply circuit: `(4·sq((x+y)/2) − sq(x) − sq(y)) / 2`, where `sq = Rcirc m` is the `x²`
polylog circuit and `(x+y)²` is recovered as `4·((x+y)/2)²` to keep the input in `[0,1]`. -/
noncomputable def multTrop (m : ℕ) : Trop 2 :=
  .scale (1 / 2)
    (.add (.add (.scale 4 (graft (Rcirc m) halfSum))
                (.scale (-1) (graft (Rcirc m) (.var 0))))
          (.scale (-1) (graft (Rcirc m) (.var 1))))

theorem multTrop_eval (m : ℕ) (v : Fin 2 → ℝ) :
    (multTrop m).eval v
      = (4 * R m (1 / 2 * (v 0 + v 1)) - R m (v 0) - R m (v 1)) / 2 := by
  simp only [multTrop, halfSum, Trop.eval_scale, Trop.eval_add, Trop.eval_var, graft_eval,
    Rcirc_eval]
  ring

/-- **The multiplication error bound.** On `[0,1]²` the gate computes `x·y` to error `3/(4·4^m)` —
three `x²` errors combined through the exact polarization identity. -/
theorem mult_approx (m : ℕ) (v : Fin 2 → ℝ)
    (hx : v 0 ∈ Set.Icc (0 : ℝ) 1) (hy : v 1 ∈ Set.Icc (0 : ℝ) 1) :
    |v 0 * v 1 - (multTrop m).eval v| ≤ 3 / (4 * 4 ^ m) := by
  rw [multTrop_eval]
  have hs : 1 / 2 * (v 0 + v 1) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  obtain ⟨h1l, h1r⟩ := abs_le.mp (sq_sub_R_le m (1 / 2 * (v 0 + v 1)) hs)
  obtain ⟨h2l, h2r⟩ := abs_le.mp (sq_sub_R_le m (v 0) hx)
  obtain ⟨h3l, h3r⟩ := abs_le.mp (sq_sub_R_le m (v 1) hy)
  -- polarization: the error is a fixed linear combination of the three x^2 errors
  have key : v 0 * v 1 - (4 * R m (1 / 2 * (v 0 + v 1)) - R m (v 0) - R m (v 1)) / 2
      = 2 * ((1 / 2 * (v 0 + v 1)) ^ 2 - R m (1 / 2 * (v 0 + v 1)))
        - ((v 0) ^ 2 - R m (v 0)) / 2 - ((v 1) ^ 2 - R m (v 1)) / 2 := by ring
  have hδ : (3 : ℝ) / (4 * 4 ^ m) = 3 * (1 / (4 * 4 ^ m)) := by ring
  rw [key, abs_le]
  constructor <;> linarith [h1l, h1r, h2l, h2r, h3l, h3r, hδ]

/-- **Linear depth.** Grafting the three `x²` circuits into the linear forms adds only constant
depth, so the multiply circuit stays `O(m)` deep. -/
theorem multTrop_depth (m : ℕ) : (multTrop m).depth ≤ (Rcirc m).depth + 6 := by
  have ha := graft_depth_le (Rcirc m) halfSum
  have hb := graft_depth_le (Rcirc m) (Trop.var (0 : Fin 2))
  have hc := graft_depth_le (Rcirc m) (Trop.var (1 : Fin 2))
  have hhd : halfSum.depth = 2 := rfl
  have hvd0 : (Trop.var (0 : Fin 2)).depth = 0 := rfl
  have hvd1 : (Trop.var (1 : Fin 2)).depth = 0 := rfl
  rw [hhd] at ha; rw [hvd0] at hb; rw [hvd1] at hc
  simp only [multTrop, Trop.depth, Nat.max_def]
  split_ifs <;> omega

/-! ### The ReLU net and the polylog statement -/

/-- The two-input ReLU net for ε-multiplication: the multiply circuit, compiled. -/
noncomputable def multNet (m : ℕ) : Net 2 := compile (multTrop m)

theorem multNet_eval (m : ℕ) (v : Fin 2 → ℝ) : (multNet m).eval v = (multTrop m).eval v :=
  compile_eval (multTrop m) v

/-- **Net error.** `|x·y − net(x,y)| ≤ 3/(4·4^m)` on `[0,1]²`. -/
theorem multNet_approx (m : ℕ) (v : Fin 2 → ℝ)
    (hx : v 0 ∈ Set.Icc (0 : ℝ) 1) (hy : v 1 ∈ Set.Icc (0 : ℝ) 1) :
    |v 0 * v 1 - (multNet m).eval v| ≤ 3 / (4 * 4 ^ m) := by
  rw [multNet_eval]; exact mult_approx m v hx hy

/-- **Net depth** — `O(m)`. -/
theorem multNet_depth (m : ℕ) : (multNet m).depth ≤ 4 * ((Rcirc m).depth + 6) := by
  calc (multNet m).depth ≤ 4 * (multTrop m).depth := compile_depth_le (multTrop m)
    _ ≤ 4 * ((Rcirc m).depth + 6) := by have := multTrop_depth m; omega

/-- **The polylog multiplication gate.** For every `ε > 0` there is an explicit two-input ReLU net
computing `x·y` on `[0,1]²` to error `≤ ε`, of depth `O(m)` where `3/(4·4^m) ≤ ε` — depth
`O(log 1/ε)`. The hinge of the general analytic-gate construction, at the polylog rate. -/
theorem mult_polylog (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Net 2),
      (∀ v : Fin 2 → ℝ, v 0 ∈ Set.Icc (0 : ℝ) 1 → v 1 ∈ Set.Icc (0 : ℝ) 1 →
        |v 0 * v 1 - g.eval v| ≤ ε) ∧
      g.depth ≤ 4 * ((Rcirc m).depth + 6) ∧
      (3 : ℝ) / (4 * 4 ^ m) ≤ ε := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (3 / (4 * ε)) (by norm_num : (1 : ℝ) < 4)
  refine ⟨m, multNet m, fun v hx hy => le_trans (multNet_approx m v hx hy) ?_, multNet_depth m, ?_⟩
  all_goals {
    rw [div_le_iff₀ (by positivity)]
    have h4ε : (0 : ℝ) < 4 * ε := by positivity
    have hlt : 3 / (4 * ε) < 4 ^ m := hm
    rw [div_lt_iff₀ h4ε] at hlt
    nlinarith [hlt]
  }

end Sundog.MultiplyGate
