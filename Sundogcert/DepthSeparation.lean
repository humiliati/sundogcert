/-
# Depth separation: exponential linear regions from linear tropical depth (C-D1)

The Lean realization of slate hook **C-D1**: the classical piecewise-linear depth
separations (Telgarsky's sawtooth) are *tropical-depth* separations. The witness is the
**tent map** `T(x) = 1 - |2x - 1|`, which lies in the exactly-ReLU-representable tropical
fragment (`max`/`abs`/affine). Its `d`-fold composition `T^[d]` is realized by a tropical
circuit of depth `O(d)` (hence a ReLU net of depth `O(d)` via `compile_depth_le`) yet
oscillates `2^d` times — exponentially many linear regions from *linear* depth. This is the
formal core of "depth = computation": depth buys composition, and composition buys
exponential expressivity.

## What is PROVED here

* **`tent_eval`** — the `Trop` circuit `tent` computes `T(x) = 1 - |2x - 1|` exactly.
* **`iterTent_eval`** — `iterTent d` (the `d`-fold substitution of `tent` into itself) is a
  tropical circuit computing `T^[d]`.
* **`iterTent_depth_le`** — `iterTent d` has depth `≤ d · depth(tent)`, i.e. **linear in d**.
  Composed with `CircuitNet.compile_depth_le`, the ReLU realization also has depth `O(d)`.
* **`tent_iterate_dyadic` (the punchline)** — `T^[d](j / 2^d) = 1` if `j` is odd and `0`
  if `j` is even, for `0 ≤ j ≤ 2^d`. The `2^d + 1` dyadic samples alternate `0,1,0,1,…`, so
  `T^[d]` has at least `2^d` monotone (linear) pieces — **exponentially many linear regions
  from a depth-`O(d)` circuit**.

## The IMPORTED WALL (named, NOT proved here)

* **The depth-vs-WIDTH separation** — that *no* shallow (depth `< d`) ReLU net of
  sub-exponential width can match `2^d` linear regions — is the classical lower bound
  (Telgarsky 2016; Eldan–Shamir 2016), **imported**. This module proves the *upper* side
  (a depth-`O(d)` circuit achieves `2^d` regions); the matching width lower bound for
  shallow nets is the named wall, as everywhere in this development.

## References
* Telgarsky, *Benefits of depth in neural networks*, COLT 2016 (the sawtooth depth
  separation; the `d`-fold tent has `2^d` linear pieces).
-/
import Sundogcert.CircuitNet
import Mathlib.Logic.Function.Iterate

namespace Sundog.DepthSeparation

open Sundog.CircuitNet

/-- The tent map `T(x) = 1 - |2x - 1|` (peak `1` at `x = 1/2`, zero at `0` and `1`). -/
noncomputable def T (x : ℝ) : ℝ := 1 - |2 * x - 1|

/-- The tent map as a tropical circuit: `1 + (-1)·|2·x₀ + (-1)|`. -/
def tent : Trop 1 :=
  .add (.const 1) (.scale (-1) (Trop.abs (.add (.scale 2 (.var 0)) (.const (-1)))))

/-- The tropical circuit `tent` computes the tent map exactly. -/
theorem tent_eval (x : Fin 1 → ℝ) : tent.eval x = T (x 0) := by
  simp only [tent, Trop.eval_add, Trop.eval_const, Trop.eval_scale, abs_eval,
    Trop.eval_var, T]
  have : (2 : ℝ) * x 0 + (-1) = 2 * x 0 - 1 := by ring
  rw [this]; ring

/-- Substitute the circuit `g` for the single input variable of `e` (all `var`s, since
`n = 1`). This realizes function composition `e ∘ g`. -/
def subst0 : Trop 1 → Trop 1 → Trop 1
  | .var _,     g => g
  | .const c,   _ => .const c
  | .add a b,   g => .add (subst0 a g) (subst0 b g)
  | .scale c a, g => .scale c (subst0 a g)
  | .max a b,   g => .max (subst0 a g) (subst0 b g)

/-- Substitution realizes composition: `subst0 e g` computes `e` on input `g(x)`. -/
theorem subst0_eval (e g : Trop 1) (x : Fin 1 → ℝ) :
    (subst0 e g).eval x = e.eval (fun _ => g.eval x) := by
  induction e with
  | var i => simp [subst0, Trop.eval_var]
  | const c => simp [subst0, Trop.eval_const]
  | add a b iha ihb => simp [subst0, Trop.eval_add, iha, ihb]
  | scale c a ih => simp [subst0, Trop.eval_scale, ih]
  | max a b iha ihb => simp [subst0, Trop.eval_max, iha, ihb]

/-- The `d`-fold tent circuit: substitute `tent` into the running circuit `d` times. -/
def iterTent : ℕ → Trop 1
  | 0     => .var 0
  | d + 1 => subst0 (iterTent d) tent

/-- `iterTent d` computes the `d`-fold composition `T^[d]`. -/
theorem iterTent_eval : ∀ (d : ℕ) (x : Fin 1 → ℝ), (iterTent d).eval x = T^[d] (x 0) := by
  intro d
  induction d with
  | zero => intro x; simp [iterTent, Trop.eval_var]
  | succ d ih =>
      intro x
      simp only [iterTent, subst0_eval, ih, tent_eval, Function.iterate_succ_apply]

/-- Substitution adds at most `depth g` to the depth. -/
theorem subst0_depth_le (e g : Trop 1) :
    (subst0 e g).depth ≤ e.depth + g.depth := by
  induction e with
  | var i => simp [subst0, Trop.depth]
  | const c => simp [subst0, Trop.depth]
  | add a b iha ihb => simp only [subst0, Trop.depth, Nat.max_def]; split_ifs <;> omega
  | scale c a ih => simp only [subst0, Trop.depth]; omega
  | max a b iha ihb => simp only [subst0, Trop.depth, Nat.max_def]; split_ifs <;> omega

/-- **The `d`-fold tent circuit has depth linear in `d`.** Hence (via
`CircuitNet.compile_depth_le`) its ReLU realization also has depth `O(d)`. -/
theorem iterTent_depth_le (d : ℕ) : (iterTent d).depth ≤ d * tent.depth := by
  induction d with
  | zero => simp [iterTent, Trop.depth]
  | succ d ih =>
      have h := subst0_depth_le (iterTent d) tent
      calc (iterTent (d + 1)).depth
          = (subst0 (iterTent d) tent).depth := by rw [iterTent]
        _ ≤ (iterTent d).depth + tent.depth := h
        _ ≤ d * tent.depth + tent.depth := by omega
        _ = (d + 1) * tent.depth := by ring

/-- **The oscillation (THE PUNCHLINE).** At the `2^d + 1` dyadic samples `j / 2^d`,
`T^[d]` alternates: it is `1` when `j` is odd and `0` when `j` is even. So the depth-`O(d)`
tent circuit produces `2^d` sign alternations — at least `2^d` linear pieces, exponentially
many in the depth. -/
theorem tent_iterate_dyadic :
    ∀ (d : ℕ) (j : ℕ), j ≤ 2 ^ d → T^[d] ((j : ℝ) / 2 ^ d) = if Odd j then 1 else 0 := by
  intro d
  induction d with
  | zero =>
      intro j hj
      simp only [pow_zero] at hj ⊢
      interval_cases j
      · simp
      · simp
  | succ d ih =>
      intro j hj
      rw [Function.iterate_succ_apply]
      -- inner step: T(j / 2^(d+1)) = (reflected j) / 2^d
      have h2d : (0 : ℝ) < 2 ^ d := by positivity
      have hTj : T ((j : ℝ) / 2 ^ (d + 1)) =
          (if j ≤ 2 ^ d then (j : ℝ) / 2 ^ d else ((2 ^ (d + 1) - j : ℕ) : ℝ) / 2 ^ d) := by
        unfold T
        have hpow : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
        by_cases hle : j ≤ 2 ^ d
        · rw [if_pos hle]
          have hx : (2 : ℝ) * ((j : ℝ) / 2 ^ (d + 1)) - 1 = (j : ℝ) / 2 ^ d - 1 := by
            rw [hpow]; field_simp
          rw [hx]
          have hjle : (j : ℝ) / 2 ^ d ≤ 1 := by
            rw [div_le_one h2d]; exact_mod_cast hle
          rw [abs_of_nonpos (by linarith)]; ring
        · rw [if_neg hle]
          have hgt : 2 ^ d < j := by omega
          have hx : (2 : ℝ) * ((j : ℝ) / 2 ^ (d + 1)) - 1 = (j : ℝ) / 2 ^ d - 1 := by
            rw [hpow]; field_simp
          rw [hx]
          have hjge : (1 : ℝ) ≤ (j : ℝ) / 2 ^ d := by
            rw [one_le_div h2d]; exact_mod_cast hgt.le
          rw [abs_of_nonneg (by linarith)]
          have hcast : ((2 ^ (d + 1) - j : ℕ) : ℝ) = (2 : ℝ) ^ (d + 1) - j := by
            have : j ≤ 2 ^ (d + 1) := hj
            push_cast [Nat.cast_sub this]; ring
          rw [hcast, hpow]; field_simp; ring
      rw [hTj]
      by_cases hle : j ≤ 2 ^ d
      · rw [if_pos hle, ih j hle]
      · rw [if_neg hle]
        have hj' : 2 ^ (d + 1) - j ≤ 2 ^ d := by
          have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
          omega
        rw [ih _ hj']
        -- parity of the reflection equals parity of j (2^(d+1) is even)
        have hpar : Odd (2 ^ (d + 1) - j) ↔ Odd j := by
          have heven : Even (2 ^ (d + 1)) := ⟨2 ^ d, by rw [pow_succ]; ring⟩
          rcases heven with ⟨m, hm⟩
          constructor
          · intro ⟨t, ht⟩; refine ⟨m - t - 1, ?_⟩; omega
          · intro ⟨t, ht⟩; refine ⟨m - t - 1, ?_⟩; omega
        by_cases ho : Odd j
        · rw [if_pos (hpar.mpr ho), if_pos ho]
        · have hno : ¬ Odd (2 ^ (d + 1) - j) := fun h => ho (hpar.mp h)
          rw [if_neg hno, if_neg ho]

end Sundog.DepthSeparation

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.DepthSeparation.iterTent_eval
#print axioms Sundog.DepthSeparation.iterTent_depth_le
#print axioms Sundog.DepthSeparation.tent_iterate_dyadic
