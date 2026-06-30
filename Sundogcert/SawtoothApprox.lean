/-
# The polylog rate: x² via the Telgarsky sawtooth, at logarithmic depth (S3-4, hard step)

S3-4's first strike (`AnalyticGate`) approximated `x²` at the elementary **polynomial** rate
(`O(1/√ε)` pieces, an explicit `n`-piece interpolant). The paper's headline is the **polylog**
rate. This module lands it, via the Yarotsky/Telgarsky sawtooth.

The construction reuses the lane's depth-separation tent `T(x) = 1 − |2x − 1|` (`DepthSeparation`).
Define the self-similar approximant
  `R 0 x = x`,  `R (m+1) x = x − T x / 2 + R m (T x) / 4`.
The whole error analysis collapses to **one self-similar recursion**: with `e_m = x² − R m`,

  `e_{m+1}(x) = e_m(T x) / 4`,

which follows from the **tent identity** `(T x − 1)² = (2x − 1)²` (here trivial, since
`T x − 1 = −|2x − 1|`). Since `T` maps `[0,1] → [0,1]` and `|e_0| ≤ 1/4`, induction gives

  `|x² − R m x| ≤ 1 / (4 · 4^m)`   on `[0,1]`  —  **error decaying geometrically in `m`**.

And `R m` is built by `m`-fold composition with `T` (`subst0`), so it is a circuit of depth **linear
in `m`** (`Rcirc_depth`), compiling to a ReLU net of depth `O(m)` (`compile_depth_le`). Geometric
accuracy `4^{−m}` at linear depth `m` is exactly the polylog rate: to reach error `ε` needs depth
`O(log 1/ε)` — exponentially fewer gates than the first-strike `O(1/√ε)`-piece interpolant. The
sawtooth is the depth-separation tent (exponential pieces from linear depth) put to constructive
use.
-/
import Sundogcert.DepthSeparation
import Sundogcert.RegionCount

namespace Sundog.SawtoothApprox

open Sundog.CircuitNet Sundog.DepthSeparation Sundog.RegionCount

/-! ### The tent, value level -/

/-- **The tent identity** — the one fact the whole error analysis rests on. -/
theorem T_sub_one_sq (x : ℝ) : (T x - 1) ^ 2 = (2 * x - 1) ^ 2 := by
  have h : T x - 1 = -|2 * x - 1| := by simp only [T]; ring
  rw [h, neg_pow, sq_abs]; ring

/-- The tent maps `[0,1]` into `[0,1]`. -/
theorem T_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : T x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hx
  have habs : |2 * x - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  simp only [T, Set.mem_Icc]
  constructor <;> [linarith [habs]; linarith [abs_nonneg (2 * x - 1)]]

/-! ### The self-similar approximant and its error bound -/

/-- `R 0 x = x`; `R (m+1) x = x − T x / 2 + R m (T x) / 4`. The Yarotsky self-similar form. -/
noncomputable def R : ℕ → ℝ → ℝ
  | 0, x => x
  | (m + 1), x => x - T x / 2 + R m (T x) / 4

/-- **The error bound (the polylog accuracy).** `|x² − R m x| ≤ 1/(4·4^m)` on `[0,1]`, by the
self-similar recursion `e_{m+1}(x) = e_m(T x)/4`. -/
theorem sq_sub_R_le (m : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ 2 - R m x| ≤ 1 / (4 * 4 ^ m) := by
  induction m generalizing x with
  | zero =>
    simp only [R, pow_zero, mul_one]
    obtain ⟨h0, h1⟩ := hx
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - 1 / 2)]
  | succ m ih =>
    have hstep : x ^ 2 - R (m + 1) x = ((T x) ^ 2 - R m (T x)) / 4 := by
      simp only [R]; linear_combination (-1 / 4 : ℝ) * T_sub_one_sq x
    have hbound := ih (T x) (T_mem hx)
    have key : |x ^ 2 - R (m + 1) x| = |(T x) ^ 2 - R m (T x)| / 4 := by
      rw [hstep, abs_div]; norm_num
    rw [key, pow_succ]
    calc |(T x) ^ 2 - R m (T x)| / 4 ≤ (1 / (4 * 4 ^ m)) / 4 := by gcongr
      _ = 1 / (4 * (4 ^ m * 4)) := by ring

/-! ### The approximant as a circuit, with linear depth -/

/-- The circuit for `R m`: `R 0 = x`, `R (m+1) = (x − T·x/2) + (1/4)·(R m ∘ T)`, the composition
realized by `subst0` (substituting the tent into the running circuit). -/
noncomputable def Rcirc : ℕ → Trop 1
  | 0 => .var 0
  | (m + 1) =>
    .add (.add (.var 0) (.scale (-(1 / 2)) tent)) (.scale (1 / 4) (subst0 (Rcirc m) tent))

/-- `Rcirc m` computes `R m`. -/
theorem Rcirc_eval (m : ℕ) (x : Fin 1 → ℝ) : (Rcirc m).eval x = R m (x 0) := by
  induction m generalizing x with
  | zero => simp [Rcirc, R, Trop.eval_var]
  | succ m ih =>
    have hsub : (subst0 (Rcirc m) tent).eval x = R m (T (x 0)) := by
      rw [subst0_eval, ih, tent_eval]
    simp only [Rcirc, Trop.eval_add, Trop.eval_scale, Trop.eval_var, tent_eval, hsub, R]
    ring

theorem realize1_Rcirc (m : ℕ) (x : ℝ) : realize1 (Rcirc m) x = R m x :=
  Rcirc_eval m (fun _ => x)

/-- **Linear depth.** `Rcirc m` has depth at most `m · (2·tent.depth + 4)`. -/
theorem Rcirc_depth (m : ℕ) : (Rcirc m).depth ≤ m * (2 * tent.depth + 4) := by
  induction m with
  | zero => simp [Rcirc, Trop.depth]
  | succ m ih =>
    have hsub := subst0_depth_le (Rcirc m) tent
    have hstep : (Rcirc (m + 1)).depth ≤ (Rcirc m).depth + (2 * tent.depth + 4) := by
      simp only [Rcirc, Trop.depth, Nat.max_def]; split_ifs <;> omega
    calc (Rcirc (m + 1)).depth
          ≤ (Rcirc m).depth + (2 * tent.depth + 4) := hstep
      _ ≤ m * (2 * tent.depth + 4) + (2 * tent.depth + 4) := Nat.add_le_add_right ih _
      _ = (m + 1) * (2 * tent.depth + 4) := by ring

/-! ### The ReLU net and the polylog statement -/

/-- The ReLU net approximating `x²`: the sawtooth circuit, compiled. -/
noncomputable def sqNet (m : ℕ) : Net 1 := compile (Rcirc m)

/-- **Error of the net.** `|x² − net| ≤ 1/(4·4^m)` on `[0,1]` — geometric decay in `m`. -/
theorem sqNet_approx (m : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ 2 - realize1N (sqNet m) x| ≤ 1 / (4 * 4 ^ m) := by
  have h : realize1N (sqNet m) x = R m x := by
    rw [sqNet, realize1_compile, realize1_Rcirc]
  rw [h]; exact sq_sub_R_le m x hx

/-- **Depth of the net.** `O(m)` — linear in the number of folds. -/
theorem sqNet_depth (m : ℕ) : (sqNet m).depth ≤ 4 * (m * (2 * tent.depth + 4)) := by
  calc (sqNet m).depth ≤ 4 * (Rcirc m).depth := compile_depth_le (Rcirc m)
    _ ≤ 4 * (m * (2 * tent.depth + 4)) := by
        apply Nat.mul_le_mul_left; exact Rcirc_depth m

/-- **The polylog rate (S3-4, hard step).** For every `ε > 0` there is a ReLU net approximating
`x²` on `[0,1]` to error `≤ ε`, of depth `O(m)` where `1/(4·4^m) ≤ ε` — i.e. depth `O(log 1/ε)`.
Geometric accuracy `4^{−m}` at linear depth `m`: the polylog rate, exponentially better than the
first-strike `O(1/√ε)`-piece interpolant. -/
theorem sq_polylog_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Net 1),
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |x ^ 2 - realize1N g x| ≤ ε) ∧
      (g.depth ≤ 4 * (m * (2 * tent.depth + 4))) ∧
      (1 : ℝ) / (4 * 4 ^ m) ≤ ε := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (4 * ε)) (by norm_num : (1 : ℝ) < 4)
  refine ⟨m, sqNet m, fun x hx => le_trans (sqNet_approx m x hx) ?_, sqNet_depth m, ?_⟩
  · -- 1/(4·4^m) ≤ ε
    rw [div_le_iff₀ (by positivity)]
    have h4ε : (0 : ℝ) < 4 * ε := by positivity
    have : 1 / (4 * ε) < 4 ^ m := hm
    rw [div_lt_iff₀ h4ε] at this
    nlinarith [this]
  · rw [div_le_iff₀ (by positivity)]
    have h4ε : (0 : ℝ) < 4 * ε := by positivity
    have : 1 / (4 * ε) < 4 ^ m := hm
    rw [div_lt_iff₀ h4ε] at this
    nlinarith [this]

end Sundog.SawtoothApprox
