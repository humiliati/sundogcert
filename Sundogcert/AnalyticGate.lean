/-
# An analytic gate at ε > 0: x² is ReLU-approximable with a machine-checked error bound (S3-4)

Slate-3 hook **S3-4**. The lane's exact (ε = 0) core (`CircuitNet`, `ExactRepr`) stops at the
piecewise-linear fragment. The paper's headline (arXiv:2606.26705 Cor 5.1) is about *analytic*
gates approximated to error ε. This module lands the lane's **first ε > 0 result**: the canonical
analytic gate `x²` (the Yarotsky/Telgarsky building block, not piecewise-linear) is approximated on
`[0,1]` by an explicit finite ReLU net to any error ε, with the L∞ bound **machine-checked**.

The construction reuses S3-1: the uniform-breakpoint chordal interpolant of `x²` is the upper
envelope of its secant lines (`x²` is convex), i.e. a tropical `max`-circuit (`linesTrop`), which
compiles to a ReLU net (`compile`). The new content is the error bound, which is *elementary* for
`x²` because the secant error has a closed form:

    secant_{a,b}(x) − x² = (x − a)(b − x),

so `0 ≤ secant(x) − x²` on `[a,b]` and `secant(x) − x² ≤ ((b−a)/2)²` everywhere (a one-line
`sq_nonneg`). With `n` uniform pieces the gap is `1/(4n²)`, giving `‖x² − net‖_∞ ≤ ε` on `[0,1]`.

**Honest rate boundary.** This is the *elementary* `O(1/√ε)`-piece (polynomial) rate. The paper's
*polylog* rate is the self-composition / sawtooth construction (Telgarsky), which is **not** done
here — the named falsifier `RATE_NOT_POLYLOG` stands at exactly that gap. So this is S3-4's first
strike: the ε > 0 milestone (an analytic gate IS a ReLU net to any ε, proved), at the poly rate.
-/
import Sundogcert.ExactRepr

namespace Sundog.AnalyticGate

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.ExactRepr

/-! ### The secant kernel (elementary geometry of `x²`) -/

/-- The secant line of `x²` on `[a,b]`, as a `(slope, intercept)` pair: slope `a+b`, intercept
`-(a·b)`. -/
def sline (a b : ℝ) : ℝ × ℝ := (a + b, -(a * b))

/-- **The closed-form secant error of `x²`.** -/
theorem sline_sub_sq (a b x : ℝ) :
    (sline a b).1 * x + (sline a b).2 - x ^ 2 = (x - a) * (b - x) := by
  simp only [sline]; ring

/-- The secant overshoots `x²` by at most `((b−a)/2)²`, everywhere. -/
theorem sline_le (a b x : ℝ) :
    (sline a b).1 * x + (sline a b).2 ≤ x ^ 2 + ((b - a) / 2) ^ 2 := by
  nlinarith [sline_sub_sq a b x, sq_nonneg (x - (a + b) / 2)]

/-- On its own interval `[a,b]`, the secant is `≥ x²`. -/
theorem le_sline (a b x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    x ^ 2 ≤ (sline a b).1 * x + (sline a b).2 := by
  nlinarith [sline_sub_sq a b x, mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-! ### Max-of-lines helpers (reusing the `ExactRepr` fold machinery) -/

/-- An upper bound on every line in `L` lifts to an upper bound on `linesTrop L`. -/
theorem linesTrop_le {L : List (ℝ × ℝ)} {x c : ℝ} (hL : L ≠ [])
    (h : ∀ q ∈ L, q.1 * x + q.2 ≤ c) : realize1 (linesTrop L) x ≤ c := by
  obtain ⟨pr, rest, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp only [linesTrop]
  rw [realize1_foldl, affineCirc_realize]
  exact foldlMax_le (fun q => q.1 * x + q.2) rest (pr.1 * x + pr.2) c
    (h pr List.mem_cons_self) (fun a ha => h a (List.mem_cons_of_mem pr ha))

/-- Any single line of `L` is `≤ linesTrop L`. -/
theorem le_linesTrop {L : List (ℝ × ℝ)} {x : ℝ} {q₀ : ℝ × ℝ} (hq : q₀ ∈ L) :
    q₀.1 * x + q₀.2 ≤ realize1 (linesTrop L) x := by
  obtain ⟨pr, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hq)
  simp only [linesTrop]
  rw [realize1_foldl, affineCirc_realize]
  rcases List.mem_cons.mp hq with rfl | hmem
  · exact le_foldlMax_base (fun q => q.1 * x + q.2) rest _
  · exact le_foldlMax_mem (fun q => q.1 * x + q.2) rest (pr.1 * x + pr.2) hmem

/-! ### The approximating net -/

/-- The list of `n` secant lines of `x²` on the uniform grid of `[0,1]`. -/
noncomputable def secantList (n : ℕ) : List (ℝ × ℝ) :=
  (List.range n).map (fun i : ℕ => sline ((i : ℝ) / n) (((i : ℝ) + 1) / n))

/-- The ReLU net: the chordal interpolant of `x²` (upper envelope of its secants), compiled. -/
noncomputable def sqNet (n : ℕ) : Net 1 := compile (linesTrop (secantList n))

theorem secantList_ne_nil {n : ℕ} (hn : 0 < n) : secantList n ≠ [] := by
  have hlen : (secantList n).length = n := by simp [secantList]
  intro h; rw [h, List.length_nil] at hlen; omega

theorem realize1N_sqNet (n : ℕ) (x : ℝ) :
    realize1N (sqNet n) x = realize1 (linesTrop (secantList n)) x := by
  rw [sqNet, realize1_compile]

/-- **Upper error bound.** The net overshoots `x²` by at most `1/(4n²)`, everywhere. -/
theorem sqNet_le (n : ℕ) (hn : 0 < n) (x : ℝ) :
    realize1N (sqNet n) x ≤ x ^ 2 + 1 / (4 * n ^ 2) := by
  rw [realize1N_sqNet]
  refine linesTrop_le (secantList_ne_nil hn) (fun q hq => ?_)
  simp only [secantList, List.mem_map] at hq
  obtain ⟨i, _, rfl⟩ := hq
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgap : (((((i : ℝ) + 1) / n) - (i : ℝ) / n) / 2) ^ 2 = 1 / (4 * n ^ 2) := by
    field_simp; ring
  calc (sline ((i : ℝ) / n) (((i : ℝ) + 1) / n)).1 * x
          + (sline ((i : ℝ) / n) (((i : ℝ) + 1) / n)).2
        ≤ x ^ 2 + (((((i : ℝ) + 1) / n) - (i : ℝ) / n) / 2) ^ 2 := sline_le _ _ x
    _ = x ^ 2 + 1 / (4 * n ^ 2) := by rw [hgap]

/-- **Lower error bound.** On `[0,1]` the net is `≥ x²` (it is the chordal interpolant of a convex
function). -/
theorem le_sqNet (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ^ 2 ≤ realize1N (sqNet n) x := by
  rw [realize1N_sqNet]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set i : ℕ := min (Nat.floor ((n : ℝ) * x)) (n - 1) with hi
  have hi_lt : i < n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)
  have hmem : sline ((i : ℝ) / n) (((i : ℝ) + 1) / n) ∈ secantList n := by
    unfold secantList
    exact List.mem_map_of_mem (f := fun j : ℕ => sline ((j : ℝ) / n) (((j : ℝ) + 1) / n))
      (List.mem_range.mpr hi_lt)
  have hax : (i : ℝ) / n ≤ x := by
    rw [div_le_iff₀ hn']
    have hi_le : (i : ℝ) ≤ (Nat.floor ((n : ℝ) * x) : ℝ) := by
      have : i ≤ Nat.floor ((n : ℝ) * x) := by rw [hi]; omega
      exact_mod_cast this
    have hfl : (Nat.floor ((n : ℝ) * x) : ℝ) ≤ (n : ℝ) * x :=
      Nat.floor_le (mul_nonneg hn'.le hx.1)
    linarith [hi_le, hfl]
  have hxb : x ≤ ((i : ℝ) + 1) / n := by
    rw [le_div_iff₀ hn']
    by_cases hle : Nat.floor ((n : ℝ) * x) ≤ n - 1
    · have hieq : i = Nat.floor ((n : ℝ) * x) := by rw [hi]; exact min_eq_left hle
      have hflo : (n : ℝ) * x < (Nat.floor ((n : ℝ) * x) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hieq, mul_comm]; linarith [hflo]
    · have hieq : i = n - 1 := by rw [hi]; exact min_eq_right (by omega)
      have hcast : ((i : ℝ) + 1) = n := by
        rw [hieq, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]; ring
      rw [hcast]
      have h := mul_le_mul_of_nonneg_right hx.2 hn'.le
      rwa [one_mul] at h
  calc x ^ 2 ≤ (sline ((i : ℝ) / n) (((i : ℝ) + 1) / n)).1 * x
          + (sline ((i : ℝ) / n) (((i : ℝ) + 1) / n)).2 := le_sline _ _ x hax hxb
    _ ≤ realize1 (linesTrop (secantList n)) x := le_linesTrop hmem

/-- **The analytic-gate approximation theorem (S3-4).** On `[0,1]`, the explicit ReLU net `sqNet n`
approximates `x²` with L∞ error at most `1/(4n²)` — a machine-checked error bound for an analytic
(non-PL) gate. -/
theorem sqNet_approx (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |x ^ 2 - realize1N (sqNet n) x| ≤ 1 / (4 * n ^ 2) := by
  have hlo := le_sqNet n hn x hx
  have hhi := sqNet_le n hn x
  have hpos : (0 : ℝ) ≤ 1 / (4 * n ^ 2) := by positivity
  rw [abs_le]
  exact ⟨by linarith [hhi], by linarith [hlo]⟩

/-- **ε-approximation corollary.** For every `ε > 0` there is a finite ReLU net approximating `x²`
to L∞ error `≤ ε` on `[0,1]`. The lane's first ε > 0 analytic-gate result. -/
theorem sq_eps_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Net 1, ∀ x ∈ Set.Icc (0 : ℝ) 1, |x ^ 2 - realize1N g x| ≤ ε := by
  obtain ⟨m, hm⟩ := exists_nat_ge (1 / ε)
  set n : ℕ := m + 1 with hn_def
  have hn : 0 < n := Nat.succ_pos m
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨sqNet n, fun x hx => le_trans (sqNet_approx n hn x hx) ?_⟩
  rw [div_le_iff₀ (mul_pos (by norm_num) (pow_pos hn' 2))]
  have hmn : (m : ℝ) ≤ n := by rw [hn_def]; push_cast; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1e : 1 / ε ≤ 4 * (n : ℝ) ^ 2 := by nlinarith [hm, hmn, hn1]
  calc (1 : ℝ) = ε * (1 / ε) := by field_simp
    _ ≤ ε * (4 * (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left h1e (le_of_lt hε)

end Sundog.AnalyticGate
