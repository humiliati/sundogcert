/-
# Graded cancellation: region count bounded by a cancellation budget (S3-2)

N-1 is a *dichotomy*: cancellation-free (`IsMono`) circuits are region-polynomial
(`isMono_hasPieceCover`, linear in leaves), while the cancellation-using tent reaches `2^d`
(`DepthSeparation`). S3-2 makes it a *dial*: the region count is bounded by `4 ^ g · leafCount`,
where `g` is a **cancellation budget** that is `0` exactly in the cancellation-free case (recovering
N-1) and grows by one per cancellation-exposed fold.

The operative budget is **`cancelMax`** — the number of `max` gates whose subtree contains a
negative scale. This is the honest measure: a negative scale only blows the region count up *through
a `max`* (a `max` of convex pieces stays convex and does not double — `hasPieceCover_max`; a `max`
of a non-monotone, hence non-convex, argument can double). A circuit with negative scales but no
folding `max` is still affine-piece-cheap, and `cancelMax` correctly reads `0` there.

* **`cancelMax_eq_zero_of_isMono`** — no cancellation ⇒ budget `0`.
* **`hasPieceCover_graded`** — `HasPieceCover (realize1 e) (4 ^ cancelMax e · leafCount e)`. At
  `cancelMax e = 0` this is `≤ leafCount e`, exactly N-1; each cancellation-exposed `max` pays a
  bounded factor. Cancellation is a graded resource, and the budget bounds the geometry.

The base is `4`, not `2`, because the `max`-of-non-convex bound is routed through the ReLU doubling
`max(f,g) = g + relu(f − g)` (`hasPieceCover_relu` from `ExactRepr`), which is a constant-factor
loose; a direct symmetric `2·(n+m)` `max` bound would give base `2`. The grading — polynomial at
budget `0`, exponential-in-budget otherwise — is unchanged.
-/
import Sundogcert.ExactRepr

namespace Sundog.GradedCancellation

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.RegionPoly
  Sundog.CancellationFree Sundog.ExactRepr

/-- `hasNeg e` is `true` iff the circuit `e` contains a negative scale somewhere. -/
noncomputable def hasNeg {n : ℕ} : Trop n → Bool
  | .var _ => false
  | .const _ => false
  | .add a b => hasNeg a || hasNeg b
  | .scale c a => decide (c < 0) || hasNeg a
  | .max a b => hasNeg a || hasNeg b

/-- **The cancellation budget.** The number of `max` gates whose subtree contains a negative scale
— the folds where cancellation can multiply the region count. -/
noncomputable def cancelMax {n : ℕ} : Trop n → ℕ
  | .var _ => 0
  | .const _ => 0
  | .add a b => cancelMax a + cancelMax b
  | .scale _ a => cancelMax a
  | .max a b => cancelMax a + cancelMax b + (if hasNeg a || hasNeg b then 1 else 0)

/-- Cancellation-free is exactly "no negative scale". -/
theorem isMono_iff_hasNeg {n : ℕ} (e : Trop n) : IsMono e ↔ hasNeg e = false := by
  induction e with
  | var i => simp [IsMono, hasNeg]
  | const c => simp [IsMono, hasNeg]
  | add a b iha ihb => simp [IsMono, hasNeg, Bool.or_eq_false_iff, iha, ihb]
  | scale c a ih => simp [IsMono, hasNeg, Bool.or_eq_false_iff, ih, decide_eq_false_iff_not, not_lt]
  | max a b iha ihb => simp [IsMono, hasNeg, Bool.or_eq_false_iff, iha, ihb]

/-- A cancellation-free circuit spends no budget. -/
theorem cancelMax_eq_zero_of_isMono {n : ℕ} (e : Trop n) : IsMono e → cancelMax e = 0 := by
  induction e with
  | var i => intro _; rfl
  | const c => intro _; rfl
  | add a b iha ihb => intro h; simp [cancelMax, iha h.1, ihb h.2]
  | scale c a ih => intro h; simp [cancelMax, ih h.2]
  | max a b iha ihb =>
    intro h
    have hne : (hasNeg a || hasNeg b) = false := by
      rw [Bool.or_eq_false_iff]
      exact ⟨(isMono_iff_hasNeg a).mp h.1, (isMono_iff_hasNeg b).mp h.2⟩
    simp [cancelMax, iha h.1, ihb h.2, hne]

/-- **Graded cancellation bound (S3-2).** Every circuit's 1-D realization has a piece cover of size
`4 ^ cancelMax e · leafCount e`. At zero cancellation budget this is `leafCount e` (N-1); each
cancellation-exposed `max` costs a bounded factor. The dichotomy becomes a dial. -/
theorem hasPieceCover_graded (e : Trop 1) :
    HasPieceCover (realize1 e) (4 ^ cancelMax e * leafCount e) := by
  classical
  induction e with
  | var i =>
    rw [realize1_var]; simp only [cancelMax, leafCount, pow_zero, one_mul]; exact hasPieceCover_id
  | const c =>
    rw [realize1_const]; simp only [cancelMax, leafCount, pow_zero, one_mul]
    exact hasPieceCover_const c
  | add a b iha ihb =>
    rw [realize1_add]
    refine hasPieceCover_mono_le (hasPieceCover_add iha ihb) ?_
    have hA : 1 ≤ 4 ^ cancelMax a := Nat.one_le_pow _ _ (by norm_num)
    have hB : 1 ≤ 4 ^ cancelMax b := Nat.one_le_pow _ _ (by norm_num)
    simp only [cancelMax, leafCount, pow_add]
    calc 4 ^ cancelMax a * leafCount a + 4 ^ cancelMax b * leafCount b
        ≤ 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount a
          + 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount b :=
          Nat.add_le_add
            (mul_le_mul_right' (le_mul_of_one_le_right (Nat.zero_le _) hB) (leafCount a))
            (mul_le_mul_right' (le_mul_of_one_le_left (Nat.zero_le _) hA) (leafCount b))
      _ = 4 ^ cancelMax a * 4 ^ cancelMax b * (leafCount a + leafCount b) := by ring
  | scale c a ih =>
    rw [realize1_scale]
    simpa only [cancelMax] using hasPieceCover_smul c ih
  | max a b iha ihb =>
    by_cases hm : IsMono (Trop.max a b)
    · rw [cancelMax_eq_zero_of_isMono _ hm]
      simpa using isMono_hasPieceCover hm
    · have htrue : (hasNeg a || hasNeg b) = true := by
        by_contra hc
        rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hc
        exact hm ⟨(isMono_iff_hasNeg a).mpr hc.1, (isMono_iff_hasNeg b).mpr hc.2⟩
      have hcm : cancelMax (Trop.max a b) = cancelMax a + cancelMax b + 1 := by
        simp only [cancelMax, htrue, if_true]
      rw [hcm, realize1_max]
      have key : (fun x => max (realize1 a x) (realize1 b x))
          = (fun x => realize1 b x + max (realize1 a x + (-1) * realize1 b x) 0) := by
        funext x
        rcases le_total (realize1 a x) (realize1 b x) with h | h
        · rw [max_eq_right h, max_eq_right (by linarith), add_zero]
        · rw [max_eq_left h, max_eq_left (by linarith)]; ring
      rw [key]
      refine hasPieceCover_mono_le
        (hasPieceCover_add ihb (hasPieceCover_relu (hasPieceCover_add iha
          (hasPieceCover_smul (-1) ihb)))) ?_
      have hA : 1 ≤ 4 ^ cancelMax a := Nat.one_le_pow _ _ (by norm_num)
      have hB : 1 ≤ 4 ^ cancelMax b := Nat.one_le_pow _ _ (by norm_num)
      have hpow : 4 ^ (cancelMax a + cancelMax b + 1)
          = 4 * 4 ^ cancelMax a * 4 ^ cancelMax b := by rw [pow_succ, pow_add]; ring
      have hlc : leafCount (Trop.max a b) = leafCount a + leafCount b := rfl
      rw [hpow, hlc]
      have t1 : 2 * (4 ^ cancelMax a * leafCount a)
          ≤ 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount a := by
        have h2 : (2 : ℕ) ≤ 4 * 4 ^ cancelMax b :=
          le_trans (by norm_num) (le_mul_of_one_le_right (by norm_num) hB)
        calc 2 * (4 ^ cancelMax a * leafCount a)
            ≤ (4 * 4 ^ cancelMax b) * (4 ^ cancelMax a * leafCount a) := mul_le_mul_right' h2 _
          _ = 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount a := by ring
      have t2 : 3 * (4 ^ cancelMax b * leafCount b)
          ≤ 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount b := by
        have h3 : (3 : ℕ) ≤ 4 * 4 ^ cancelMax a :=
          le_trans (by norm_num) (le_mul_of_one_le_right (by norm_num) hA)
        calc 3 * (4 ^ cancelMax b * leafCount b)
            ≤ (4 * 4 ^ cancelMax a) * (4 ^ cancelMax b * leafCount b) := mul_le_mul_right' h3 _
          _ = 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount b := by ring
      calc 4 ^ cancelMax b * leafCount b
            + 2 * (4 ^ cancelMax a * leafCount a + 4 ^ cancelMax b * leafCount b)
          = 2 * (4 ^ cancelMax a * leafCount a) + 3 * (4 ^ cancelMax b * leafCount b) := by ring
        _ ≤ 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount a
            + 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * leafCount b := Nat.add_le_add t1 t2
        _ = 4 * 4 ^ cancelMax a * 4 ^ cancelMax b * (leafCount a + leafCount b) := by ring

end Sundog.GradedCancellation
