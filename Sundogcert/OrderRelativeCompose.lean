/-
# OrderRelative — the composition law (scalar order = join of the coordinate orders)

The mode-vectors showed the scalar order is a lossy summary of a latent vector. This makes the
summary precise on the cohomological axis: the additive (torsion) order of a PRODUCT class is the
**lcm** of the coordinate orders — which is the **join in the divisibility lattice**, not the ≤-max.

`compose_order_eq_lcm` proves the order of `(1,1) ∈ ZMod a × ZMod b` is `lcm a b`;
`compose_lcm_not_max` exhibits `a=4, b=6`, where the composite order is `12 = lcm` while the ≤-join
(`max`) is only `6` — so "scalar = join" holds, but with the *divisibility* lattice's join, strictly
above the naive max. The free case (`ℤ`) is the special case where the lcm absorbs `⊤`, which is why
the mode-vectors collapse to a resist pole.
-/
import Sundogcert.OrderRelativeCohomology

namespace Sundog.OrderRelative.Compose

open Sundog.OrderRelative Sundog.OrderRelative.Cohomology

/-- **The composition instance.** The product class `(1,1) ∈ ZMod a × ZMod b` resolves at budget `k`
iff `lcm a b ≤ k` — its scalar order is `lcm a b`, the join of the coordinate orders `a, b`. -/
def composeProblem (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : Problem where
  Target := Unit
  ord _ := (Nat.lcm a b : ℕ∞)
  Resolves k _ := AnnihilatedBy ((1, 1) : ZMod a × ZMod b) k
  resolves_iff k _ := by
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    constructor
    · rintro ⟨j, hj1, hjk, hj0⟩
      have hfst : (j : ZMod a) = 0 := by
        have h := congrArg Prod.fst hj0
        simpa [nsmul_eq_mul] using h
      have hsnd : (j : ZMod b) = 0 := by
        have h := congrArg Prod.snd hj0
        simpa [nsmul_eq_mul] using h
      rw [CharP.cast_eq_zero_iff (ZMod a) a] at hfst
      rw [CharP.cast_eq_zero_iff (ZMod b) b] at hsnd
      have hlcm : Nat.lcm a b ∣ j := Nat.lcm_dvd hfst hsnd
      exact_mod_cast le_trans (Nat.le_of_dvd (by omega) hlcm) hjk
    · intro hk
      have hk' : Nat.lcm a b ≤ k := by exact_mod_cast hk
      have hlcm1 : 1 ≤ Nat.lcm a b :=
        Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
      refine ⟨Nat.lcm a b, hlcm1, hk', ?_⟩
      have h1 : (Nat.lcm a b) • (1 : ZMod a) = 0 := by
        rw [nsmul_eq_mul, mul_one]
        exact (CharP.cast_eq_zero_iff (ZMod a) a _).mpr (Nat.dvd_lcm_left a b)
      have h2 : (Nat.lcm a b) • (1 : ZMod b) = 0 := by
        rw [nsmul_eq_mul, mul_one]
        exact (CharP.cast_eq_zero_iff (ZMod b) b _).mpr (Nat.dvd_lcm_right a b)
      rw [Prod.ext_iff]
      exact ⟨by simpa using h1, by simpa using h2⟩

/-- **The composition law.** The scalar order of the product is the lcm of the coordinate orders —
the join in the divisibility lattice. -/
theorem compose_order_eq_lcm (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (composeProblem a b ha hb).ord () = (Nat.lcm a b : ℕ∞) := rfl

/-- **The join is the divisibility lattice's, not the ≤-max.** For `a=4, b=6` the composite order
is `12 = lcm 4 6`, while the ≤-join (`max`) of the coordinate orders is only `6` — so the scalar
order is the *divisibility* join, strictly above the naive max. -/
theorem compose_lcm_not_max :
    (composeProblem 4 6 (by norm_num) (by norm_num)).ord () = (12 : ℕ∞)
      ∧ ((4 : ℕ∞) ⊔ (6 : ℕ∞)) = (6 : ℕ∞) := by
  refine ⟨?_, ?_⟩
  · simp only [compose_order_eq_lcm, show Nat.lcm 4 6 = 12 from by decide, Nat.cast_ofNat]
  · rw [sup_eq_right]; exact_mod_cast (by norm_num : (4 : ℕ) ≤ 6)

end Sundog.OrderRelative.Compose
