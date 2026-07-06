/-
# O-min lane R4-D5a: the uniform frontier bound — CDT₂ opens.

The arc closes on itself: D0's `fiberFrontier A` (definable, with *automatically* finite
fibers — no hypothesis) is exactly what D4d's `uniform_finiteness` eats. The output is the
engine of classical cell decomposition for `ℝ²`:

- **`frontier_ncard_bound`** — for definable `A`, the fiber-frontier sizes
  `|∂(A_x)|` are uniformly bounded by some `N`, for *every* definable `A`, no fiber
  hypothesis at all.
- **`exists_isNth_of_mem` / `ranks_enumerate`** — over a finite fiber, every point is the
  rank-`j` point for `j` = its below-count, so membership is exactly "be one of the first
  `ncard` rank values": the D2 rank functions *enumerate* finite fibers.
- **`exactSet` + `frontier_partition` (the capstone)** — the line is covered by the tame
  exact-count classes `{x : |∂(A_x)| = k}`, `k ≤ N`, and over the `k`-class the `k`
  definable rank functions of `fiberFrontier A` enumerate every fiber frontier.

D5b next: the master refinement (rank continuity cut-sets + test-set frontiers in one
Finset), then D5c band triviality, then the packaged CDT₂ (D5d, owner-gated shape).
-/
import Sundogcert.OMinimalUniformFiniteness

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### The fiber identification and the uniform bound -/

/-- D0's fiber identification, standalone: the fiber of `fiberFrontier A` at `x` IS the
frontier of the fiber of `A` at `x`. -/
theorem fiberFrontier_fiber_eq (A : Set (Fin 2 → ℝ)) (x : ℝ) :
    {y : ℝ | pairFn x y ∈ fiberFrontier A} = frontier {y : ℝ | pairFn x y ∈ A} := by
  ext y
  simp [fiberFrontier]

/-- **The uniform frontier bound**: fiber frontiers of a definable set are uniformly
bounded — `uniform_finiteness` applied to `fiberFrontier`, with no fiber hypothesis. -/
theorem frontier_ncard_bound (hA : S.Definable A) :
    ∃ N : ℕ, ∀ x : ℝ, (frontier {y : ℝ | pairFn x y ∈ A}).ncard ≤ N := by
  obtain ⟨N, hN⟩ := uniform_finiteness (definable_fiberFrontier hA)
    (fiberFrontier_fiber_finite hA)
  refine ⟨N, fun x => ?_⟩
  rw [← fiberFrontier_fiber_eq]
  exact hN x

/-! ### Rank enumeration of finite fibers -/

/-- Every point of a finite fiber is the rank-`j` point for `j` = its below-count. -/
theorem exists_isNth_of_mem {x z : ℝ} (hfin : {y : ℝ | pairFn x y ∈ A}.Finite)
    (hz : pairFn x z ∈ A) :
    ∃ j : ℕ, IsNth A j x z ∧ j < {y : ℝ | pairFn x y ∈ A}.ncard := by
  classical
  have hBfin : ({y : ℝ | pairFn x y ∈ A} ∩ Set.Iio z).Finite := hfin.inter_of_left _
  refine ⟨({y : ℝ | pairFn x y ∈ A} ∩ Set.Iio z).ncard, ⟨hz, ?_, ?_⟩, ?_⟩
  · -- BelowCount at the below-set's cardinality
    refine belowCount_of_finset _ hBfin.toFinset ?_ ?_ z ?_
    · exact (Set.ncard_eq_toFinset_card _ hBfin).symm
    · intro y hy
      exact (hBfin.mem_toFinset.mp hy).1
    · intro y hy
      exact (hBfin.mem_toFinset.mp hy).2
  · -- no BelowCount at one more
    intro hbc
    obtain ⟨Y, hYcard, hY⟩ := belowCount_exists_finset hbc
    have hsub : Y ⊆ hBfin.toFinset :=
      fun y hy => hBfin.mem_toFinset.mpr ⟨(hY y hy).2, (hY y hy).1⟩
    have hle := Finset.card_le_card hsub
    rw [hYcard, ← Set.ncard_eq_toFinset_card _ hBfin] at hle
    omega
  · -- the below-count is strictly less than the fiber size
    have hzB : z ∉ {y : ℝ | pairFn x y ∈ A} ∩ Set.Iio z := fun h => lt_irrefl z h.2
    have hss : ({y : ℝ | pairFn x y ∈ A} ∩ Set.Iio z) ⊂ {y : ℝ | pairFn x y ∈ A} :=
      ⟨Set.inter_subset_left, fun hcontra => hzB (hcontra hz)⟩
    exact Set.ncard_lt_ncard hss hfin

/-- **Rank enumeration**: over a finite fiber, membership is exactly "be one of the first
`ncard` rank values". -/
theorem ranks_enumerate {x : ℝ} (hfin : {y : ℝ | pairFn x y ∈ A}.Finite) {z : ℝ} :
    pairFn x z ∈ A ↔
      ∃ j < {y : ℝ | pairFn x y ∈ A}.ncard, z = nthFn A j x := by
  constructor
  · intro hz
    obtain ⟨j, hjNth, hjlt⟩ := exists_isNth_of_mem hfin hz
    exact ⟨j, hjlt, (nthFn_eq hjNth).symm⟩
  · rintro ⟨j, hj, rfl⟩
    have hx : x ∈ countSet A (j + 1) := (mem_countSet_iff_le_ncard hfin).mpr hj
    obtain ⟨z', hz'⟩ := isNth_exists_of_mem_countSet hfin hx (Nat.lt_succ_self j)
    exact (nthFn_isNth ⟨z', hz'⟩).1

/-! ### The exact-count classes -/

/-- The exact-count base class: parameters whose fiber has at least `k` but not `k+1`
points — for finite fibers, exactly `k`. -/
def exactSet (A : Set (Fin 2 → ℝ)) (k : ℕ) : Set ℝ :=
  countSet A k \ countSet A (k + 1)

theorem tame_exactSet (hA : S.Definable A) (k : ℕ) : Tame (exactSet A k) := by
  rw [exactSet, Set.diff_eq]
  exact tame_inter (tame_countSet hA k) (tame_compl (tame_countSet hA (k + 1)))

theorem mem_exactSet_iff {x : ℝ} (hfin : {y : ℝ | pairFn x y ∈ A}.Finite) {k : ℕ} :
    x ∈ exactSet A k ↔ {y : ℝ | pairFn x y ∈ A}.ncard = k := by
  rw [exactSet, Set.mem_diff, mem_countSet_iff_le_ncard hfin,
    mem_countSet_iff_le_ncard hfin]
  omega

/-- The exact-count classes cover the line, boundedly. -/
theorem exactSet_partition (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    ∃ N : ℕ, ∀ x : ℝ, ∃ k ≤ N, x ∈ exactSet A k := by
  obtain ⟨N, hN⟩ := uniform_finiteness hA hfib
  exact ⟨N, fun x => ⟨_, hN x, (mem_exactSet_iff (hfib x)).mpr rfl⟩⟩

/-! ### The D5a capstone -/

/-- **The CDT₂ base partition.** For definable `A`: finitely many tame exact-frontier-count
classes cover the line, and over the `k`-class the `k` definable rank functions of
`fiberFrontier A` enumerate every fiber frontier. -/
theorem frontier_partition (hA : S.Definable A) :
    ∃ N : ℕ, (∀ x : ℝ, ∃ k ≤ N, x ∈ exactSet (fiberFrontier A) k) ∧
      ∀ k : ℕ, Tame (exactSet (fiberFrontier A) k) ∧
        ∀ x ∈ exactSet (fiberFrontier A) k, ∀ z : ℝ,
          z ∈ frontier {y : ℝ | pairFn x y ∈ A} ↔
            ∃ j < k, z = nthFn (fiberFrontier A) j x := by
  obtain ⟨N, hN⟩ := exactSet_partition (definable_fiberFrontier hA)
    (fiberFrontier_fiber_finite hA)
  refine ⟨N, hN, fun k => ⟨tame_exactSet (definable_fiberFrontier hA) k, ?_⟩⟩
  intro x hx z
  have hfin := fiberFrontier_fiber_finite hA x
  have hk : {y : ℝ | pairFn x y ∈ fiberFrontier A}.ncard = k :=
    (mem_exactSet_iff hfin).mp hx
  have hmem : z ∈ frontier {y : ℝ | pairFn x y ∈ A} ↔
      pairFn x z ∈ fiberFrontier A := by
    rw [← fiberFrontier_fiber_eq]
    exact Iff.rfl
  rw [hmem, ranks_enumerate hfin, hk]

end Sundog.OMinimalAbstract
