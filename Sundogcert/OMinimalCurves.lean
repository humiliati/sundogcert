/-
# O-min lane R4-D3: the k-curve extraction.

**`exists_k_ordered_curves`** — definable `A` with all fibers finite and unbounded fiber
sizes: for every `k` there is one interval on which the `k` rank functions
`nthFn A 0, …, nthFn A (k-1)` are simultaneously

- **genuine** (exact rank `IsNth` holds — in particular every graph point lies in `A`),
- **continuous** (the continuous Monotonicity Theorem, applied to each rank function via
  D2's `definableFun_nthFn`, with the `k` finite cut-sets dodged at once), and
- **strictly ordered** (`isNth_lt`: of two rank points, the lower rank sits strictly below —
  so the `k` curves are pairwise disjoint).

The interval comes from D2's dichotomy (`exists_interval_in_countSet`); the common
cut-set-free window comes from a `Finset.induction` shrink (`avoid_finset`): a finite set
cannot block every subinterval.

**Honest fence.** D3 only: the curves exist per `k`; the contradiction from "arbitrarily
many disjoint curves" is D4 — the wall.
-/
import Sundogcert.OMinimalPointFns

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### Below-count monotonicity and the rank ordering -/

theorem belowCount_mono {x t : ℝ} : ∀ {k : ℕ},
    BelowCount A x t (k + 1) → BelowCount A x t k
  | 0, _ => trivial
  | _ + 1, ⟨y, h1, h2, h3⟩ => ⟨y, h1, h2, belowCount_mono h3⟩

theorem belowCount_mono_le {x t : ℝ} {k k' : ℕ} (h : k ≤ k') :
    BelowCount A x t k' → BelowCount A x t k := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun h' => ih (belowCount_mono h')

/-- **Ranks are ordered**: the rank-`j` point sits strictly below the rank-`j'` point for
`j < j'` — equality or inversion both manufacture an illegal below-witness. -/
theorem isNth_lt {x z z' : ℝ} {j j' : ℕ} (hjj : j < j')
    (h : IsNth A j x z) (h' : IsNth A j' x z') : z < z' := by
  rcases lt_trichotomy z z' with hlt | heq | hgt
  · exact hlt
  · exfalso
    subst heq
    exact h.2.2 (belowCount_mono_le hjj h'.2.1)
  · exfalso
    exact h.2.2 (belowCount_mono_le (k' := j' + 1) (by omega)
      ⟨z', hgt, h'.1, h'.2.1⟩)

/-- On a counting set, every rank below `k` is realized. -/
theorem isNth_exists_of_mem_countSet {x : ℝ} {k : ℕ}
    (hfin : {y : ℝ | pairFn x y ∈ A}.Finite)
    (hx : x ∈ countSet A k) {j : ℕ} (hj : j < k) : ∃ z, IsNth A j x z := by
  obtain ⟨t, hAC⟩ := hx
  obtain ⟨Y, hcard, hY⟩ := aboveCount_exists_finset hAC
  obtain ⟨Y', hY'sub, hY'card⟩ :=
    Finset.exists_subset_card_eq (s := Y) (n := j + 1) (by omega)
  exact isNth_exists hfin j Y' hY'card (fun y hy => (hY y (hY'sub hy)).2)

/-! ### The finite-avoidance window -/

/-- A finite set cannot block every subinterval: shrink past it, one point at a time. -/
private theorem avoid_finset (G : Finset ℝ) : ∀ a₀ b₀ : ℝ, a₀ < b₀ →
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ Set.Ioo a₀ b₀ ∧ ∀ y ∈ G, y ∉ Set.Ioo a b := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    intro a₀ b₀ h
    exact ⟨a₀, b₀, h, subset_rfl, by simp⟩
  | @insert y s _ ih =>
    intro a₀ b₀ h
    obtain ⟨a, b, hab, hsub, havoid⟩ := ih a₀ b₀ h
    by_cases hyin : y ∈ Set.Ioo a b
    · refine ⟨a, y, hyin.1, fun z hz => hsub ⟨hz.1, lt_trans hz.2 hyin.2⟩, ?_⟩
      intro w hw hwin
      rcases Finset.mem_insert.mp hw with rfl | hwG
      · exact lt_irrefl w hwin.2
      · exact havoid w hwG ⟨hwin.1, lt_trans hwin.2 hyin.2⟩
    · refine ⟨a, b, hab, hsub, ?_⟩
      intro w hw hwin
      rcases Finset.mem_insert.mp hw with rfl | hwG
      · exact hyin hwin
      · exact havoid w hwG hwin

/-! ### The extraction -/

/-- **The k-curve extraction (D3).** Definable `A`, all fibers finite, all counting sets
nonempty: for every `k` there is an interval on which the `k` rank functions are genuine
(exact rank, graphs in `A`), continuous, and strictly ordered — `k` pairwise disjoint
ordered continuous definable curves over one base interval. -/
theorem exists_k_ordered_curves (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite)
    (hne : ∀ k : ℕ, (countSet A k).Nonempty) (k : ℕ) :
    ∃ a b : ℝ, a < b ∧
      (∀ j, j < k → ∀ x ∈ Set.Ioo a b, IsNth A j x (nthFn A j x)) ∧
      (∀ j, j < k → ContinuousOn (nthFn A j) (Set.Ioo a b)) ∧
      (∀ j j', j < j' → j' < k →
        ∀ x ∈ Set.Ioo a b, nthFn A j x < nthFn A j' x) := by
  classical
  obtain ⟨a₀, b₀, hab₀, hsub₀⟩ := exists_interval_in_countSet hA hfib hne k
  have H := fun j : ℕ => monotonicity_theorem_continuous (definableFun_nthFn hA j)
  choose F hF using H
  obtain ⟨a, b, hab, hsub, havoid⟩ := avoid_finset ((Finset.range k).biUnion F) a₀ b₀ hab₀
  have hranks : ∀ j, j < k → ∀ x ∈ Set.Ioo a b, IsNth A j x (nthFn A j x) := by
    intro j hj x hx
    exact nthFn_isNth (isNth_exists_of_mem_countSet (hfib x) (hsub₀ (hsub hx)) hj)
  refine ⟨a, b, hab, hranks, ?_, ?_⟩
  · intro j hj
    exact (hF j a b hab (fun s hs =>
      havoid s (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hs⟩))).2
  · intro j j' hjj hj' x hx
    exact isNth_lt hjj (hranks j (by omega) x hx) (hranks j' hj' x hx)

end Sundog.OMinimalAbstract
