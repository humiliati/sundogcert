/-
# O-min lane R4-D5b: the master refinement — one cut set trivializes everything.

**`master_refinement`**: for definable `A`, there is a bound `N` and ONE finite cut set `C`
such that on every interval avoiding `C`:

- the interval lies in a single exact-frontier-count class (`exactSet (fiberFrontier A) k`,
  `k ≤ N`),
- all `N` rank functions of `fiberFrontier A` are continuous,
- and every structural test is constant: graph membership (`(x, rank_j x) ∈ A`?), band
  interiors (`bandIn` between consecutive ranks — both polarities via `Aᶜ`), the two ray
  tests below rank 0 and above rank `j`, and the full-fiber test (for the frontier-free
  class).

`C` bundles: the Monotonicity cut-sets of the `N` rank functions, and the (finite, by
tameness) frontiers of every class and test set. Constancy is `preconnected_split` on a
frontier-free interval — pure topology once the frontiers are inside `C`.

The polarity trick: `bandOut A = bandIn Aᶜ` etc., so each test needs ONE tame lemma,
instantiated at `A` and at `Aᶜ` (`S.definable_compl`).

D5c consumes this wholesale: per-fiber band dichotomy + these constancies =
`A ∩ (I × ℝ)` is a union of rank graphs and open bands.
-/
import Sundogcert.OMinimalFrontierBound

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalNormalForm Sundog.OMinimalAbstract.Fml

variable {S : OMinStructure} {A B : Set (Fin 2 → ℝ)}

/-! ### The test sets -/

/-- The band-interior test: every height strictly between `φ x` and `ψ x` lies in `B`. -/
def bandIn (B : Set (Fin 2 → ℝ)) (φ ψ : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | ∀ y : ℝ, (φ x < y ∧ y < ψ x) → pairFn x y ∈ B}

/-- The lower-ray test: every height strictly below `φ x` lies in `B`. -/
def rayLowIn (B : Set (Fin 2 → ℝ)) (φ : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | ∀ y : ℝ, y < φ x → pairFn x y ∈ B}

/-- The upper-ray test: every height strictly above `φ x` lies in `B`. -/
def rayHighIn (B : Set (Fin 2 → ℝ)) (φ : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | ∀ y : ℝ, φ x < y → pairFn x y ∈ B}

/-- The full-fiber test: every height lies in `B`. -/
def allIn (B : Set (Fin 2 → ℝ)) : Set ℝ :=
  {x : ℝ | ∀ y : ℝ, pairFn x y ∈ B}

/-- The graph test: the `φ`-graph point lies in `B`. -/
def graphIn (B : Set (Fin 2 → ℝ)) (φ : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | pairFn x (φ x) ∈ B}

/-! ### Local formula helpers -/

private theorem rcompPair {n : ℕ} (h : Fin n → ℝ) (i j : Fin n) :
    h ∘ ![i, j] = pairFn (h i) (h j) := by
  funext k
  fin_cases k <;> simp [pairFn, Function.comp]

private theorem rsnocPair (g : Fin 1 → ℝ) (t : ℝ) :
    (Fin.snoc g t : Fin 2 → ℝ) = pairFn (g 0) t := by
  funext k
  fin_cases k <;> simp [pairFn, Fin.snoc]

private theorem rs2_0 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem rsL2 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 1 = z := by simp [Fin.snoc]

private theorem rs3_0 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem rs3_1 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem rsL3 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 2 = z := by simp [Fin.snoc]

attribute [local simp] rs2_0 rsL2 rs3_0 rs3_1 rsL3

/-! ### Tameness of the tests -/

theorem tame_bandIn {φ ψ : ℝ → ℝ} (hφ : S.DefinableFun φ) (hψ : S.DefinableFun ψ)
    (hB : S.Definable B) : Tame (bandIn B φ ψ) := by
  have h := Fml.tame_one (S := S) (Fml.all
    (((Fml.ex ((Fml.atom ![0, 2] hφ).and (ltAt 2 1))).and
      (Fml.ex ((Fml.atom ![0, 2] hψ).and (ltAt 1 2)))).imp (Fml.atom id hB)))
  have e : bandIn B φ ψ
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.all
        (((Fml.ex ((Fml.atom ![0, 2] hφ).and (ltAt 2 1))).and
          (Fml.ex ((Fml.atom ![0, 2] hψ).and (ltAt 1 2)))).imp (Fml.atom id hB)))
        (fun _ => x)} := by
    ext a
    simp [bandIn, Fml.eval, rcompPair, rsnocPair, exists_eq_left']
  rw [e]
  exact h

theorem tame_rayLowIn {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (hB : S.Definable B) :
    Tame (rayLowIn B φ) := by
  have h := Fml.tame_one (S := S) (Fml.all
    ((Fml.ex ((Fml.atom ![0, 2] hφ).and (ltAt 1 2))).imp (Fml.atom id hB)))
  have e : rayLowIn B φ
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.all
        ((Fml.ex ((Fml.atom ![0, 2] hφ).and (ltAt 1 2))).imp (Fml.atom id hB)))
        (fun _ => x)} := by
    ext a
    simp [rayLowIn, Fml.eval, rcompPair, rsnocPair, exists_eq_left']
  rw [e]
  exact h

theorem tame_rayHighIn {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (hB : S.Definable B) :
    Tame (rayHighIn B φ) := by
  have h := Fml.tame_one (S := S) (Fml.all
    ((Fml.ex ((Fml.atom ![0, 2] hφ).and (ltAt 2 1))).imp (Fml.atom id hB)))
  have e : rayHighIn B φ
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.all
        ((Fml.ex ((Fml.atom ![0, 2] hφ).and (ltAt 2 1))).imp (Fml.atom id hB)))
        (fun _ => x)} := by
    ext a
    simp [rayHighIn, Fml.eval, rcompPair, rsnocPair, exists_eq_left']
  rw [e]
  exact h

theorem tame_allIn (hB : S.Definable B) : Tame (allIn B) := by
  have h := Fml.tame_one (S := S) (Fml.all (Fml.atom id hB))
  have e : allIn B
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.all (Fml.atom id hB))
        (fun _ => x)} := by
    ext a
    simp [allIn, Fml.eval, rsnocPair]
  rw [e]
  exact h

theorem tame_graphIn {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (hB : S.Definable B) :
    Tame (graphIn B φ) := by
  have h := Fml.tame_one (S := S) (Fml.ex ((Fml.atom id hφ).and (Fml.atom id hB)))
  have e : graphIn B φ
      = {x : ℝ | Fml.eval (S := S) (n := 1)
          (Fml.ex ((Fml.atom id hφ).and (Fml.atom id hB))) (fun _ => x)} := by
    ext a
    simp [graphIn, Fml.eval, rsnocPair, exists_eq_left']
  rw [e]
  exact h

/-! ### Frontier-free constancy -/

/-- On a frontier-free interval, membership is constant — `preconnected_split`. -/
theorem tame_const_on {T : Set ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.Ioo a b, x ∉ frontier T) :
    (∀ x ∈ Set.Ioo a b, x ∈ T) ∨ (∀ x ∈ Set.Ioo a b, x ∉ T) := by
  rcases preconnected_split isPreconnected_Ioo h with hsub | hdis
  · exact Or.inl fun x hx => hsub hx
  · exact Or.inr fun x hx hxT =>
      (Set.eq_empty_iff_forall_notMem.mp hdis x) ⟨hx, hxT⟩

/-! ### The master refinement -/

/-- **The master refinement (D5b).** One bound `N` and one finite cut set `C`: the
exact-count classes cover the line, and on every interval avoiding `C` — one class, all
ranks continuous, and every graph/band/ray/full test constant (both polarities). -/
theorem master_refinement (hA : S.Definable A) :
    ∃ (N : ℕ) (C : Finset ℝ),
      (∀ x : ℝ, ∃ k ≤ N, x ∈ exactSet (fiberFrontier A) k) ∧
      ∀ a b : ℝ, a < b → (∀ s ∈ C, s ∉ Set.Ioo a b) →
        (∃ k ≤ N, Set.Ioo a b ⊆ exactSet (fiberFrontier A) k) ∧
        (∀ j < N, ContinuousOn (nthFn (fiberFrontier A) j) (Set.Ioo a b)) ∧
        (∀ j < N,
          (∀ x ∈ Set.Ioo a b, x ∈ graphIn A (nthFn (fiberFrontier A) j)) ∨
          (∀ x ∈ Set.Ioo a b, x ∉ graphIn A (nthFn (fiberFrontier A) j))) ∧
        (∀ j < N, ∀ B' ∈ ({A, Aᶜ} : Set (Set (Fin 2 → ℝ))),
          (∀ x ∈ Set.Ioo a b,
            x ∈ bandIn B' (nthFn (fiberFrontier A) j) (nthFn (fiberFrontier A) (j+1))) ∨
          (∀ x ∈ Set.Ioo a b,
            x ∉ bandIn B' (nthFn (fiberFrontier A) j) (nthFn (fiberFrontier A) (j+1)))) ∧
        (∀ B' ∈ ({A, Aᶜ} : Set (Set (Fin 2 → ℝ))),
          ((∀ x ∈ Set.Ioo a b, x ∈ rayLowIn B' (nthFn (fiberFrontier A) 0)) ∨
            (∀ x ∈ Set.Ioo a b, x ∉ rayLowIn B' (nthFn (fiberFrontier A) 0))) ∧
          (∀ j < N,
            (∀ x ∈ Set.Ioo a b, x ∈ rayHighIn B' (nthFn (fiberFrontier A) j)) ∨
            (∀ x ∈ Set.Ioo a b, x ∉ rayHighIn B' (nthFn (fiberFrontier A) j))) ∧
          ((∀ x ∈ Set.Ioo a b, x ∈ allIn B') ∨
            (∀ x ∈ Set.Ioo a b, x ∉ allIn B'))) := by
  classical
  have hY := definable_fiberFrontier hA
  have hfibY := fiberFrontier_fiber_finite hA
  obtain ⟨N, hpart⟩ := exactSet_partition hY hfibY
  -- rank cut-sets (choice over all j)
  choose Fcut hFcut using
    (fun j : ℕ => monotonicity_theorem_continuous (definableFun_nthFn hY j))
  -- polarity-indexed definability
  have hpol : ∀ B' ∈ ({A, Aᶜ} : Set (Set (Fin 2 → ℝ))), S.Definable B' := by
    rintro B' (rfl | rfl)
    · exact hA
    · exact S.definable_compl hA
  -- the tame test finiteness proofs
  have hclassfin : ∀ k : ℕ, (frontier (exactSet (fiberFrontier A) k)).Finite :=
    fun k => tame_exactSet hY k
  have hgraphfin : ∀ j : ℕ, (frontier (graphIn A (nthFn (fiberFrontier A) j))).Finite :=
    fun j => tame_graphIn (definableFun_nthFn hY j) hA
  have hbandfinA : ∀ j : ℕ, (frontier (bandIn A (nthFn (fiberFrontier A) j)
      (nthFn (fiberFrontier A) (j+1)))).Finite :=
    fun j => tame_bandIn (definableFun_nthFn hY j) (definableFun_nthFn hY (j+1)) hA
  have hbandfinC : ∀ j : ℕ, (frontier (bandIn Aᶜ (nthFn (fiberFrontier A) j)
      (nthFn (fiberFrontier A) (j+1)))).Finite :=
    fun j => tame_bandIn (definableFun_nthFn hY j) (definableFun_nthFn hY (j+1))
      (S.definable_compl hA)
  have hrayLofinA : (frontier (rayLowIn A (nthFn (fiberFrontier A) 0))).Finite :=
    tame_rayLowIn (definableFun_nthFn hY 0) hA
  have hrayLofinC : (frontier (rayLowIn Aᶜ (nthFn (fiberFrontier A) 0))).Finite :=
    tame_rayLowIn (definableFun_nthFn hY 0) (S.definable_compl hA)
  have hrayHifinA : ∀ j : ℕ, (frontier (rayHighIn A (nthFn (fiberFrontier A) j))).Finite :=
    fun j => tame_rayHighIn (definableFun_nthFn hY j) hA
  have hrayHifinC : ∀ j : ℕ, (frontier (rayHighIn Aᶜ (nthFn (fiberFrontier A) j))).Finite :=
    fun j => tame_rayHighIn (definableFun_nthFn hY j) (S.definable_compl hA)
  have hallfinA : (frontier (allIn A)).Finite := tame_allIn hA
  have hallfinC : (frontier (allIn Aᶜ)).Finite := tame_allIn (S.definable_compl hA)
  -- the master cut set
  set C : Finset ℝ :=
    ((Finset.range N).biUnion Fcut) ∪
    ((Finset.range (N+1)).biUnion (fun k => (hclassfin k).toFinset)) ∪
    ((Finset.range N).biUnion (fun j => (hgraphfin j).toFinset)) ∪
    ((Finset.range N).biUnion (fun j => (hbandfinA j).toFinset ∪ (hbandfinC j).toFinset)) ∪
    (hrayLofinA.toFinset ∪ hrayLofinC.toFinset) ∪
    ((Finset.range N).biUnion (fun j => (hrayHifinA j).toFinset ∪ (hrayHifinC j).toFinset)) ∪
    (hallfinA.toFinset ∪ hallfinC.toFinset) with hCdef
  refine ⟨N, C, hpart, ?_⟩
  intro a b hab havoid
  -- generic constancy from frontier-in-C
  have hconst : ∀ (T : Set ℝ) (hT : (frontier T).Finite),
      (∀ s ∈ hT.toFinset, s ∈ C) →
      (∀ x ∈ Set.Ioo a b, x ∈ T) ∨ (∀ x ∈ Set.Ioo a b, x ∉ T) := by
    intro T hT hsub
    apply tame_const_on
    intro x hx hxfr
    exact havoid x (hsub x (hT.mem_toFinset.mpr hxfr)) hx
  -- component inclusions
  have m1 : ∀ s ∈ (Finset.range N).biUnion Fcut, s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hs)))))
  have m2 : ∀ s ∈ (Finset.range (N+1)).biUnion (fun k => (hclassfin k).toFinset),
      s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hs)))))
  have m3 : ∀ s ∈ (Finset.range N).biUnion (fun j => (hgraphfin j).toFinset),
      s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hs))))
  have m4 : ∀ s ∈ (Finset.range N).biUnion
      (fun j => (hbandfinA j).toFinset ∪ (hbandfinC j).toFinset), s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hs)))
  have m5 : ∀ s ∈ hrayLofinA.toFinset ∪ hrayLofinC.toFinset, s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hs))
  have m6 : ∀ s ∈ (Finset.range N).biUnion
      (fun j => (hrayHifinA j).toFinset ∪ (hrayHifinC j).toFinset), s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hs)
  have m7 : ∀ s ∈ hallfinA.toFinset ∪ hallfinC.toFinset, s ∈ C := fun s hs => by
    rw [hCdef]
    exact Finset.mem_union_right _ hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- one class
    obtain ⟨x₀, hx₀⟩ := exists_between hab
    obtain ⟨k, hkN, hk⟩ := hpart x₀
    rcases hconst _ (hclassfin k) (fun s hs => m2 s
        (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hs⟩)) with hin | hout
    · exact ⟨k, hkN, fun x hx => hin x hx⟩
    · exact absurd hk (hout x₀ hx₀)
  · -- rank continuity
    intro j hj
    exact (hFcut j a b hab (fun s hs => havoid s
      (m1 s (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hs⟩)))).2
  · -- graph constancy
    intro j hj
    exact hconst _ (hgraphfin j) (fun s hs => m3 s
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hs⟩))
  · -- band constancy, both polarities
    rintro j hj B' (rfl | rfl)
    · exact hconst _ (hbandfinA j) (fun s hs => m4 s
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_union_left _ hs⟩))
    · exact hconst _ (hbandfinC j) (fun s hs => m4 s
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_union_right _ hs⟩))
  · -- rays and the full test, both polarities
    rintro B' (rfl | rfl)
    · refine ⟨?_, ?_, ?_⟩
      · exact hconst _ hrayLofinA (fun s hs => m5 s (Finset.mem_union_left _ hs))
      · intro j hj
        exact hconst _ (hrayHifinA j) (fun s hs => m6 s
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_union_left _ hs⟩))
      · exact hconst _ hallfinA (fun s hs => m7 s (Finset.mem_union_left _ hs))
    · refine ⟨?_, ?_, ?_⟩
      · exact hconst _ hrayLofinC (fun s hs => m5 s (Finset.mem_union_right _ hs))
      · intro j hj
        exact hconst _ (hrayHifinC j) (fun s hs => m6 s
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_union_right _ hs⟩))
      · exact hconst _ hallfinC (fun s hs => m7 s (Finset.mem_union_right _ hs))

end Sundog.OMinimalAbstract
