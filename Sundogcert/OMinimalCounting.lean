/-
# O-min lane R4-D1: the counting formulas — fiber-size sets are tame.

The formula-layer stress test: `countSet A k = {x | the fiber A_x has ≥ k points}` is tame for
every `k`, by an **`Fml`-valued recursion over the meta-natural `k`** — the formula grows with
`k`, which is a Lean natural, not a structure element.

Two pieces of new general machinery:
- **`Fml.reindex`** — pullback of *whole formulas* along coordinate maps (atoms compose their
  reindexes; `∃` threads through `extendMap σ = snoc (castSucc ∘ σ) last`), with the semantics
  `(reindex σ φ).eval f ↔ φ.eval (f ∘ σ)` by one induction. This upgrades the layer from
  reindexable atoms to reindexable formulas — what the recursion needs to call itself at the
  freshly bound coordinate.
- **`AboveCount`** — the semantic mirror (`≥ k` fiber points strictly above `t`), with the
  chain kit for D2: antitonicity in `t`, monotonicity in `k` (`countSet_anti`), extraction of a
  `k`-element `Finset` (`aboveCount_exists_finset` — witnesses are strictly increasing, hence
  distinct), the converse via `min'`-peeling (`aboveCount_of_finset`), membership from any
  finite witness set (`mem_countSet_of_finset`), and the D2 punchline input:
  `infinite_fiber_of_mem_all` — a point in every `countSet A k` has an infinite fiber.

**Honest fence.** D1 only: the sets and their calculus; the dichotomy kill and point functions
are D2, the curves D3, the wall D4.
-/
import Sundogcert.OMinimalSlice

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

/-! ### Reindexing whole formulas -/

namespace Fml

/-- Extend a coordinate map under one binder: old coordinates map through `σ`, the fresh last
coordinate maps to the fresh last coordinate. -/
def extendMap {m n : ℕ} (σ : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.snoc (Fin.castSucc ∘ σ) (Fin.last n)

theorem snoc_comp_extendMap {m n : ℕ} (σ : Fin m → Fin n) (f : Fin n → ℝ) (y : ℝ) :
    (Fin.snoc f y : Fin (n + 1) → ℝ) ∘ extendMap σ = Fin.snoc (f ∘ σ) y := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [extendMap, Function.comp]
  | cast j => simp [extendMap, Function.comp]

/-- Pull back a whole formula along a coordinate map. -/
def reindex {S : OMinStructure} : ∀ {m n : ℕ}, (Fin m → Fin n) → Fml S m → Fml S n
  | _, _, σ, .atom τ h => .atom (σ ∘ τ) h
  | _, _, σ, .not φ => .not (reindex σ φ)
  | _, _, σ, .and φ ψ => .and (reindex σ φ) (reindex σ ψ)
  | _, _, σ, .ex φ => .ex (reindex (extendMap σ) φ)

/-- Reindexing semantics: evaluate through the coordinate map. -/
theorem eval_reindex {S : OMinStructure} {m : ℕ} (φ : Fml S m) :
    ∀ {n : ℕ} (σ : Fin m → Fin n) (f : Fin n → ℝ),
      (reindex σ φ).eval f ↔ φ.eval (f ∘ σ) := by
  induction φ with
  | atom τ h =>
    intro n σ f
    simp [reindex, Fml.eval, Function.comp_assoc]
  | not φ ih =>
    intro n σ f
    simp [reindex, Fml.eval, ih]
  | and φ ψ ih₁ ih₂ =>
    intro n σ f
    simp [reindex, Fml.eval, ih₁, ih₂]
  | ex φ ih =>
    intro n σ f
    simp only [reindex, Fml.eval]
    constructor
    · rintro ⟨y, hy⟩
      have h := (ih (extendMap σ) (Fin.snoc f y)).mp hy
      rw [snoc_comp_extendMap] at h
      exact ⟨y, h⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, (ih (extendMap σ) (Fin.snoc f y)).mpr ?_⟩
      rw [snoc_comp_extendMap]
      exact hy

/-- The true formula. -/
def tru {S : OMinStructure} {n : ℕ} : Fml S n := .atom id (S.definable_univ n)

@[simp] theorem eval_tru {S : OMinStructure} {n : ℕ} (f : Fin n → ℝ) :
    (tru (S := S)).eval f ↔ True := by
  simp [tru, Fml.eval]

end Fml

open Fml

/-! ### Local snoc helpers and the pair collapse -/

private theorem snocA (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocB (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 1 = y := by
  simp [Fin.snoc]

private theorem snocD (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocE (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 2 = y := by
  simp [Fin.snoc]

private theorem comp02 (g : Fin 2 → ℝ) (y : ℝ) :
    ((Fin.snoc g y : Fin 3 → ℝ) ∘ ![0, 2]) = pairFn (g 0) y := by
  funext k
  fin_cases k <;> simp [pairFn, Fin.snoc, Function.comp]

/-! ### The counting recursion, semantic and syntactic -/

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-- `≥ k` fiber points of `A` above `x`, all strictly greater than `t` (semantic mirror). -/
def AboveCount (A : Set (Fin 2 → ℝ)) (x : ℝ) : ℝ → ℕ → Prop
  | _, 0 => True
  | t, k + 1 => ∃ y, t < y ∧ pairFn x y ∈ A ∧ AboveCount A x y k

/-- The counting formula, slots `(x = 0, t = 1)`: built by recursion on the meta-natural `k`,
recursing through `reindex ![0, 2]` at the freshly bound point. -/
def gtCount (hA : S.Definable A) : ℕ → Fml S 2
  | 0 => .tru
  | k + 1 => .ex ((ltAt 1 2).and ((Fml.atom ![0, 2] hA).and
      (Fml.reindex ![0, 2] (gtCount hA k))))

theorem eval_gtCount (hA : S.Definable A) : ∀ (k : ℕ) (g : Fin 2 → ℝ),
    (gtCount hA k).eval g ↔ AboveCount A (g 0) (g 1) k := by
  intro k
  induction k with
  | zero =>
    intro g
    simp [gtCount, AboveCount]
  | succ k ih =>
    intro g
    simp only [gtCount, Fml.eval, eval_ltAt, Fml.eval_reindex, comp02, snocD, snocE,
      pairFn_zero, pairFn_one, ih, AboveCount]

/-- `B_k`: the set of parameters whose fiber has at least `k` points. -/
def countSet (A : Set (Fin 2 → ℝ)) (k : ℕ) : Set ℝ := {x | ∃ t, AboveCount A x t k}

/-- **The counting sets are tame** (the formula-layer stress test, passed). -/
theorem tame_countSet (hA : S.Definable A) (k : ℕ) : Tame (countSet A k) := by
  have h := Fml.tame_one (S := S) (Fml.ex (gtCount hA k))
  have e : countSet A k = {x : ℝ | Fml.eval (S := S) (n := 1)
      (Fml.ex (gtCount hA k)) (fun _ => x)} := by
    ext x
    simp only [countSet, Set.mem_setOf_eq, Fml.eval, eval_gtCount, snocA, snocB]
  rw [e]
  exact h

/-! ### The chain kit for D2 -/

theorem aboveCount_anti {x : ℝ} : ∀ {k : ℕ} {t t' : ℝ},
    t' ≤ t → AboveCount A x t k → AboveCount A x t' k
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, h, ⟨y, h1, h2, h3⟩ => ⟨y, lt_of_le_of_lt h h1, h2, h3⟩

theorem aboveCount_mono {x t : ℝ} : ∀ {k : ℕ},
    AboveCount A x t (k + 1) → AboveCount A x t k
  | 0, _ => trivial
  | _ + 1, ⟨y, h1, h2, h3⟩ => ⟨y, h1, h2, aboveCount_mono h3⟩

/-- The chain decreases. -/
theorem countSet_anti (A : Set (Fin 2 → ℝ)) (k : ℕ) :
    countSet A (k + 1) ⊆ countSet A k :=
  fun _ ⟨t, h⟩ => ⟨t, aboveCount_mono h⟩

/-- Extract a `k`-element witness set (the chain is strictly increasing, hence distinct). -/
theorem aboveCount_exists_finset {x : ℝ} : ∀ {k : ℕ} {t : ℝ}, AboveCount A x t k →
    ∃ Y : Finset ℝ, Y.card = k ∧ ∀ y ∈ Y, t < y ∧ pairFn x y ∈ A := by
  intro k
  induction k with
  | zero =>
    intro t _
    exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    rintro t ⟨y, h1, h2, h3⟩
    obtain ⟨Y, hcard, hY⟩ := ih h3
    have hnot : y ∉ Y := fun hyY => absurd (hY y hyY).1 (lt_irrefl y)
    refine ⟨insert y Y, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hnot, hcard]
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzY
      · exact ⟨h1, h2⟩
      · obtain ⟨hz1, hz2⟩ := hY z hzY
        exact ⟨lt_trans h1 hz1, hz2⟩

/-- **The D2 punchline input**: a point in every counting set has an infinite fiber. -/
theorem infinite_fiber_of_mem_all {x : ℝ} (h : ∀ k, x ∈ countSet A k) :
    {y : ℝ | pairFn x y ∈ A}.Infinite := by
  intro hfin
  obtain ⟨t, hAC⟩ := h (hfin.toFinset.card + 1)
  obtain ⟨Y, hcard, hY⟩ := aboveCount_exists_finset hAC
  have hsub : Y ⊆ hfin.toFinset := by
    intro z hz
    rw [Set.Finite.mem_toFinset]
    exact (hY z hz).2
  have := Finset.card_le_card hsub
  omega

/-- The converse: build `AboveCount` from any finite witness set by `min'`-peeling. -/
theorem aboveCount_of_finset {x : ℝ} : ∀ (k : ℕ) (Y : Finset ℝ), Y.card = k →
    (∀ y ∈ Y, pairFn x y ∈ A) → ∀ t : ℝ, (∀ y ∈ Y, t < y) → AboveCount A x t k := by
  intro k
  induction k with
  | zero =>
    intro Y _ _ t _
    trivial
  | succ k ih =>
    intro Y hcard hmem t hbelow
    have hne : Y.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    refine ⟨Y.min' hne, hbelow _ (Y.min'_mem hne), hmem _ (Y.min'_mem hne), ?_⟩
    apply ih (Y.erase (Y.min' hne))
    · rw [Finset.card_erase_of_mem (Y.min'_mem hne), hcard]
      omega
    · intro y hy
      exact hmem y (Finset.mem_of_mem_erase hy)
    · intro y hy
      have h1 := Y.min'_le y (Finset.mem_of_mem_erase hy)
      have h2 := (Finset.mem_erase.mp hy).1
      exact lt_of_le_of_ne h1 (Ne.symm h2)

/-- Membership in the counting set from any finite witness set. -/
theorem mem_countSet_of_finset {x : ℝ} {Y : Finset ℝ}
    (hmem : ∀ y ∈ Y, pairFn x y ∈ A) : x ∈ countSet A Y.card := by
  by_cases hne : Y.Nonempty
  · refine ⟨Y.min' hne - 1, aboveCount_of_finset _ Y rfl hmem _ ?_⟩
    intro y hy
    have := Y.min'_le y hy
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    exact ⟨0, trivial⟩

end Sundog.OMinimalAbstract
