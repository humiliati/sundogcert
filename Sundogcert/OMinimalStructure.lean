/-
# O-min lane R4-A: the abstract o-minimal structure and its definable calculus.

The van den Dries-style interface, formalized over dimension-indexed sets `Set (Fin n → ℝ)`:

- **booleans** per dimension (`empty`, `compl`, `union`);
- **substitution closure in one axiom** (`definable_subst`): definables are closed under
  `{f | f ∘ σ ∈ A}` for *every* `σ : Fin m → Fin n` — cylinders, coordinate permutations, and
  diagonal identifications all at once;
- **projection** (`definable_proj`), in the working `∃`-form over `Fin.snoc` (the image of the
  drop-last restriction map, stated the way proofs use it);
- **atoms**: the order `{f | f 0 < f 1}` and the singletons `{f | f 0 = r}`;
- **the o-minimality axiom** (`tame_dim_one`): dimension-one definables are `Tame` — rung 1's
  finite-frontier predicate slots in as the `S₁` axiom unchanged, exactly as designed.

On the interface, the definable calculus with no instance needed: intersections and finite
unions; permutation/cylinder/diagonal corollaries of substitution; rays and open intervals;
definable functions (`DefinableFun`, via graphs) closed under identity, constants, and
**composition** (the three-variable projection argument); preimages and level/superlevel sets;
and the tameness payoffs (level and superlevel sets of definable functions are tame — the
abstract echo of rung 1's `netDef_tame`).

Capstone: `definable_toOne_iff_tame` — **the dimension-one definable sets are exactly the tame
sets**. The ⊇ direction runs through rung 2's normal form (`tame_iff_normalForm`) plus the shape
lemma for open `OrdConnected` sets (∅ / `univ` / `Ioi` / `Iio` / `Ioo`, by boundedness cases) —
rung 2 becomes load-bearing for the abstract interface.

**Honest fence.** An interface plus its calculus; **non-vacuity is R4-B's deliverable** (the
n-dimensional semilinear instance), not claimed here. No monotonicity theorem, no cell
decomposition — those are R4-C/D.
-/
import Sundogcert.OMinimalNormalForm

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalNormalForm

/-! ### Small `Fin.snoc` and reindex evaluation helpers -/

private theorem snoc1_0 (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snoc1_1 (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 1 = y := by
  simp [Fin.snoc]

private theorem snoc2_0 (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snoc2_1 (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snoc2_2 (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 2 = y := by
  simp [Fin.snoc]

/-- Every `Fin 1 → ℝ` is the constant function at its value. -/
private theorem eq_const_of_fin_one (f : Fin 1 → ℝ) : f = fun _ => f 0 :=
  funext fun i => congrArg f (Fin.eq_zero i)

/-! ### The structure -/

/-- **A van den Dries-style o-minimal structure on ℝ.** Definable families over
`Set (Fin n → ℝ)`; booleans; substitution closure (one axiom = cylinders + permutations +
diagonals); projection (working `∃`/`snoc` form); the order and singleton atoms; and rung 1's
`Tame` as the dimension-one (o-minimality) axiom. -/
structure OMinStructure where
  Definable : ∀ {n : ℕ}, Set (Fin n → ℝ) → Prop
  definable_empty : ∀ {n : ℕ}, Definable (∅ : Set (Fin n → ℝ))
  definable_compl : ∀ {n : ℕ} {A : Set (Fin n → ℝ)}, Definable A → Definable Aᶜ
  definable_union : ∀ {n : ℕ} {A B : Set (Fin n → ℝ)},
    Definable A → Definable B → Definable (A ∪ B)
  definable_subst : ∀ {m n : ℕ} (σ : Fin m → Fin n) {A : Set (Fin m → ℝ)},
    Definable A → Definable {f : Fin n → ℝ | f ∘ σ ∈ A}
  definable_proj : ∀ {n : ℕ} {A : Set (Fin (n + 1) → ℝ)},
    Definable A → Definable {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A}
  definable_lt : Definable {f : Fin 2 → ℝ | f 0 < f 1}
  definable_singleton : ∀ r : ℝ, Definable {f : Fin 1 → ℝ | f 0 = r}
  tame_dim_one : ∀ {A : Set (Fin 1 → ℝ)}, Definable A → Tame {x : ℝ | (fun _ => x) ∈ A}

/-- The dimension-one set attached to a set of reals. -/
def toOne (T : Set ℝ) : Set (Fin 1 → ℝ) := {f | f 0 ∈ T}

theorem toOne_eval (A : Set (Fin 1 → ℝ)) : toOne {x : ℝ | (fun _ => x) ∈ A} = A := by
  ext f
  simp only [toOne, Set.mem_setOf_eq]
  rw [← eq_const_of_fin_one f]

namespace OMinStructure

variable (S : OMinStructure)

/-! ### Boolean calculus -/

theorem definable_univ (n : ℕ) : S.Definable (Set.univ : Set (Fin n → ℝ)) := by
  have h := S.definable_compl (S.definable_empty (n := n))
  simpa using h

theorem definable_inter {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : S.Definable A) (hB : S.Definable B) : S.Definable (A ∩ B) := by
  have h := S.definable_compl (S.definable_union (S.definable_compl hA) (S.definable_compl hB))
  simpa [Set.compl_union, compl_compl] using h

theorem definable_sdiff {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : S.Definable A) (hB : S.Definable B) : S.Definable (A \ B) :=
  S.definable_inter hA (S.definable_compl hB)

/-- Tame transport in the convenient `toOne` form. -/
theorem tame_of_definable_toOne {T : Set ℝ} (h : S.Definable (toOne T)) : Tame T := by
  have := S.tame_dim_one h
  simpa [toOne] using this

/-! ### Substitution corollaries: reversed order, diagonal -/

/-- The reversed order `{f | f 1 < f 0}` (substitution along the swap). -/
theorem definable_gt : S.Definable {f : Fin 2 → ℝ | f 1 < f 0} := by
  have h := S.definable_subst (![1, 0] : Fin 2 → Fin 2) S.definable_lt
  have e : {f : Fin 2 → ℝ | f ∘ ![1, 0] ∈ {f : Fin 2 → ℝ | f 0 < f 1}}
      = {f : Fin 2 → ℝ | f 1 < f 0} := by
    ext f
    simp [Function.comp]
  rwa [e] at h

/-- The diagonal `{f | f 0 = f 1}` (complement of the two strict orders). -/
theorem definable_diag : S.Definable {f : Fin 2 → ℝ | f 0 = f 1} := by
  have h := S.definable_compl (S.definable_union S.definable_lt S.definable_gt)
  have e : ({f : Fin 2 → ℝ | f 0 < f 1} ∪ {f : Fin 2 → ℝ | f 1 < f 0})ᶜ
      = {f : Fin 2 → ℝ | f 0 = f 1} := by
    ext f
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h2 h1
    · rintro h
      exact ⟨le_of_eq h.symm, le_of_eq h⟩
  rwa [e] at h

/-! ### Rays and intervals are definable -/

/-- `(r, ∞)` is definable: project `y = r ∧ y < x`. -/
theorem definable_Ioi (r : ℝ) : S.Definable (toOne (Set.Ioi r)) := by
  -- the constant-second-coordinate set {h | h 1 = r}
  have h1 := S.definable_subst (![1] : Fin 1 → Fin 2) (S.definable_singleton r)
  have e1 : {h : Fin 2 → ℝ | h ∘ ![1] ∈ {f : Fin 1 → ℝ | f 0 = r}}
      = {h : Fin 2 → ℝ | h 1 = r} := by
    ext h
    simp [Function.comp]
  rw [e1] at h1
  -- combine with {h | h 1 < h 0} and project the second coordinate
  have h3 := S.definable_proj (S.definable_inter h1 S.definable_gt)
  have e3 : {g : Fin 1 → ℝ | ∃ y : ℝ, Fin.snoc g y ∈
        {h : Fin 2 → ℝ | h 1 = r} ∩ {h : Fin 2 → ℝ | h 1 < h 0}}
      = toOne (Set.Ioi r) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, snoc1_0, snoc1_1, toOne, Set.mem_Ioi]
    constructor
    · rintro ⟨y, rfl, h⟩
      exact h
    · intro h
      exact ⟨r, rfl, h⟩
  rwa [e3] at h3

/-- `(-∞, r)` is definable: project `y = r ∧ x < y`. -/
theorem definable_Iio (r : ℝ) : S.Definable (toOne (Set.Iio r)) := by
  have h1 := S.definable_subst (![1] : Fin 1 → Fin 2) (S.definable_singleton r)
  have e1 : {h : Fin 2 → ℝ | h ∘ ![1] ∈ {f : Fin 1 → ℝ | f 0 = r}}
      = {h : Fin 2 → ℝ | h 1 = r} := by
    ext h
    simp [Function.comp]
  rw [e1] at h1
  have h3 := S.definable_proj (S.definable_inter h1 S.definable_lt)
  have e3 : {g : Fin 1 → ℝ | ∃ y : ℝ, Fin.snoc g y ∈
        {h : Fin 2 → ℝ | h 1 = r} ∩ {h : Fin 2 → ℝ | h 0 < h 1}}
      = toOne (Set.Iio r) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, snoc1_0, snoc1_1, toOne, Set.mem_Iio]
    constructor
    · rintro ⟨y, rfl, h⟩
      exact h
    · intro h
      exact ⟨r, rfl, h⟩
  rwa [e3] at h3

/-- Open bounded intervals are definable. -/
theorem definable_Ioo (a b : ℝ) : S.Definable (toOne (Set.Ioo a b)) := by
  have h := S.definable_inter (S.definable_Ioi a) (S.definable_Iio b)
  have e : toOne (Set.Ioi a) ∩ toOne (Set.Iio b) = toOne (Set.Ioo a b) := by
    ext f
    simp [toOne, Set.mem_Ioo]
  rwa [e] at h

/-- Singletons of reals, in `toOne` form. -/
theorem definable_toOne_singleton (r : ℝ) : S.Definable (toOne {r}) := by
  have h := S.definable_singleton r
  have e : {f : Fin 1 → ℝ | f 0 = r} = toOne {r} := by
    ext f
    simp [toOne]
  rwa [e] at h

/-! ### Definable functions -/

/-- A function is definable when its graph is. -/
def DefinableFun (φ : ℝ → ℝ) : Prop := S.Definable {h : Fin 2 → ℝ | φ (h 0) = h 1}

theorem definableFun_id : S.DefinableFun id := by
  have h := S.definable_diag
  have e : {f : Fin 2 → ℝ | f 0 = f 1} = {h : Fin 2 → ℝ | id (h 0) = h 1} := by
    ext f
    simp
  rwa [e] at h

theorem definableFun_const (c : ℝ) : S.DefinableFun (fun _ => c) := by
  have h1 := S.definable_subst (![1] : Fin 1 → Fin 2) (S.definable_singleton c)
  have e : {h : Fin 2 → ℝ | h ∘ ![1] ∈ {f : Fin 1 → ℝ | f 0 = c}}
      = {h : Fin 2 → ℝ | (fun _ : ℝ => c) (h 0) = h 1} := by
    ext h
    simp [Function.comp, eq_comm]
  rwa [e] at h1

/-- **Composition of definable functions is definable** — the three-variable projection
argument: the graph of `ψ ∘ φ` is `∃ y, (x, y) ∈ graph φ ∧ (y, z) ∈ graph ψ`, with `y` in the
last (projected) coordinate. -/
theorem DefinableFun.comp {φ ψ : ℝ → ℝ} (hψ : S.DefinableFun ψ) (hφ : S.DefinableFun φ) :
    S.DefinableFun (ψ ∘ φ) := by
  -- coordinates of Fin 3: 0 = x, 1 = z, 2 = y (the projected middle value)
  have h1 := S.definable_subst (![0, 2] : Fin 2 → Fin 3) hφ
  have e1 : {h : Fin 3 → ℝ | h ∘ ![0, 2] ∈ {k : Fin 2 → ℝ | φ (k 0) = k 1}}
      = {h : Fin 3 → ℝ | φ (h 0) = h 2} := by
    ext h
    simp [Function.comp]
  rw [e1] at h1
  have h2 := S.definable_subst (![2, 1] : Fin 2 → Fin 3) hψ
  have e2 : {h : Fin 3 → ℝ | h ∘ ![2, 1] ∈ {k : Fin 2 → ℝ | ψ (k 0) = k 1}}
      = {h : Fin 3 → ℝ | ψ (h 2) = h 1} := by
    ext h
    simp [Function.comp]
  rw [e2] at h2
  have h3 := S.definable_proj (S.definable_inter h1 h2)
  have e3 : {g : Fin 2 → ℝ | ∃ y : ℝ, Fin.snoc g y ∈
        {h : Fin 3 → ℝ | φ (h 0) = h 2} ∩ {h : Fin 3 → ℝ | ψ (h 2) = h 1}}
      = {h : Fin 2 → ℝ | (ψ ∘ φ) (h 0) = h 1} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, snoc2_0, snoc2_1, snoc2_2,
      Function.comp_apply]
    constructor
    · rintro ⟨y, h1', h2'⟩
      rw [← h1'] at h2'
      exact h2'
    · intro h
      exact ⟨φ (g 0), rfl, h⟩
  rwa [e3] at h3

/-- Preimages of dimension-one definables under definable functions are definable:
`{x | φ x ∈ᵀ A}` via `∃ y, y = φ x ∧ y ∈ᵀ A`. -/
theorem DefinableFun.preimage {φ : ℝ → ℝ} (hφ : S.DefinableFun φ)
    {A : Set (Fin 1 → ℝ)} (hA : S.Definable A) :
    S.Definable {g : Fin 1 → ℝ | (fun _ : Fin 1 => φ (g 0)) ∈ A} := by
  -- coordinates of Fin 2: 0 = x, 1 = y (the projected value φ x)
  have h1 := S.definable_subst (![1] : Fin 1 → Fin 2) hA
  have h3 := S.definable_proj (S.definable_inter hφ h1)
  have e3 : {g : Fin 1 → ℝ | ∃ y : ℝ, Fin.snoc g y ∈
        {h : Fin 2 → ℝ | φ (h 0) = h 1} ∩ {h : Fin 2 → ℝ | h ∘ ![1] ∈ A}}
      = {g : Fin 1 → ℝ | (fun _ : Fin 1 => φ (g 0)) ∈ A} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, snoc1_0, snoc1_1]
    have ecomp : ∀ y : ℝ, (Fin.snoc g y ∘ ![1] : Fin 1 → ℝ) = fun _ => y := by
      intro y
      funext i
      simp [Function.comp, snoc1_1]
    constructor
    · rintro ⟨y, rfl, hmem⟩
      rw [ecomp] at hmem
      exact hmem
    · intro hmem
      refine ⟨φ (g 0), rfl, ?_⟩
      rw [ecomp]
      exact hmem
  rwa [e3] at h3

/-- Level sets of definable functions are definable. -/
theorem DefinableFun.levelSet {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (r : ℝ) :
    S.Definable (toOne {x : ℝ | φ x = r}) := by
  have h := hφ.preimage S (S.definable_toOne_singleton r)
  have e : {g : Fin 1 → ℝ | (fun _ : Fin 1 => φ (g 0)) ∈ toOne {r}}
      = toOne {x : ℝ | φ x = r} := by
    ext g
    simp [toOne]
  rwa [e] at h

/-- Strict superlevel sets of definable functions are definable. -/
theorem DefinableFun.superlevelSet {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (r : ℝ) :
    S.Definable (toOne {x : ℝ | r < φ x}) := by
  have h := hφ.preimage S (S.definable_Ioi r)
  have e : {g : Fin 1 → ℝ | (fun _ : Fin 1 => φ (g 0)) ∈ toOne (Set.Ioi r)}
      = toOne {x : ℝ | r < φ x} := by
    ext g
    simp [toOne]
  rwa [e] at h

/-- **The tameness payoff (the abstract echo of rung 1's `netDef_tame`)**: every level set of
every definable function, in every o-minimal structure, is tame. -/
theorem DefinableFun.tame_levelSet {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (r : ℝ) :
    Tame {x : ℝ | φ x = r} :=
  S.tame_of_definable_toOne (hφ.levelSet S r)

/-- Superlevel sets of definable functions are tame. -/
theorem DefinableFun.tame_superlevelSet {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (r : ℝ) :
    Tame {x : ℝ | r < φ x} :=
  S.tame_of_definable_toOne (hφ.superlevelSet S r)

end OMinStructure

/-! ### The shape lemma: open `OrdConnected` sets are literal intervals -/

/-- An open set contains points strictly on both sides of each of its members. -/
private theorem exists_lt_mem_lt {j : Set ℝ} (ho : IsOpen j) {x : ℝ} (hx : x ∈ j) :
    (∃ u ∈ j, u < x) ∧ (∃ v ∈ j, x < v) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho x hx
  constructor
  · refine ⟨x - ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : x - ε / 2 - x < 0)]
    linarith
  · refine ⟨x + ε / 2, hball ?_, by linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < x + ε / 2 - x)]
    linarith

/-- **The shape lemma.** An open `OrdConnected` subset of ℝ is `∅`, `univ`, an open ray, or a
bounded open interval — by boundedness cases, with `csInf`/`csSup` as the endpoints. This is the
transport that turns rung 2's abstract normal-form pieces into definable atoms. -/
theorem isOpen_ordConnected_shape {j : Set ℝ} (ho : IsOpen j) (hc : j.OrdConnected) :
    j = ∅ ∨ j = Set.univ ∨ (∃ a, j = Set.Ioi a) ∨ (∃ b, j = Set.Iio b) ∨
      ∃ a b, j = Set.Ioo a b := by
  rcases j.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl rfl
  by_cases hbb : BddBelow j <;> by_cases hba : BddAbove j
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨sInf j, sSup j, ?_⟩)))
    ext x
    simp only [Set.mem_Ioo]
    constructor
    · intro hx
      obtain ⟨⟨u, hu, hux⟩, ⟨v, hv, hxv⟩⟩ := exists_lt_mem_lt ho hx
      exact ⟨lt_of_le_of_lt (csInf_le hbb hu) hux, lt_of_lt_of_le hxv (le_csSup hba hv)⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hne h1
      obtain ⟨v, hv, hxv⟩ := exists_lt_of_lt_csSup hne h2
      exact hc.out hu hv ⟨hux.le, hxv.le⟩
  · refine Or.inr (Or.inr (Or.inl ⟨sInf j, ?_⟩))
    ext x
    simp only [Set.mem_Ioi]
    constructor
    · intro hx
      obtain ⟨⟨u, hu, hux⟩, _⟩ := exists_lt_mem_lt ho hx
      exact lt_of_le_of_lt (csInf_le hbb hu) hux
    · intro h1
      obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hne h1
      obtain ⟨v, hv, hxv⟩ := (not_bddAbove_iff.mp hba) x
      exact hc.out hu hv ⟨hux.le, hxv.le⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨sSup j, ?_⟩)))
    ext x
    simp only [Set.mem_Iio]
    constructor
    · intro hx
      obtain ⟨_, ⟨v, hv, hxv⟩⟩ := exists_lt_mem_lt ho hx
      exact lt_of_lt_of_le hxv (le_csSup hba hv)
    · intro h2
      obtain ⟨v, hv, hxv⟩ := exists_lt_of_lt_csSup hne h2
      obtain ⟨u, hu, hux⟩ := (not_bddBelow_iff.mp hbb) x
      exact hc.out hu hv ⟨hux.le, hxv.le⟩
  · refine Or.inr (Or.inl ?_)
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨u, hu, hux⟩ := (not_bddBelow_iff.mp hbb) x
    obtain ⟨v, hv, hxv⟩ := (not_bddAbove_iff.mp hba) x
    exact hc.out hu hv ⟨hux.le, hxv.le⟩

/-! ### The capstone: dimension-one definables are exactly the tame sets -/

theorem toOne_empty : toOne (∅ : Set ℝ) = ∅ := by
  ext f
  simp [toOne]

theorem toOne_univ : toOne (Set.univ : Set ℝ) = Set.univ := by
  ext f
  simp [toOne]

theorem toOne_union (A B : Set ℝ) : toOne (A ∪ B) = toOne A ∪ toOne B := by
  ext f
  simp [toOne]

namespace OMinStructure

variable (S : OMinStructure)

/-- Every open interval (as an open `OrdConnected` set) is definable, via the shape lemma. -/
theorem definable_of_isOpen_ordConnected {j : Set ℝ} (ho : IsOpen j) (hc : j.OrdConnected) :
    S.Definable (toOne j) := by
  rcases isOpen_ordConnected_shape ho hc with rfl | rfl | ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, b, rfl⟩
  · rw [toOne_empty]
    exact S.definable_empty
  · rw [toOne_univ]
    exact S.definable_univ 1
  · exact S.definable_Ioi a
  · exact S.definable_Iio b
  · exact S.definable_Ioo a b

/-- Finite point sets are definable. -/
theorem definable_toOne_finset (P : Finset ℝ) : S.Definable (toOne ↑P) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, toOne_empty]
    exact S.definable_empty
  | insert a P haP ih =>
    rw [Finset.coe_insert, Set.insert_eq, toOne_union]
    exact S.definable_union (S.definable_toOne_singleton a) ih

/-- Finite unions of definable real sets are definable. -/
theorem definable_toOne_sUnion (J : Finset (Set ℝ))
    (h : ∀ j ∈ J, S.Definable (toOne j)) : S.Definable (toOne (⋃₀ ↑J)) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Set.sUnion_empty, toOne_empty]
    exact S.definable_empty
  | insert j J hjJ ih =>
    rw [Finset.coe_insert, Set.sUnion_insert, toOne_union]
    exact S.definable_union (h j (Finset.mem_insert_self j J))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **⊇: every tame set is definable** — rung 2's normal form decomposes a tame set into points
and open intervals, and each piece is definable by the atoms + the shape lemma. -/
theorem definable_of_tame {T : Set ℝ} (hT : Tame T) : S.Definable (toOne T) := by
  obtain ⟨P, J, hJ, rfl⟩ := normalForm_of_tame hT
  rw [toOne_union]
  exact S.definable_union (S.definable_toOne_finset P)
    (S.definable_toOne_sUnion J fun j hj =>
      S.definable_of_isOpen_ordConnected (hJ j hj).1 (hJ j hj).2)

/-- **The capstone (R4-A headline): the dimension-one definable sets are EXACTLY the tame sets**
— rung 1's `Tame` is the right `S₁` axiom, in both directions, for every o-minimal structure. -/
theorem definable_toOne_iff_tame (T : Set ℝ) : S.Definable (toOne T) ↔ Tame T :=
  ⟨S.tame_of_definable_toOne, S.definable_of_tame⟩

/-- The capstone for arbitrary dimension-one definables (every `A : Set (Fin 1 → ℝ)` is a
`toOne`). -/
theorem definable_dim_one_iff_tame (A : Set (Fin 1 → ℝ)) :
    S.Definable A ↔ Tame {x : ℝ | (fun _ => x) ∈ A} := by
  constructor
  · exact fun h => S.tame_dim_one h
  · intro h
    have h2 := S.definable_of_tame h
    rwa [toOne_eval] at h2

end OMinStructure

/-- Gate alias (short name: long qualified names wrap `#print axioms` output past the
pretty-printer width, breaking `#guard_msgs`). The capstone: `S₁` = tame, exactly. -/
theorem s1_eq_tame (S : OMinStructure) (T : Set ℝ) : S.Definable (toOne T) ↔ Tame T :=
  S.definable_toOne_iff_tame T

/-- Gate alias. The tameness payoff: level sets of definable functions are tame. -/
theorem defFun_tame_level (S : OMinStructure) {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (r : ℝ) :
    Tame {x : ℝ | φ x = r} :=
  hφ.tame_levelSet S r

end Sundog.OMinimalAbstract
