/-
# O-min lane R4-D4b: the β-machinery (least non-normal height and its fiber neighbors).

The classical Finiteness-Lemma route needs three definable functions on the bad set: the
least non-normal height `β`, and its fiber neighbors `β⁻` (largest fiber point below) and
`β⁺` (smallest fiber point above). This module builds them, plus the fiber max/min needed
for the ±∞-ray cases, all through one engine:

- **`selFn` — the generic definable selector**: any definable *functional* relation
  `R ⊆ ℝ²` totalizes (by 0) to a `DefinableFun` — D2's `nthFn` pattern abstracted over the
  atom, proved once, instantiated five times.
- **`leastBadSet`/`betaFn`**: existence via `IsClosed.csInf_mem` — the not-normal heights
  are closed (D4a), nonempty on the bad set, and bounded below because bottom-ray normality
  pushes every sufficiently low height into an empty box (`notNormal_bddBelow`).
- **`fiberMaxSet`/`fiberMinSet`, `maxBelowSet`/`minAboveSet`**: existence by `Finset.max'`
  on the finite fibers; the neighbor relations take the `betaFn` *graph itself* as an atom —
  definable functions feed back into the formula layer.
- **The bad sets are tame**: `tame_badFin` (some finite height non-normal),
  `tame_notNormalTop`/`tame_notNormalBot` (ray-normality fails).

**Honest fence.** D4b only: no tube kill (D4c), no UF (D4d).
-/
import Sundogcert.OMinimalNormal

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalAbstract.Fml

variable {S : OMinStructure} {A R : Set (Fin 2 → ℝ)}

/-! ### Local helpers -/

private theorem pairEta (f : Fin 2 → ℝ) : pairFn (f 0) (f 1) = f := by
  funext k
  fin_cases k <;> simp [pairFn]

private theorem compPairB {n : ℕ} (h : Fin n → ℝ) (i j : Fin n) :
    h ∘ ![i, j] = pairFn (h i) (h j) := by
  funext k
  fin_cases k <;> simp [pairFn, Function.comp]

private theorem bs2_0 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem bsL2 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 1 = z := by simp [Fin.snoc]

private theorem bs3_0 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem bs3_1 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem bsL3 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 2 = z := by simp [Fin.snoc]

private theorem bs4_0 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem bs4_1 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem bs4_2 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 2 = h 2 := by simp [Fin.snoc]

private theorem bsL4 (h : Fin 3 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 4 → ℝ) 3 = z := by simp [Fin.snoc]

attribute [local simp] bs2_0 bsL2 bs3_0 bs3_1 bsL3 bs4_0 bs4_1 bs4_2 bsL4

/-! ### The generic definable selector -/

open Classical in
-- Totalize a relation by choice, default 0 off-domain.
noncomputable def selFn (R : Set (Fin 2 → ℝ)) (a : ℝ) : ℝ :=
  if h : ∃ z, pairFn a z ∈ R then h.choose else 0

/-- A relation is functional when second coordinates agree over each first coordinate. -/
def IsFunctional (R : Set (Fin 2 → ℝ)) : Prop :=
  ∀ a z z' : ℝ, pairFn a z ∈ R → pairFn a z' ∈ R → z = z'

theorem selFn_mem {a : ℝ} (h : ∃ z, pairFn a z ∈ R) : pairFn a (selFn R a) ∈ R := by
  rw [selFn, dif_pos h]
  exact h.choose_spec

theorem selFn_eq (hf : IsFunctional R) {a z : ℝ} (hz : pairFn a z ∈ R) : selFn R a = z :=
  hf a _ _ (selFn_mem ⟨z, hz⟩) hz

/-- **The selector engine**: a definable functional relation totalizes to a definable
function — proved once, instantiated for every β-machinery function below. -/
theorem definableFun_selFn (hR : S.Definable R) (hf : IsFunctional R) :
    S.DefinableFun (selFn R) := by
  have h := Fml.definable (((Fml.ex (Fml.atom ![0, 2] hR)).and (Fml.atom id hR)).or
    ((Fml.not (Fml.ex (Fml.atom ![0, 2] hR))).and (eqConstAt 1 0)))
  have e : {f : Fin 2 → ℝ | (((Fml.ex (Fml.atom ![0, 2] hR)).and (Fml.atom id hR)).or
      ((Fml.not (Fml.ex (Fml.atom ![0, 2] hR))).and (eqConstAt 1 0))).eval f}
      = {h : Fin 2 → ℝ | selFn R (h 0) = h 1} := by
    ext f
    simp only [Set.mem_setOf_eq, eval_or, Fml.eval, eval_eqConstAt, compPairB,
      Function.comp_id, bs3_0, bsL3]
    constructor
    · rintro (⟨_, hmem⟩ | ⟨hnex, hz0⟩)
      · exact selFn_eq hf (by rw [pairEta]; exact hmem)
      · rw [selFn, dif_neg hnex]
        exact hz0.symm
    · intro heq
      by_cases hex : ∃ z, pairFn (f 0) z ∈ R
      · refine Or.inl ⟨hex, ?_⟩
        have hm := selFn_mem hex
        rw [heq, pairEta] at hm
        exact hm
      · refine Or.inr ⟨hex, ?_⟩
        rw [← heq, selFn, dif_neg hex]
  rwa [e] at h

/-! ### Bounds from ray-normality -/

theorem notNormal_bddBelow {a : ℝ} (h : NormalBot A a) :
    BddBelow {b : ℝ | ¬ Normal A a b} := by
  obtain ⟨u, w, p, ⟨hua, haw⟩, hray⟩ := h
  refine ⟨p, fun b hb => ?_⟩
  by_contra hbp
  rw [not_le] at hbp
  apply hb
  obtain ⟨b', hb'⟩ := exists_lt b
  exact ⟨u, w, b', p, ⟨⟨hua, haw⟩, hb', hbp⟩,
    Or.inl (fun x y hxy => hray x hxy.1 y hxy.2.2)⟩

theorem notNormal_bddAbove {a : ℝ} (h : NormalTop A a) :
    BddAbove {b : ℝ | ¬ Normal A a b} := by
  obtain ⟨u, w, q, ⟨hua, haw⟩, hray⟩ := h
  refine ⟨q, fun b hb => ?_⟩
  by_contra hbq
  rw [not_le] at hbq
  apply hb
  obtain ⟨b', hb'⟩ := exists_gt b
  exact ⟨u, w, q, b', ⟨⟨hua, haw⟩, hbq, hb'⟩,
    Or.inl (fun x y hxy => hray x hxy.1 y hxy.2.1)⟩

/-! ### The least non-normal height -/

/-- The graph of "z is the least non-normal height above a". -/
def leastBadSet (A : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {h : Fin 2 → ℝ | ¬ Normal A (h 0) (h 1) ∧ ∀ z' : ℝ, z' < h 1 → Normal A (h 0) z'}

@[simp] theorem mem_leastBadSet {a z : ℝ} : pairFn a z ∈ leastBadSet A ↔
    (¬ Normal A a z ∧ ∀ z' : ℝ, z' < z → Normal A a z') := by
  simp [leastBadSet]

theorem leastBad_functional : IsFunctional (leastBadSet A) := by
  intro a z z' hz hz'
  rw [mem_leastBadSet] at hz hz'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hz.1 (hz'.2 z h)
  · exact hz'.1 (hz.2 z' h)

theorem definable_leastBadSet (hA : S.Definable A) : S.Definable (leastBadSet A) := by
  have h := Fml.definable ((Fml.atom id (definable_notNormal hA)).and
    (Fml.all ((ltAt 2 1).imp (Fml.atom ![0, 2] (definable_normal hA)))))
  have e : {f : Fin 2 → ℝ | ((Fml.atom id (definable_notNormal hA)).and
      (Fml.all ((ltAt 2 1).imp (Fml.atom ![0, 2] (definable_normal hA))))).eval f}
      = leastBadSet A := by
    ext f
    simp [leastBadSet, Fml.eval, compPairB]
  rwa [e] at h

/-- Existence of the least non-normal height: the not-normal set is closed (D4a),
nonempty, and bounded below (bottom-ray normality). -/
theorem leastBad_exists {a : ℝ} (hbot : NormalBot A a) (hbad : ∃ b, ¬ Normal A a b) :
    ∃ z, pairFn a z ∈ leastBadSet A := by
  have hcl := notNormal_slice_isClosed (A := A) a
  have hbdd := notNormal_bddBelow hbot
  have hmem := hcl.csInf_mem hbad hbdd
  refine ⟨sInf {b : ℝ | ¬ Normal A a b}, ?_⟩
  rw [mem_leastBadSet]
  refine ⟨hmem, fun z' hz' => ?_⟩
  by_contra hz'bad
  exact absurd (csInf_le hbdd hz'bad) (not_le.mpr hz')

/-- The least non-normal height, totalized. -/
noncomputable def betaFn (A : Set (Fin 2 → ℝ)) : ℝ → ℝ := selFn (leastBadSet A)

theorem definableFun_betaFn (hA : S.Definable A) : S.DefinableFun (betaFn A) :=
  definableFun_selFn (definable_leastBadSet hA) leastBad_functional

theorem betaFn_mem {a : ℝ} (hbot : NormalBot A a) (hbad : ∃ b, ¬ Normal A a b) :
    pairFn a (betaFn A a) ∈ leastBadSet A :=
  selFn_mem (leastBad_exists hbot hbad)

/-! ### Fiber max and min (for the ±∞-ray kills) -/

/-- The graph of "z is the largest fiber point above a". -/
def fiberMaxSet (A : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {h : Fin 2 → ℝ | pairFn (h 0) (h 1) ∈ A ∧
    ∀ y : ℝ, pairFn (h 0) y ∈ A → ¬ (h 1 < y)}

/-- The graph of "z is the smallest fiber point above a". -/
def fiberMinSet (A : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {h : Fin 2 → ℝ | pairFn (h 0) (h 1) ∈ A ∧
    ∀ y : ℝ, pairFn (h 0) y ∈ A → ¬ (y < h 1)}

@[simp] theorem mem_fiberMaxSet {a z : ℝ} : pairFn a z ∈ fiberMaxSet A ↔
    (pairFn a z ∈ A ∧ ∀ y : ℝ, pairFn a y ∈ A → ¬ (z < y)) := by
  simp [fiberMaxSet]

@[simp] theorem mem_fiberMinSet {a z : ℝ} : pairFn a z ∈ fiberMinSet A ↔
    (pairFn a z ∈ A ∧ ∀ y : ℝ, pairFn a y ∈ A → ¬ (y < z)) := by
  simp [fiberMinSet]

theorem fiberMax_functional : IsFunctional (fiberMaxSet A) := by
  intro a z z' hz hz'
  rw [mem_fiberMaxSet] at hz hz'
  exact le_antisymm (not_lt.mp (hz'.2 z hz.1)) (not_lt.mp (hz.2 z' hz'.1))

theorem fiberMin_functional : IsFunctional (fiberMinSet A) := by
  intro a z z' hz hz'
  rw [mem_fiberMinSet] at hz hz'
  exact le_antisymm (not_lt.mp (hz.2 z' hz'.1)) (not_lt.mp (hz'.2 z hz.1))

theorem definable_fiberMaxSet (hA : S.Definable A) : S.Definable (fiberMaxSet A) := by
  have h := Fml.definable ((Fml.atom id hA).and
    (Fml.all ((Fml.atom ![0, 2] hA).imp (Fml.not (ltAt 1 2)))))
  have e : {f : Fin 2 → ℝ | ((Fml.atom id hA).and
      (Fml.all ((Fml.atom ![0, 2] hA).imp (Fml.not (ltAt 1 2))))).eval f}
      = fiberMaxSet A := by
    ext f
    simp [fiberMaxSet, Fml.eval, compPairB, pairEta]
  rwa [e] at h

theorem definable_fiberMinSet (hA : S.Definable A) : S.Definable (fiberMinSet A) := by
  have h := Fml.definable ((Fml.atom id hA).and
    (Fml.all ((Fml.atom ![0, 2] hA).imp (Fml.not (ltAt 2 1)))))
  have e : {f : Fin 2 → ℝ | ((Fml.atom id hA).and
      (Fml.all ((Fml.atom ![0, 2] hA).imp (Fml.not (ltAt 2 1))))).eval f}
      = fiberMinSet A := by
    ext f
    simp [fiberMinSet, Fml.eval, compPairB, pairEta]
  rwa [e] at h

theorem fiberMax_exists {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : {y : ℝ | pairFn a y ∈ A}.Nonempty) : ∃ z, pairFn a z ∈ fiberMaxSet A := by
  have hFne : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr hne
  refine ⟨hfin.toFinset.max' hFne, ?_⟩
  rw [mem_fiberMaxSet]
  constructor
  · have hm := hfin.toFinset.max'_mem hFne
    rwa [Set.Finite.mem_toFinset] at hm
  · intro y hy
    exact not_lt.mpr (hfin.toFinset.le_max' y (by rwa [Set.Finite.mem_toFinset]))

theorem fiberMin_exists {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : {y : ℝ | pairFn a y ∈ A}.Nonempty) : ∃ z, pairFn a z ∈ fiberMinSet A := by
  have hFne : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr hne
  refine ⟨hfin.toFinset.min' hFne, ?_⟩
  rw [mem_fiberMinSet]
  constructor
  · have hm := hfin.toFinset.min'_mem hFne
    rwa [Set.Finite.mem_toFinset] at hm
  · intro y hy
    exact not_lt.mpr (hfin.toFinset.min'_le y (by rwa [Set.Finite.mem_toFinset]))

/-- The fiber max, totalized. -/
noncomputable def maxFn (A : Set (Fin 2 → ℝ)) : ℝ → ℝ := selFn (fiberMaxSet A)

/-- The fiber min, totalized. -/
noncomputable def minFn (A : Set (Fin 2 → ℝ)) : ℝ → ℝ := selFn (fiberMinSet A)

theorem definableFun_maxFn (hA : S.Definable A) : S.DefinableFun (maxFn A) :=
  definableFun_selFn (definable_fiberMaxSet hA) fiberMax_functional

theorem definableFun_minFn (hA : S.Definable A) : S.DefinableFun (minFn A) :=
  definableFun_selFn (definable_fiberMinSet hA) fiberMin_functional

theorem maxFn_mem {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : {y : ℝ | pairFn a y ∈ A}.Nonempty) : pairFn a (maxFn A a) ∈ fiberMaxSet A :=
  selFn_mem (fiberMax_exists hfin hne)

theorem minFn_mem {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : {y : ℝ | pairFn a y ∈ A}.Nonempty) : pairFn a (minFn A a) ∈ fiberMinSet A :=
  selFn_mem (fiberMin_exists hfin hne)

/-! ### The fiber neighbors of β -/

/-- The graph of "z is the largest fiber point strictly below `β`". -/
def maxBelowSet (A : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {h : Fin 2 → ℝ | pairFn (h 0) (h 1) ∈ A ∧ ∃ t : ℝ, (betaFn A (h 0) = t ∧
    ((h 1) < t ∧ ∀ y : ℝ, ((pairFn (h 0) y ∈ A ∧ y < t) → ¬ ((h 1) < y))))}

/-- The graph of "z is the smallest fiber point strictly above `β`". -/
def minAboveSet (A : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) :=
  {h : Fin 2 → ℝ | pairFn (h 0) (h 1) ∈ A ∧ ∃ t : ℝ, (betaFn A (h 0) = t ∧
    (t < (h 1) ∧ ∀ y : ℝ, ((pairFn (h 0) y ∈ A ∧ t < y) → ¬ (y < (h 1)))))}

@[simp] theorem mem_maxBelowSet {a z : ℝ} : pairFn a z ∈ maxBelowSet A ↔
    (pairFn a z ∈ A ∧ (z < betaFn A a ∧
      ∀ y : ℝ, ((pairFn a y ∈ A ∧ y < betaFn A a) → ¬ (z < y)))) := by
  simp [maxBelowSet]

@[simp] theorem mem_minAboveSet {a z : ℝ} : pairFn a z ∈ minAboveSet A ↔
    (pairFn a z ∈ A ∧ (betaFn A a < z ∧
      ∀ y : ℝ, ((pairFn a y ∈ A ∧ betaFn A a < y) → ¬ (y < z)))) := by
  simp [minAboveSet]

theorem maxBelow_functional : IsFunctional (maxBelowSet A) := by
  intro a z z' hz hz'
  rw [mem_maxBelowSet] at hz hz'
  exact le_antisymm (not_lt.mp (hz'.2.2 z ⟨hz.1, hz.2.1⟩))
    (not_lt.mp (hz.2.2 z' ⟨hz'.1, hz'.2.1⟩))

theorem minAbove_functional : IsFunctional (minAboveSet A) := by
  intro a z z' hz hz'
  rw [mem_minAboveSet] at hz hz'
  exact le_antisymm (not_lt.mp (hz.2.2 z' ⟨hz'.1, hz'.2.1⟩))
    (not_lt.mp (hz'.2.2 z ⟨hz.1, hz.2.1⟩))

theorem definable_maxBelowSet (hA : S.Definable A) : S.Definable (maxBelowSet A) := by
  have hG := definableFun_betaFn hA
  have h := Fml.definable ((Fml.atom id hA).and (Fml.ex ((Fml.atom ![0, 2] hG).and
    ((ltAt 1 2).and (Fml.all (((Fml.atom ![0, 3] hA).and (ltAt 3 2)).imp
      (Fml.not (ltAt 1 3))))))))
  have e : {f : Fin 2 → ℝ | ((Fml.atom id hA).and (Fml.ex ((Fml.atom ![0, 2] hG).and
      ((ltAt 1 2).and (Fml.all (((Fml.atom ![0, 3] hA).and (ltAt 3 2)).imp
        (Fml.not (ltAt 1 3)))))))).eval f}
      = maxBelowSet A := by
    ext f
    simp [maxBelowSet, Fml.eval, compPairB, pairEta]
  rwa [e] at h

theorem definable_minAboveSet (hA : S.Definable A) : S.Definable (minAboveSet A) := by
  have hG := definableFun_betaFn hA
  have h := Fml.definable ((Fml.atom id hA).and (Fml.ex ((Fml.atom ![0, 2] hG).and
    ((ltAt 2 1).and (Fml.all (((Fml.atom ![0, 3] hA).and (ltAt 2 3)).imp
      (Fml.not (ltAt 3 1))))))))
  have e : {f : Fin 2 → ℝ | ((Fml.atom id hA).and (Fml.ex ((Fml.atom ![0, 2] hG).and
      ((ltAt 2 1).and (Fml.all (((Fml.atom ![0, 3] hA).and (ltAt 2 3)).imp
        (Fml.not (ltAt 3 1)))))))).eval f}
      = minAboveSet A := by
    ext f
    simp [minAboveSet, Fml.eval, compPairB, pairEta]
  rwa [e] at h

theorem maxBelow_exists {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : ∃ y, pairFn a y ∈ A ∧ y < betaFn A a) :
    ∃ z, pairFn a z ∈ maxBelowSet A := by
  have hfin' : ({y : ℝ | pairFn a y ∈ A} ∩ Set.Iio (betaFn A a)).Finite :=
    hfin.inter_of_left _
  have hne' : ({y : ℝ | pairFn a y ∈ A} ∩ Set.Iio (betaFn A a)).Nonempty := by
    obtain ⟨y, h1, h2⟩ := hne
    exact ⟨y, h1, h2⟩
  have hFne : hfin'.toFinset.Nonempty := hfin'.toFinset_nonempty.mpr hne'
  refine ⟨hfin'.toFinset.max' hFne, ?_⟩
  rw [mem_maxBelowSet]
  have hm := hfin'.toFinset.max'_mem hFne
  rw [Set.Finite.mem_toFinset] at hm
  refine ⟨hm.1, hm.2, ?_⟩
  intro y hy
  exact not_lt.mpr (hfin'.toFinset.le_max' y (by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hy.1, hy.2⟩))

theorem minAbove_exists {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : ∃ y, pairFn a y ∈ A ∧ betaFn A a < y) :
    ∃ z, pairFn a z ∈ minAboveSet A := by
  have hfin' : ({y : ℝ | pairFn a y ∈ A} ∩ Set.Ioi (betaFn A a)).Finite :=
    hfin.inter_of_left _
  have hne' : ({y : ℝ | pairFn a y ∈ A} ∩ Set.Ioi (betaFn A a)).Nonempty := by
    obtain ⟨y, h1, h2⟩ := hne
    exact ⟨y, h1, h2⟩
  have hFne : hfin'.toFinset.Nonempty := hfin'.toFinset_nonempty.mpr hne'
  refine ⟨hfin'.toFinset.min' hFne, ?_⟩
  rw [mem_minAboveSet]
  have hm := hfin'.toFinset.min'_mem hFne
  rw [Set.Finite.mem_toFinset] at hm
  refine ⟨hm.1, hm.2, ?_⟩
  intro y hy
  exact not_lt.mpr (hfin'.toFinset.min'_le y (by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hy.1, hy.2⟩))

/-- The largest fiber point below `β`, totalized. -/
noncomputable def betaMinusFn (A : Set (Fin 2 → ℝ)) : ℝ → ℝ := selFn (maxBelowSet A)

/-- The smallest fiber point above `β`, totalized. -/
noncomputable def betaPlusFn (A : Set (Fin 2 → ℝ)) : ℝ → ℝ := selFn (minAboveSet A)

theorem definableFun_betaMinusFn (hA : S.Definable A) :
    S.DefinableFun (betaMinusFn A) :=
  definableFun_selFn (definable_maxBelowSet hA) maxBelow_functional

theorem definableFun_betaPlusFn (hA : S.Definable A) :
    S.DefinableFun (betaPlusFn A) :=
  definableFun_selFn (definable_minAboveSet hA) minAbove_functional

theorem betaMinusFn_mem {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : ∃ y, pairFn a y ∈ A ∧ y < betaFn A a) :
    pairFn a (betaMinusFn A a) ∈ maxBelowSet A :=
  selFn_mem (maxBelow_exists hfin hne)

theorem betaPlusFn_mem {a : ℝ} (hfin : {y : ℝ | pairFn a y ∈ A}.Finite)
    (hne : ∃ y, pairFn a y ∈ A ∧ betaFn A a < y) :
    pairFn a (betaPlusFn A a) ∈ minAboveSet A :=
  selFn_mem (minAbove_exists hfin hne)

/-! ### The bad sets are tame -/

/-- **The finite-height bad set is tame.** -/
theorem tame_badFin (hA : S.Definable A) : Tame {a : ℝ | ∃ b, ¬ Normal A a b} := by
  have h := Fml.tame_one (S := S) (Fml.ex (Fml.atom id (definable_notNormal hA)))
  have e : {a : ℝ | ∃ b, ¬ Normal A a b}
      = {x : ℝ | (Fml.ex (Fml.atom id (definable_notNormal hA))).eval (fun _ => x)} := by
    ext a
    simp [Fml.eval]
  rw [e]
  exact h

theorem tame_notNormalTop (hA : S.Definable A) : Tame {a : ℝ | ¬ NormalTop A a} := by
  have h := tame_compl (tame_normalTop hA)
  have e : {a : ℝ | NormalTop A a}ᶜ = {a : ℝ | ¬ NormalTop A a} := rfl
  rwa [e] at h

theorem tame_notNormalBot (hA : S.Definable A) : Tame {a : ℝ | ¬ NormalBot A a} := by
  have h := tame_compl (tame_normalBot hA)
  have e : {a : ℝ | NormalBot A a}ᶜ = {a : ℝ | ¬ NormalBot A a} := rfl
  rwa [e] at h

end Sundog.OMinimalAbstract
