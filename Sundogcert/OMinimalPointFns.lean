/-
# O-min lane R4-D2: the dichotomy kill, and the definable k-th point functions.

**The dichotomy (`exists_interval_in_countSet`)** — the scout's new argument, machine-checked:
for definable `A` with all fibers finite and unbounded fiber sizes, *every* counting set
contains an interval. Either `B_k` is infinite (C1a's interval extraction, fifth use), or the
whole tail `B_{k'} (k' ≥ k)` is finite — and then the weakly decreasing cardinalities
stabilize, forcing the chain to stabilize *as sets* (`eq_of_subset_of_ncard_le`), giving one
point in every `B_{k'}` — an infinite fiber, contradiction.

**The point functions** — `nthFn A j x` = the `(j+1)`-th smallest fiber point (0-indexed),
totalized by 0. The exact-rank relation `IsNth A j x z` (member + exactly `j` points below,
via the `BelowCount` mirror of D1's counting recursion) is: *unique* (a lower rank point below
a higher one manufactures one extra below-witness), *exists* on finite fibers with enough
points (min-peeling induction, with the fiber's `min'` above the previous rank point), and its
totalized graph is **definable** (`definableFun_nthFn`) — so the Monotonicity Theorem applies
to every rank function in D3.

**Honest fence.** D2 only: no curves (D3), no wall (D4).
-/
import Sundogcert.OMinimalCounting

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalAbstract.Fml

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### The chain, transitively -/

theorem countSet_anti_le (A : Set (Fin 2 → ℝ)) {k k' : ℕ} (h : k ≤ k') :
    countSet A k' ⊆ countSet A k := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact fun x hx => ih (countSet_anti A _ hx)

/-! ### The dichotomy kill -/

/-- **The dichotomy (D2 core).** All fibers finite + all counting sets nonempty ⇒ every
counting set contains an interval: an infinite `B_k` yields one directly; a finite `B_k`
makes the tail's cardinalities stabilize, the chain stabilize as sets, and one point lie in
every `B_{k'}` — an infinite fiber. -/
theorem exists_interval_in_countSet (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite)
    (hne : ∀ k : ℕ, (countSet A k).Nonempty) (k : ℕ) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ countSet A k := by
  by_cases hinf : (countSet A k).Infinite
  · exact tame_infinite_contains_Ioo (tame_countSet hA k) hinf
  · exfalso
    rw [Set.not_infinite] at hinf
    have htail : ∀ j : ℕ, (countSet A (k + j)).Finite :=
      fun j => hinf.subset (countSet_anti_le A (Nat.le_add_right k j))
    have hrne : (Set.range fun j : ℕ => (countSet A (k + j)).ncard).Nonempty :=
      ⟨_, Set.mem_range_self 0⟩
    obtain ⟨j₀, hj₀⟩ := Nat.sInf_mem hrne
    have hj₀' : (countSet A (k + j₀)).ncard
        = sInf (Set.range fun j : ℕ => (countSet A (k + j)).ncard) := hj₀
    obtain ⟨x, hx⟩ := hne (k + j₀)
    have hall : ∀ K : ℕ, x ∈ countSet A K := by
      intro K
      rcases le_or_gt K (k + j₀) with h | h
      · exact countSet_anti_le A h hx
      · have hKk : k ≤ K := le_trans (Nat.le_add_right k j₀) h.le
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hKk
        have hsub : countSet A (k + j) ⊆ countSet A (k + j₀) :=
          countSet_anti_le A (by omega)
        have h2 : sInf (Set.range fun j : ℕ => (countSet A (k + j)).ncard)
            ≤ (countSet A (k + j)).ncard := Nat.sInf_le ⟨j, rfl⟩
        have heq : countSet A (k + j) = countSet A (k + j₀) :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hj₀']; exact h2) (htail j₀)
        rw [heq]
        exact hx
    exact infinite_fiber_of_mem_all hall (hfib x)

/-! ### The below-count mirror -/

/-- `≥ k` fiber points strictly below `t` (mirror of `AboveCount`). -/
def BelowCount (A : Set (Fin 2 → ℝ)) (x : ℝ) : ℝ → ℕ → Prop
  | _, 0 => True
  | t, k + 1 => ∃ y, y < t ∧ pairFn x y ∈ A ∧ BelowCount A x y k

private theorem comp02' (g : Fin 2 → ℝ) (y : ℝ) :
    ((Fin.snoc g y : Fin 3 → ℝ) ∘ ![0, 2]) = pairFn (g 0) y := by
  funext k
  fin_cases k <;> simp [pairFn, Fin.snoc, Function.comp]

private theorem snocD' (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocE' (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 2 = y := by
  simp [Fin.snoc]

/-- The below-counting formula, slots `(x = 0, t = 1)`. -/
def ltCount (hA : S.Definable A) : ℕ → Fml S 2
  | 0 => .tru
  | k + 1 => .ex ((ltAt 2 1).and ((Fml.atom ![0, 2] hA).and
      (Fml.reindex ![0, 2] (ltCount hA k))))

theorem eval_ltCount (hA : S.Definable A) : ∀ (k : ℕ) (g : Fin 2 → ℝ),
    (ltCount hA k).eval g ↔ BelowCount A (g 0) (g 1) k := by
  intro k
  induction k with
  | zero =>
    intro g
    simp [ltCount, BelowCount]
  | succ k ih =>
    intro g
    simp only [ltCount, Fml.eval, eval_ltAt, Fml.eval_reindex, comp02', snocD', snocE',
      pairFn_zero, pairFn_one, ih, BelowCount]

/-- Build `BelowCount` from a finite witness set by `max'`-peeling. -/
theorem belowCount_of_finset {x : ℝ} : ∀ (k : ℕ) (Y : Finset ℝ), Y.card = k →
    (∀ y ∈ Y, pairFn x y ∈ A) → ∀ t : ℝ, (∀ y ∈ Y, y < t) → BelowCount A x t k := by
  intro k
  induction k with
  | zero =>
    intro Y _ _ t _
    trivial
  | succ k ih =>
    intro Y hcard hmem t habove
    have hne : Y.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    refine ⟨Y.max' hne, habove _ (Y.max'_mem hne), hmem _ (Y.max'_mem hne), ?_⟩
    apply ih (Y.erase (Y.max' hne))
    · rw [Finset.card_erase_of_mem (Y.max'_mem hne), hcard]
      omega
    · intro y hy
      exact hmem y (Finset.mem_of_mem_erase hy)
    · intro y hy
      have h1 := Y.le_max' y (Finset.mem_of_mem_erase hy)
      have h2 := (Finset.mem_erase.mp hy).1
      exact lt_of_le_of_ne h1 h2

/-- Extract a `k`-element witness set below `t`. -/
theorem belowCount_exists_finset {x : ℝ} : ∀ {k : ℕ} {t : ℝ}, BelowCount A x t k →
    ∃ Y : Finset ℝ, Y.card = k ∧ ∀ y ∈ Y, y < t ∧ pairFn x y ∈ A := by
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
        exact ⟨lt_trans hz1 h1, hz2⟩

/-! ### The exact-rank relation -/

/-- `z` is the `(j+1)`-th smallest fiber point of `A` above `x` (0-indexed rank `j`):
a member with exactly `j` points below it. -/
def IsNth (A : Set (Fin 2 → ℝ)) (j : ℕ) (x z : ℝ) : Prop :=
  pairFn x z ∈ A ∧ BelowCount A x z j ∧ ¬ BelowCount A x z (j + 1)

theorem isNth_unique {x : ℝ} {j : ℕ} {z z' : ℝ}
    (h : IsNth A j x z) (h' : IsNth A j x z') : z = z' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2.2 ⟨z, hlt, h.1, h.2.1⟩
  · exact h.2.2 ⟨z', hlt, h'.1, h'.2.1⟩

/-- Existence on finite fibers with enough points: min-peeling above the previous rank. -/
theorem isNth_exists {x : ℝ} (hfin : {y : ℝ | pairFn x y ∈ A}.Finite) :
    ∀ (j : ℕ) (Y : Finset ℝ), Y.card = j + 1 → (∀ y ∈ Y, pairFn x y ∈ A) →
    ∃ z, IsNth A j x z := by
  intro j
  induction j with
  | zero =>
    intro Y hcard hmem
    have hne : {y : ℝ | pairFn x y ∈ A}.Nonempty := by
      have hYne : Y.Nonempty := by
        rw [← Finset.card_pos, hcard]
        omega
      obtain ⟨y, hy⟩ := hYne
      exact ⟨y, hmem y hy⟩
    have hFne : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr hne
    refine ⟨hfin.toFinset.min' hFne, ?_, trivial, ?_⟩
    · have hm := hfin.toFinset.min'_mem hFne
      rwa [Set.Finite.mem_toFinset] at hm
    · rintro ⟨y, hy1, hy2, -⟩
      have hle : hfin.toFinset.min' hFne ≤ y :=
        hfin.toFinset.min'_le y (by rwa [Set.Finite.mem_toFinset])
      linarith
  | succ j ih =>
    intro Y hcard hmem
    obtain ⟨Y', hY'sub, hY'card⟩ := Finset.exists_subset_card_eq (s := Y) (n := j + 1) (by omega)
    obtain ⟨zj, hzj⟩ := ih Y' hY'card (fun y hy => hmem y (hY'sub hy))
    have habove : ∃ w ∈ Y, zj < w := by
      by_contra hno
      simp only [not_exists, not_and, not_lt] at hno
      have hsubE : ∀ w ∈ Y.erase zj, w < zj := fun w hw =>
        lt_of_le_of_ne (hno w (Finset.mem_of_mem_erase hw)) (Finset.mem_erase.mp hw).1
      have hcardE : j + 1 ≤ (Y.erase zj).card := by
        have := Finset.pred_card_le_card_erase (s := Y) (a := zj)
        omega
      obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hcardE
      exact hzj.2.2 (belowCount_of_finset _ W hWcard
        (fun w hw => hmem w (Finset.mem_of_mem_erase (hWsub hw))) zj
        (fun w hw => hsubE w (hWsub hw)))
    have hAfin : ({y : ℝ | pairFn x y ∈ A} ∩ Set.Ioi zj).Finite := hfin.inter_of_left _
    have hAne : ({y : ℝ | pairFn x y ∈ A} ∩ Set.Ioi zj).Nonempty := by
      obtain ⟨w, hwY, hzw⟩ := habove
      exact ⟨w, hmem w hwY, hzw⟩
    have hFne2 : hAfin.toFinset.Nonempty := hAfin.toFinset_nonempty.mpr hAne
    have hzmem : hAfin.toFinset.min' hFne2 ∈ {y : ℝ | pairFn x y ∈ A} ∩ Set.Ioi zj := by
      have hm := hAfin.toFinset.min'_mem hFne2
      rwa [Set.Finite.mem_toFinset] at hm
    have hgap : ∀ w, pairFn x w ∈ A → zj < w → hAfin.toFinset.min' hFne2 ≤ w :=
      fun w h1 h2 => hAfin.toFinset.min'_le w (by
        rw [Set.Finite.mem_toFinset]
        exact ⟨h1, h2⟩)
    refine ⟨hAfin.toFinset.min' hFne2, hzmem.1, ⟨zj, hzmem.2, hzj.1, hzj.2.1⟩, ?_⟩
    rintro hbc
    obtain ⟨W, hWcard, hW⟩ := belowCount_exists_finset hbc
    have hWle : ∀ w ∈ W, w ≤ zj := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hW w hw
      by_contra hgt
      rw [not_le] at hgt
      exact absurd (hgap w hw2 hgt) (not_le.mpr hw1)
    have hsubE : ∀ w ∈ W.erase zj, w < zj := fun w hw =>
      lt_of_le_of_ne (hWle w (Finset.mem_of_mem_erase hw)) (Finset.mem_erase.mp hw).1
    have hcardE : j + 1 ≤ (W.erase zj).card := by
      have := Finset.pred_card_le_card_erase (s := W) (a := zj)
      omega
    obtain ⟨V, hVsub, hVcard⟩ := Finset.exists_subset_card_eq hcardE
    exact hzj.2.2 (belowCount_of_finset _ V hVcard
      (fun w hw => (hW w (Finset.mem_of_mem_erase (hVsub hw))).2) zj
      (fun w hw => hsubE w (hVsub hw)))

/-! ### The totalized rank functions and their definability -/

open Classical in
/-- The `(j+1)`-th smallest fiber point, totalized by `0`. -/
noncomputable def nthFn (A : Set (Fin 2 → ℝ)) (j : ℕ) (x : ℝ) : ℝ :=
  if h : ∃ z, IsNth A j x z then h.choose else 0

theorem nthFn_isNth {x : ℝ} {j : ℕ} (h : ∃ z, IsNth A j x z) :
    IsNth A j x (nthFn A j x) := by
  rw [nthFn, dif_pos h]
  exact h.choose_spec

theorem nthFn_eq {x z : ℝ} {j : ℕ} (hz : IsNth A j x z) : nthFn A j x = z :=
  isNth_unique (nthFn_isNth ⟨z, hz⟩) hz

/-- Every point of `Fin 2 → ℝ` is the pair of its coordinates. -/
private theorem pairFn_eta (h : Fin 2 → ℝ) : pairFn (h 0) (h 1) = h := by
  funext k
  fin_cases k <;> simp [pairFn]

/-- The exact-rank formula, slots `(x = 0, z = 1)`. -/
private def nthFml (hA : S.Definable A) (j : ℕ) : Fml S 2 :=
  (Fml.atom id hA).and ((ltCount hA j).and (.not (ltCount hA (j + 1))))

private theorem eval_nthFml (hA : S.Definable A) (j : ℕ) (h : Fin 2 → ℝ) :
    (nthFml hA j).eval h ↔ IsNth A j (h 0) (h 1) := by
  simp only [nthFml, Fml.eval, eval_ltCount, IsNth, Function.comp_id, pairFn_eta]

/-- `∃ z, IsNth j x z`, slots `(x = 0, z = 1)` (the `z`-slot is ignored). -/
private def exNthFml (hA : S.Definable A) (j : ℕ) : Fml S 2 :=
  .ex (Fml.reindex ![0, 2] (nthFml hA j))

private theorem eval_exNthFml (hA : S.Definable A) (j : ℕ) (h : Fin 2 → ℝ) :
    (exNthFml hA j).eval h ↔ ∃ z, IsNth A j (h 0) z := by
  simp only [exNthFml, Fml.eval, Fml.eval_reindex, comp02', eval_nthFml,
    pairFn_zero, pairFn_one]

/-- **The rank functions are definable** — so the Monotonicity Theorem applies to each. -/
theorem definableFun_nthFn (hA : S.Definable A) (j : ℕ) :
    S.DefinableFun (nthFn A j) := by
  have h := Fml.definable (S := S)
    (((exNthFml hA j).and (nthFml hA j)).or
      ((Fml.not (exNthFml hA j)).and (eqConstAt 1 0)))
  have e : {f : Fin 2 → ℝ | Fml.eval
      (((exNthFml hA j).and (nthFml hA j)).or
        ((Fml.not (exNthFml hA j)).and (eqConstAt 1 0))) f}
      = {f : Fin 2 → ℝ | nthFn A j (f 0) = f 1} := by
    ext f
    simp only [Set.mem_setOf_eq, eval_or, Fml.eval, eval_exNthFml, eval_nthFml,
      eval_eqConstAt]
    constructor
    · rintro (⟨_, hnth⟩ | ⟨hnex, hz0⟩)
      · exact nthFn_eq hnth
      · rw [nthFn, dif_neg hnex, hz0]
    · intro heq
      by_cases hex : ∃ z, IsNth A j (f 0) z
      · exact Or.inl ⟨hex, heq ▸ nthFn_isNth hex⟩
      · refine Or.inr ⟨hex, ?_⟩
        rw [← heq, nthFn, dif_neg hex]
  rwa [e] at h

end Sundog.OMinimalAbstract
