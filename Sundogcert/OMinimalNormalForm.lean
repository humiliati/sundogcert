/-
# O-min ladder R2-N: the normal form — tame IS "finite union of points and open intervals".

The rung-1 docstring equivalence becomes a theorem: `Tame s ↔ NormalForm s`, where `NormalForm`
is the standard o-minimality normal form — a finite set of points plus finitely many open
intervals (`IsOpen ∧ OrdConnected`, so rays and `univ` are included). This is where dimension one
earns the name *o-minimal*: definable sets are not just finite-frontier, they decompose.

**⇐ (assembly).** A point set is tame (finite sets are closed with themselves as frontier); an
open interval is tame (`frontier ⊆ {sInf, sSup}` — a frontier point of an open `OrdConnected` set
is a one-sided bound lying in the closure, hence the genuine `csSup`/`csInf`; junk values are
harmless since the inclusion is what is used); finite unions close by rung 1's boolean algebra.

**⇒ (the content).** Induction on `(frontier s).ncard`, peeling the top: with `a` the largest
frontier point and `a'` the next one down, the windows `Ioo a' a` and `Ioi a` are frontier-free,
so on each `s` is full or empty (`preconnected_split` — a frontier-free preconnected window can
not separate `s`); the points `{a'}, {a}` are singleton pieces; and `s ∩ Iio a'` has strictly
smaller frontier (`frontier_inter_subset`), closing the induction. *Design note:* the
pre-registered plan was a sorted-list gap cover; this max'-peeling induction is the same argument
with no list machinery — the pre-registered falsifier `NORMAL_FORM_NEEDS_COMPONENTS` (sorted
adjacency stalls) was routed around rather than fired.

**Honest scope.** Dimension one only; the pieces are produced by an induction, not stored as a
canonical minimal decomposition (uniqueness/minimality of the decomposition is not claimed).
-/
import Sundogcert.OMinimalOne

namespace Sundog.OMinimalNormalForm

open Sundog.OMinimalOne

/-- **The o-minimality normal form**: a finite set of points plus finitely many open intervals
(open + `OrdConnected` = open interval, including rays and `univ`). -/
def NormalForm (s : Set ℝ) : Prop :=
  ∃ (P : Finset ℝ) (J : Finset (Set ℝ)),
    (∀ j ∈ J, IsOpen j ∧ j.OrdConnected) ∧ s = ↑P ∪ ⋃₀ ↑J

theorem normalForm_empty : NormalForm ∅ :=
  ⟨∅, ∅, by simp, by simp⟩

theorem normalForm_singleton (a : ℝ) : NormalForm {a} :=
  ⟨{a}, ∅, by simp, by simp⟩

theorem normalForm_interval {j : Set ℝ} (ho : IsOpen j) (hc : j.OrdConnected) : NormalForm j :=
  ⟨∅, {j}, by simp [ho, hc], by simp⟩

theorem NormalForm.union {s t : Set ℝ} (hs : NormalForm s) (ht : NormalForm t) :
    NormalForm (s ∪ t) := by
  obtain ⟨P₁, J₁, hJ₁, rfl⟩ := hs
  obtain ⟨P₂, J₂, hJ₂, rfl⟩ := ht
  classical
  refine ⟨P₁ ∪ P₂, J₁ ∪ J₂, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with h | h
    exacts [hJ₁ j h, hJ₂ j h]
  · rw [Finset.coe_union, Finset.coe_union, Set.sUnion_union]
    ext x
    simp only [Set.mem_union]
    tauto

/-! ### The two window tools -/

/-- **A frontier-free preconnected window cannot separate `s`**: on such a window, `s` is full or
empty. Direct from the `IsPreconnected` definition with `u = interior s`, `v = interior sᶜ`. -/
theorem preconnected_split {J s : Set ℝ} (hJ : IsPreconnected J)
    (hdisj : ∀ x ∈ J, x ∉ frontier s) : J ⊆ s ∨ J ∩ s = ∅ := by
  have hcov : J ⊆ interior s ∪ interior sᶜ := by
    intro x hx
    by_cases hcl : x ∈ closure s
    · left
      have hfr : x ∉ frontier s := hdisj x hx
      rw [frontier_eq_closure_inter_closure] at hfr
      have hnot : x ∉ closure sᶜ := fun hc => hfr ⟨hcl, hc⟩
      rw [closure_compl] at hnot
      simpa using hnot
    · right
      have hx' : x ∈ (closure s)ᶜ := hcl
      rwa [← interior_compl] at hx'
  by_cases h1 : (J ∩ interior s).Nonempty
  · by_cases h2 : (J ∩ interior sᶜ).Nonempty
    · exfalso
      obtain ⟨z, hzJ, hz1, hz2⟩ :=
        hJ (interior s) (interior sᶜ) isOpen_interior isOpen_interior hcov h1 h2
      exact (interior_subset hz2) (interior_subset hz1)
    · left
      intro x hx
      rcases hcov hx with h | h
      · exact interior_subset h
      · exact absurd ⟨x, hx, h⟩ h2
  · right
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxJ hxs
    rcases hcov hxJ with h | h
    · exact h1 ⟨x, hxJ, h⟩
    · exact (interior_subset h) hxs

/-- Resolve one frontier-free open-interval window against `s`: the piece `s ∩ J` is the whole
window or empty — a normal-form piece either way. -/
theorem normalForm_inter_window {s J : Set ℝ} (ho : IsOpen J) (hc : J.OrdConnected)
    (hdisj : ∀ x ∈ J, x ∉ frontier s) : NormalForm (s ∩ J) := by
  rcases preconnected_split hc.isPreconnected hdisj with h | h
  · rw [Set.inter_eq_right.mpr h]
    exact normalForm_interval ho hc
  · rw [Set.inter_comm, h]
    exact normalForm_empty

/-- A point piece is a normal-form piece. -/
theorem normalForm_inter_singleton (s : Set ℝ) (a : ℝ) : NormalForm (s ∩ {a}) := by
  by_cases h : a ∈ s
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h)]
    exact normalForm_singleton a
  · rw [Set.inter_singleton_eq_empty.mpr h]
    exact normalForm_empty

/-! ### ⇐ — normal form is tame -/

/-- A finite point set is tame (closed, own frontier). -/
theorem tame_finset (P : Finset ℝ) : Tame (↑P : Set ℝ) :=
  P.finite_toSet.subset P.finite_toSet.isClosed.frontier_subset

/-- **An open interval is tame**: a frontier point of an open `OrdConnected` set is a one-sided
bound lying in the closure, hence it *is* the `sSup` (or `sInf`) — `frontier ⊆ {sInf, sSup}`. -/
theorem tame_of_isOpen_ordConnected {j : Set ℝ} (ho : IsOpen j) (hc : j.OrdConnected) :
    Tame j := by
  have hsub : frontier j ⊆ {sInf j, sSup j} := by
    intro x hx
    rw [ho.frontier_eq] at hx
    obtain ⟨hxcl, hxj⟩ := hx
    have hjne : j.Nonempty := by
      rcases j.eq_empty_or_nonempty with rfl | h
      · simp at hxcl
      · exact h
    have hbound : (∀ y ∈ j, y ≤ x) ∨ (∀ y ∈ j, x ≤ y) := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      simp only [not_forall, not_le, exists_prop] at h1 h2
      obtain ⟨u, hu, hxu⟩ := h1
      obtain ⟨v, hv, hvx⟩ := h2
      exact hxj (hc.out hv hu ⟨hvx.le, hxu.le⟩)
    rcases hbound with hub | hlb
    · have hlub : IsLUB j x := by
        constructor
        · exact fun y hy => hub y hy
        · intro z hz
          have hsub' : closure j ⊆ Set.Iic z := closure_minimal (fun y hy => hz hy) isClosed_Iic
          exact hsub' hxcl
      have hx' := hlub.csSup_eq hjne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr hx'.symm
    · have hglb : IsGLB j x := by
        constructor
        · exact fun y hy => hlb y hy
        · intro z hz
          have hsub' : closure j ⊆ Set.Ici z := closure_minimal (fun y hy => hz hy) isClosed_Ici
          exact hsub' hxcl
      have hx' := hglb.csInf_eq hjne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl hx'.symm
  exact (Set.finite_singleton (sSup j) |>.insert (sInf j)).subset hsub

/-- Tame is closed under finite `sUnion`. -/
theorem tame_sUnion {J : Finset (Set ℝ)} (h : ∀ j ∈ J, Tame j) : Tame (⋃₀ ↑J) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp only [Finset.coe_empty, Set.sUnion_empty]; exact tame_empty
  | insert j J hjJ ih =>
    rw [Finset.coe_insert, Set.sUnion_insert]
    exact tame_union (h j (Finset.mem_insert_self j J))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **⇐ direction**: every normal-form set is tame. -/
theorem tame_of_normalForm {s : Set ℝ} (h : NormalForm s) : Tame s := by
  obtain ⟨P, J, hJ, rfl⟩ := h
  exact tame_union (tame_finset P)
    (tame_sUnion fun j hj => tame_of_isOpen_ordConnected (hJ j hj).1 (hJ j hj).2)

/-! ### ⇒ — tame sets decompose (max'-peeling induction) -/

/-- The inductive engine: a tame set with at most `n` frontier points is normal-form. Peels the
top frontier point (and its left neighbor) per step; the windows between are frontier-free. -/
private theorem normalForm_of_frontier_card :
    ∀ n : ℕ, ∀ s : Set ℝ, Tame s → (frontier s).ncard ≤ n → NormalForm s := by
  intro n
  induction n with
  | zero =>
    intro s hs hcard
    have hfr : frontier s = ∅ := (Set.ncard_eq_zero hs).mp (Nat.le_zero.mp hcard)
    rcases frontier_eq_empty_iff.mp hfr with rfl | rfl
    · exact normalForm_empty
    · exact normalForm_interval isOpen_univ Set.ordConnected_univ
  | succ n ih =>
    intro s hs hcard
    by_cases hne : frontier s = ∅
    · exact ih s hs (by simp [hne])
    · have hFin : (frontier s).Finite := hs
      have hFne : hFin.toFinset.Nonempty :=
        hFin.toFinset_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hne)
      set F := hFin.toFinset with hFdef
      set a := F.max' hFne with ha
      have haF : a ∈ frontier s := hFin.mem_toFinset.mp (F.max'_mem hFne)
      have hmax : ∀ x ∈ frontier s, x ≤ a := fun x hx =>
        F.le_max' x (hFin.mem_toFinset.mpr hx)
      -- the ray above a is frontier-free
      have wIoi : ∀ x ∈ Set.Ioi a, x ∉ frontier s := fun x hx hxfr =>
        absurd (hmax x hxfr) (not_le.mpr hx)
      by_cases hne' : (F.erase a).Nonempty
      · -- two frontier points to peel: a and its left neighbor a'
        set a' := (F.erase a).max' hne' with ha'
        have ha'F : a' ∈ F.erase a := (F.erase a).max'_mem hne'
        have ha'mem : a' ∈ frontier s := hFin.mem_toFinset.mp (Finset.mem_of_mem_erase ha'F)
        have ha'lt : a' < a :=
          lt_of_le_of_ne (hmax a' ha'mem) (Finset.mem_erase.mp ha'F).1
        have hmax' : ∀ x ∈ frontier s, x ≠ a → x ≤ a' := fun x hx hxa =>
          (F.erase a).le_max' x (Finset.mem_erase.mpr ⟨hxa, hFin.mem_toFinset.mpr hx⟩)
        -- the window between a' and a is frontier-free
        have wIoo : ∀ x ∈ Set.Ioo a' a, x ∉ frontier s := fun x hx hxfr =>
          absurd (hmax' x hxfr (ne_of_lt hx.2)) (not_le.mpr hx.1)
        -- the piece below a' is tame with strictly smaller frontier
        have hTame1 : Tame (s ∩ Set.Iio a') :=
          tame_inter hs (tame_of_isOpen_ordConnected isOpen_Iio Set.ordConnected_Iio)
        have hsub1 : frontier (s ∩ Set.Iio a') ⊆ frontier s \ {a} := by
          intro x hx
          have := frontier_inter_subset s (Set.Iio a') hx
          rcases this with h | h
          · refine ⟨h.1, ?_⟩
            have hxle : x ≤ a' := by
              have := h.2
              rw [closure_Iio] at this
              exact this
            exact fun hxa => absurd (hxa ▸ hxle) (not_le.mpr ha'lt)
          · have hxa' : x = a' := by
              have := h.2
              rw [frontier_Iio] at this
              exact this
            exact hxa' ▸ ⟨ha'mem, fun h' => absurd (h' ▸ ha'lt) (lt_irrefl a)⟩
        have hcard1 : (frontier (s ∩ Set.Iio a')).ncard ≤ n := by
          have h1 : (frontier (s ∩ Set.Iio a')).ncard ≤ (frontier s \ {a}).ncard :=
            Set.ncard_le_ncard hsub1 (hFin.diff)
          have h2 : (frontier s \ {a}).ncard = (frontier s).ncard - 1 :=
            Set.ncard_diff_singleton_of_mem haF
          have h3 : 0 < (frontier s).ncard := (Set.ncard_pos hFin).mpr ⟨a, haF⟩
          omega
        -- assemble: five pieces cover s
        have huniv : Set.Iio a' ∪ {a'} ∪ Set.Ioo a' a ∪ {a} ∪ Set.Ioi a = Set.univ := by
          ext x
          simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Ioo,
            Set.mem_Ioi, Set.mem_univ, iff_true]
          rcases lt_trichotomy x a' with h | h | h
          · tauto
          · tauto
          · rcases lt_trichotomy x a with h2 | h2 | h2 <;> tauto
        have hcover : s = s ∩ Set.Iio a' ∪ s ∩ {a'} ∪ s ∩ Set.Ioo a' a ∪ s ∩ {a}
            ∪ s ∩ Set.Ioi a := by
          rw [← Set.inter_union_distrib_left, ← Set.inter_union_distrib_left,
            ← Set.inter_union_distrib_left, ← Set.inter_union_distrib_left, huniv,
            Set.inter_univ]
        rw [hcover]
        exact ((((ih _ hTame1 hcard1).union (normalForm_inter_singleton s a')).union
          (normalForm_inter_window isOpen_Ioo Set.ordConnected_Ioo wIoo)).union
          (normalForm_inter_singleton s a)).union
          (normalForm_inter_window isOpen_Ioi Set.ordConnected_Ioi wIoi)
      · -- a is the only frontier point: both rays are frontier-free, no recursion
        have hFa : ∀ x ∈ frontier s, x = a := by
          intro x hx
          by_contra hxa
          exact hne' ⟨x, Finset.mem_erase.mpr ⟨hxa, hFin.mem_toFinset.mpr hx⟩⟩
        have wIio : ∀ x ∈ Set.Iio a, x ∉ frontier s := fun x hx hxfr =>
          absurd (hFa x hxfr) (ne_of_lt hx)
        have huniv : Set.Iio a ∪ {a} ∪ Set.Ioi a = Set.univ := by
          ext x
          simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Ioi,
            Set.mem_univ, iff_true]
          rcases lt_trichotomy x a with h | h | h <;> tauto
        have hcover : s = s ∩ Set.Iio a ∪ s ∩ {a} ∪ s ∩ Set.Ioi a := by
          rw [← Set.inter_union_distrib_left, ← Set.inter_union_distrib_left, huniv,
            Set.inter_univ]
        rw [hcover]
        exact ((normalForm_inter_window isOpen_Iio Set.ordConnected_Iio wIio).union
          (normalForm_inter_singleton s a)).union
          (normalForm_inter_window isOpen_Ioi Set.ordConnected_Ioi wIoi)

/-- **⇒ direction**: every tame set is normal-form. -/
theorem normalForm_of_tame {s : Set ℝ} (hs : Tame s) : NormalForm s :=
  normalForm_of_frontier_card (frontier s).ncard s hs le_rfl

/-- **The normal form (R2-N headline).** Tame **is** "finite union of points and open intervals"
— the dimension-one o-minimality axiom in its standard normal form, both directions. -/
theorem tame_iff_normalForm {s : Set ℝ} : Tame s ↔ NormalForm s :=
  ⟨normalForm_of_tame, tame_of_normalForm⟩

end Sundog.OMinimalNormalForm
