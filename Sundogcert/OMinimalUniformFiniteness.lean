/-
# O-min lane R4-D4d: UNIFORM FINITENESS — the Finiteness Lemma, complete.

**`uniform_finiteness`**: for definable `A ⊆ ℝ²` with every fiber finite, the fiber sizes
are uniformly bounded — van den Dries Ch. 3 (1.7), machine-checked over the abstract
`OMinStructure`. Equivalently (`exists_empty_countSet`): some counting set is empty.

The three pieces:

- **`count_locally_constant`** — at a fully normal parameter the fiber count is locally
  constant. `≥`: a min-peeling induction on the fiber Finset builds one selected point per
  fiber point in nearby columns, kept distinct by one fresh separator per step (the
  selection-continuity bracket traps each selection below its separator, the recursion
  floor keeps the rest above). `≤`: the two ray boxes cap the ends; the compact leftover
  `K = Icc \ strips` is covered by finitely many empty boxes (Heine–Borel — ℝ-specific,
  fenced exactly like C1d's countability); every remaining A-point lies in some fiber
  point's thin box, and thinness makes the assignment injective.
- **`frontier_countSet_subset`** — hence every counting set's frontier lies in the finite
  abnormal set (constant count near a good point means locally all-in or all-out).
- **The chain kill** — if sizes were unbounded, every counting set is nonempty while
  `⋂ₖ countSet A k = ∅` (D1's infinite-fiber kill). If some counting set hides inside the
  finite abnormal set, D2's dichotomy already yields an interval inside a finite set.
  Otherwise pick witnesses off the abnormal set; infinitely many share one abnormal-gap
  (pigeonhole on below-sets — sort-free), and `preconnected_split` propagates membership
  across the gap: the earliest witness lies in every counting set — an infinite fiber.

This completes R4-D: D0 slices → D1 counting → D2 dichotomy + ranks → D3 curves →
D4a–d normality/β/tube/UF.
-/
import Sundogcert.OMinimalBadFinite

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalNormalForm Sundog.OMinimalAbstract.Fml Topology

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### The `≥` half: strips by min-peeling -/

private theorem strips_lower {a : ℝ}
    (hnorm : ∀ b : ℝ, Normal A a b) :
    ∀ (n : ℕ) (F : Finset ℝ), F.card = n → (∀ y ∈ F, pairFn a y ∈ A) →
    ∀ t : ℝ, (∀ y ∈ F, t < y) →
    ∃ u w : ℝ, u < a ∧ a < w ∧ ∀ x : ℝ, u < x → x < w →
      ∃ G : Finset ℝ, G.card = n ∧ ∀ z ∈ G, pairFn x z ∈ A ∧ t < z := by
  intro n
  induction n with
  | zero =>
    intro F hcard hmem t ht
    obtain ⟨u, hu⟩ := exists_lt a
    obtain ⟨w, hw⟩ := exists_gt a
    exact ⟨u, w, hu, hw, fun x _ _ => ⟨∅, rfl, by simp⟩⟩
  | succ n ih =>
    intro F hcard hmem t ht
    have hFne : F.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    have hy₀F := F.min'_mem hFne
    -- separator above the min, below the rest
    have hsep : ∃ d₀ : ℝ, F.min' hFne < d₀ ∧ ∀ y ∈ F.erase (F.min' hFne), d₀ < y := by
      by_cases hne : (F.erase (F.min' hFne)).Nonempty
      · have hlt : F.min' hFne < (F.erase (F.min' hFne)).min' hne := by
          have h1 := F.min'_le _
            (Finset.mem_of_mem_erase ((F.erase (F.min' hFne)).min'_mem hne))
          have h2 := (Finset.mem_erase.mp ((F.erase (F.min' hFne)).min'_mem hne)).1
          exact lt_of_le_of_ne h1 (Ne.symm h2)
        obtain ⟨d₀, hd1, hd2⟩ := exists_between hlt
        exact ⟨d₀, hd1, fun y hy =>
          lt_of_lt_of_le hd2 ((F.erase (F.min' hFne)).min'_le y hy)⟩
      · obtain ⟨d₀, hd₀⟩ := exists_gt (F.min' hFne)
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨d₀, hd₀, ?_⟩
        rw [hne]
        simp
    obtain ⟨d₀, hd₀1, hd₀rest⟩ := hsep
    obtain ⟨c₀, hc₀1, hc₀2⟩ := exists_between (ht _ hy₀F)
    -- the graph box at (a, min)
    obtain ⟨u, w, p, q, ⟨⟨hua, haw⟩, hpy, hyq⟩, hbox⟩ := hnorm (F.min' hFne)
    rcases hbox with hemp | ⟨-, hthin, hcont⟩
    · exact absurd (hmem _ hy₀F) (hemp a _ ⟨⟨hua, haw⟩, hpy, hyq⟩)
    obtain ⟨u₀, w₀, ⟨hu₀a, haw₀⟩, hwin⟩ :=
      hcont a ⟨hua, haw⟩ _ ⟨⟨hpy, hyq⟩, hmem _ hy₀F⟩ c₀ d₀ ⟨hc₀2, hd₀1⟩
    obtain ⟨u₁, w₁, hu₁a, haw₁, hrec⟩ := ih (F.erase (F.min' hFne))
      (by rw [Finset.card_erase_of_mem hy₀F, hcard]; omega)
      (fun y hy => hmem y (Finset.mem_of_mem_erase hy)) d₀ hd₀rest
    refine ⟨max u (max u₀ u₁), min w (min w₀ w₁),
      max_lt hua (max_lt hu₀a hu₁a), lt_min haw (lt_min haw₀ haw₁), ?_⟩
    intro x hx1 hx2
    have hxu : u < x := lt_of_le_of_lt (le_max_left _ _) hx1
    have hxu₀ : u₀ < x :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hx1
    have hxu₁ : u₁ < x :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hx1
    have hxw : x < w := lt_of_lt_of_le hx2 (min_le_left _ _)
    have hxw₀ : x < w₀ :=
      lt_of_lt_of_le hx2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hxw₁ : x < w₁ :=
      lt_of_lt_of_le hx2 (le_trans (min_le_right _ _) (min_le_right _ _))
    obtain ⟨z, ⟨hpz, hzq⟩, hzA, -⟩ := hthin x ⟨hxu, hxw⟩
    have hzbr := hwin x ⟨⟨hxu₀, hxw₀⟩, hxu, hxw⟩ z ⟨⟨hpz, hzq⟩, hzA⟩
    obtain ⟨G, hGcard, hG⟩ := hrec x hxu₁ hxw₁
    have hznotG : z ∉ G := fun hzG => absurd (hG z hzG).2 (not_lt.mpr hzbr.2.le)
    refine ⟨insert z G, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hznotG, hGcard]
    · intro z' hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'G
      · exact ⟨hzA, lt_trans hc₀1 hzbr.1⟩
      · exact ⟨(hG z' hz'G).1,
          lt_trans (lt_trans (lt_trans hc₀1 hc₀2) hd₀1) (hG z' hz'G).2⟩

/-! ### The `≤` half: rays + compact leftover cover -/

private theorem strips_upper
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) {a : ℝ}
    (hnorm : ∀ b : ℝ, Normal A a b) (htop : NormalTop A a) (hbot : NormalBot A a) :
    ∃ u w : ℝ, u < a ∧ a < w ∧ ∀ x : ℝ, u < x → x < w →
      {y : ℝ | pairFn x y ∈ A}.ncard ≤ {y : ℝ | pairFn a y ∈ A}.ncard := by
  classical
  obtain ⟨uT, wT, qT, ⟨huT, hwT⟩, hrayT⟩ := htop
  obtain ⟨uB, wB, pB, ⟨huB, hwB⟩, hrayB⟩ := hbot
  set Fa := (hfib a).toFinset with hFadef
  -- thin boxes at the fiber points, totalized
  have hboxes : ∀ y : ℝ, ∃ u w p q : ℝ, y ∈ Fa →
      ((u < a ∧ a < w) ∧ (p < y ∧ y < q) ∧ IsThinBox A u w p q) := by
    intro y
    by_cases hy : y ∈ Fa
    · have hyA : pairFn a y ∈ A := (hfib a).mem_toFinset.mp hy
      obtain ⟨u, w, p, q, ⟨⟨h1, h2⟩, h3, h4⟩, hbox⟩ := hnorm y
      rcases hbox with hemp | ⟨-, hthin, -⟩
      · exact absurd hyA (hemp a y ⟨⟨h1, h2⟩, h3, h4⟩)
      · exact ⟨u, w, p, q, fun _ => ⟨⟨h1, h2⟩, ⟨h3, h4⟩, hthin⟩⟩
    · exact ⟨0, 0, 0, 0, fun h => absurd h hy⟩
  choose bU bW bP bQ hbspec using hboxes
  -- the compact leftover
  set K := Set.Icc pB qT ∩ (⋃ y ∈ Fa, Set.Ioo (bP y) (bQ y))ᶜ with hKdef
  have hKfree : ∀ b ∈ K, pairFn a b ∉ A := by
    intro b hb hbA
    have hbF : b ∈ Fa := (hfib a).mem_toFinset.mpr hbA
    exact hb.2 (Set.mem_biUnion hbF ⟨((hbspec b) hbF).2.1.1, ((hbspec b) hbF).2.1.2⟩)
  -- empty boxes over K, totalized
  have hKbox : ∀ b : ℝ, ∃ u w p q : ℝ, (p < b ∧ b < q) ∧ (b ∈ K →
      ((u < a ∧ a < w) ∧ IsEmptyBox A u w p q)) := by
    intro b
    by_cases hb : b ∈ K
    · obtain ⟨u, w, p, q, ⟨⟨h1, h2⟩, h3, h4⟩, hbox⟩ := hnorm b
      rcases hbox with hemp | ⟨hmem, -, -⟩
      · exact ⟨u, w, p, q, ⟨h3, h4⟩, fun _ => ⟨⟨h1, h2⟩, hemp⟩⟩
      · exact absurd hmem (hKfree b hb)
    · obtain ⟨p, hp⟩ := exists_lt b
      obtain ⟨q, hq⟩ := exists_gt b
      exact ⟨0, 0, p, q, ⟨hp, hq⟩, fun h => absurd h hb⟩
  choose eU eW eP eQ hespec using hKbox
  -- Heine–Borel on K
  have hKcomp : IsCompact K :=
    isCompact_Icc.inter_right (isOpen_biUnion fun y _ => isOpen_Ioo).isClosed_compl
  have hcov : K ⊆ ⋃ b : ℝ, (fun b => if b ∈ K then Set.Ioo (eP b) (eQ b) else ∅) b := by
    intro b hb
    exact Set.mem_iUnion.mpr ⟨b, by
      rw [if_pos hb]
      exact ⟨(hespec b).1.1, (hespec b).1.2⟩⟩
  obtain ⟨T, hT⟩ := hKcomp.elim_finite_subcover _
    (fun b => by
      by_cases hb : b ∈ K
      · rw [if_pos hb]
        exact isOpen_Ioo
      · rw [if_neg hb]
        exact isOpen_empty) hcov
  -- the grand window, via nhds
  have hbig : ((Set.Ioo uT wT ∩ Set.Ioo uB wB) ∩
      ((⋂ y ∈ Fa, Set.Ioo (bU y) (bW y)) ∩
        ⋂ b ∈ T, (if b ∈ K then Set.Ioo (eU b) (eW b) else Set.univ))) ∈ 𝓝 a := by
    refine Filter.inter_mem (Filter.inter_mem (Ioo_mem_nhds huT hwT)
      (Ioo_mem_nhds huB hwB)) (Filter.inter_mem ?_ ?_)
    · refine (isOpen_biInter_finset fun y _ => isOpen_Ioo).mem_nhds ?_
      refine Set.mem_iInter₂.mpr fun y hy => ⟨((hbspec y) hy).1.1, ((hbspec y) hy).1.2⟩
    · refine (isOpen_biInter_finset fun b _ => ?_).mem_nhds ?_
      · by_cases hb : b ∈ K
        · rw [if_pos hb]
          exact isOpen_Ioo
        · rw [if_neg hb]
          exact isOpen_univ
      · refine Set.mem_iInter₂.mpr fun b _ => ?_
        by_cases hb : b ∈ K
        · rw [if_pos hb]
          exact ⟨((hespec b).2 hb).1.1, ((hespec b).2 hb).1.2⟩
        · rw [if_neg hb]
          trivial
  obtain ⟨u, w, hauw, hsubw⟩ := mem_nhds_iff_exists_Ioo_subset.mp hbig
  refine ⟨u, w, hauw.1, hauw.2, ?_⟩
  intro x hxu hxw
  obtain ⟨⟨hxT, hxB⟩, hxF, hxK⟩ := hsubw ⟨hxu, hxw⟩
  -- cover claim: every A-point of column x lies in some fiber point's thin box
  have hcover : ∀ z : ℝ, pairFn x z ∈ A → ∃ y ∈ Fa, bP y < z ∧ z < bQ y := by
    intro z hzA
    have hzp : ¬ (z < pB) := fun h => hrayB x ⟨hxB.1, hxB.2⟩ z h hzA
    have hzq : ¬ (qT < z) := fun h => hrayT x ⟨hxT.1, hxT.2⟩ z h hzA
    by_cases hzK : z ∈ K
    · exfalso
      obtain ⟨b, hbT, hzU⟩ := Set.mem_iUnion₂.mp (hT hzK)
      by_cases hbK : b ∈ K
      · rw [if_pos hbK] at hzU
        have hxb : x ∈ Set.Ioo (eU b) (eW b) := by
          have := Set.mem_iInter₂.mp hxK b hbT
          rwa [if_pos hbK] at this
        exact ((hespec b).2 hbK).2 x z ⟨⟨hxb.1, hxb.2⟩, hzU.1, hzU.2⟩ hzA
      · rw [if_neg hbK] at hzU
        exact hzU
    · have hzS : z ∈ ⋃ y ∈ Fa, Set.Ioo (bP y) (bQ y) := by
        by_contra hno
        exact hzK ⟨⟨not_lt.mp hzp, not_lt.mp hzq⟩, hno⟩
      obtain ⟨y, hyF, hzy⟩ := Set.mem_iUnion₂.mp hzS
      exact ⟨y, hyF, hzy.1, hzy.2⟩
  -- injection into the fiber of a
  have hcov' : ∀ z : ℝ, ∃ y : ℝ, pairFn x z ∈ A → (y ∈ Fa ∧ bP y < z ∧ z < bQ y) := by
    intro z
    by_cases hz : pairFn x z ∈ A
    · obtain ⟨y, hyF, hy⟩ := hcover z hz
      exact ⟨y, fun _ => ⟨hyF, hy⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose g hg using hcov'
  have hinj : Set.InjOn g {y : ℝ | pairFn x y ∈ A} := by
    intro z hz z' hz' hgz
    have h1 := hg z hz
    have h2 := hg z' hz'
    rw [hgz] at h1
    have hxg : x ∈ Set.Ioo (bU (g z')) (bW (g z')) := Set.mem_iInter₂.mp hxF _ h2.1
    obtain ⟨zz, -, -, huniq⟩ := ((hbspec (g z')) h2.1).2.2 x ⟨hxg.1, hxg.2⟩
    rw [huniq z ⟨⟨h1.2.1, h1.2.2⟩, hz⟩, huniq z' ⟨⟨h2.2.1, h2.2.2⟩, hz'⟩]
  have hmapsto : ∀ z ∈ {y : ℝ | pairFn x y ∈ A}, g z ∈ (Fa : Set ℝ) :=
    fun z hz => (hg z hz).1
  have hle := Set.ncard_le_ncard_of_injOn g hmapsto hinj (Fa.finite_toSet)
  rwa [Set.ncard_coe_finset, hFadef, ← Set.ncard_eq_toFinset_card _ (hfib a)] at hle

/-! ### Local count constancy -/

/-- **At a fully normal parameter the fiber count is locally constant** — the classical
box-cover argument, both halves. -/
theorem count_locally_constant
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) {a : ℝ}
    (hnorm : ∀ b : ℝ, Normal A a b) (htop : NormalTop A a) (hbot : NormalBot A a) :
    ∃ u w : ℝ, u < a ∧ a < w ∧ ∀ x : ℝ, u < x → x < w →
      {y : ℝ | pairFn x y ∈ A}.ncard = {y : ℝ | pairFn a y ∈ A}.ncard := by
  classical
  set Fa := (hfib a).toFinset with hFadef
  have hfloor : ∃ t : ℝ, ∀ y ∈ Fa, t < y := by
    by_cases h : Fa.Nonempty
    · obtain ⟨t, ht⟩ := exists_lt (Fa.min' h)
      exact ⟨t, fun y hy => lt_of_lt_of_le ht (Fa.min'_le y hy)⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      refine ⟨0, ?_⟩
      rw [h]
      simp
  obtain ⟨t, ht⟩ := hfloor
  obtain ⟨u₁, w₁, hu₁, hw₁, hlow⟩ := strips_lower hnorm Fa.card Fa rfl
    (fun y hy => (hfib a).mem_toFinset.mp hy) t ht
  obtain ⟨u₂, w₂, hu₂, hw₂, hupp⟩ := strips_upper hfib hnorm htop hbot
  refine ⟨max u₁ u₂, min w₁ w₂, max_lt hu₁ hu₂, lt_min hw₁ hw₂, ?_⟩
  intro x hx1 hx2
  have hxu₁ : u₁ < x := lt_of_le_of_lt (le_max_left _ _) hx1
  have hxu₂ : u₂ < x := lt_of_le_of_lt (le_max_right _ _) hx1
  have hxw₁ : x < w₁ := lt_of_lt_of_le hx2 (min_le_left _ _)
  have hxw₂ : x < w₂ := lt_of_lt_of_le hx2 (min_le_right _ _)
  refine le_antisymm (hupp x hxu₂ hxw₂) ?_
  obtain ⟨G, hGcard, hG⟩ := hlow x hxu₁ hxw₁
  have hsub : (G : Set ℝ) ⊆ {y : ℝ | pairFn x y ∈ A} :=
    fun z hz => (hG z (Finset.mem_coe.mp hz)).1
  have hle := Set.ncard_le_ncard hsub (hfib x)
  rw [Set.ncard_coe_finset, hGcard] at hle
  rwa [hFadef, ← Set.ncard_eq_toFinset_card _ (hfib a)] at hle

/-! ### The countSet–ncard bridge and the frontier bound -/

/-- The countSet–ncard bridge (de-privatized at D5a; hypothesis localized). -/
theorem mem_countSet_iff_le_ncard
    {x : ℝ} (hfin : {y : ℝ | pairFn x y ∈ A}.Finite) {k : ℕ} :
    x ∈ countSet A k ↔ k ≤ {y : ℝ | pairFn x y ∈ A}.ncard := by
  have hn : {y : ℝ | pairFn x y ∈ A}.ncard = hfin.toFinset.card :=
    Set.ncard_eq_toFinset_card _ hfin
  constructor
  · intro hx
    obtain ⟨s, hAC⟩ := hx
    obtain ⟨Y, hYcard, hY⟩ := aboveCount_exists_finset hAC
    have hsub : Y ⊆ hfin.toFinset :=
      fun z hz => hfin.mem_toFinset.mpr (hY z hz).2
    have hcard := Finset.card_le_card hsub
    rw [hYcard] at hcard
    omega
  · intro hk
    rw [hn] at hk
    obtain ⟨Y, hYsub, hYcard⟩ :=
      Finset.exists_subset_card_eq (s := hfin.toFinset) (n := k) hk
    have hmem := mem_countSet_of_finset (A := A) (x := x) (Y := Y)
      (fun y hy => hfin.mem_toFinset.mp (hYsub hy))
    rwa [hYcard] at hmem

private theorem frontier_countSet_subset
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) (k : ℕ) :
    frontier (countSet A k) ⊆
      {a : ℝ | (∃ b, ¬ Normal A a b) ∨ ¬ NormalTop A a ∨ ¬ NormalBot A a} := by
  intro a hfr
  by_contra hgood
  simp only [Set.mem_setOf_eq, not_or, not_exists, not_not] at hgood
  obtain ⟨h1, h2, h3⟩ := hgood
  obtain ⟨u, w, hua, haw, hconst⟩ := count_locally_constant hfib h1 h2 h3
  rw [frontier_eq_closure_inter_closure] at hfr
  by_cases hk : k ≤ {y : ℝ | pairFn a y ∈ A}.ncard
  · have hempty : Set.Ioo u w ∩ (countSet A k)ᶜ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxc⟩
      refine hxc ((mem_countSet_iff_le_ncard (hfib x)).mpr ?_)
      rw [hconst x hx.1 hx.2]
      exact hk
    obtain ⟨x, hx⟩ := (mem_closure_iff_nhds.mp hfr.2) _ (Ioo_mem_nhds hua haw)
    rw [Set.eq_empty_iff_forall_notMem] at hempty
    exact hempty x hx
  · rw [not_le] at hk
    have hempty : Set.Ioo u w ∩ countSet A k = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxc⟩
      have := (mem_countSet_iff_le_ncard (hfib x)).mp hxc
      rw [hconst x hx.1 hx.2] at this
      omega
    obtain ⟨x, hx⟩ := (mem_closure_iff_nhds.mp hfr.1) _ (Ioo_mem_nhds hua haw)
    rw [Set.eq_empty_iff_forall_notMem] at hempty
    exact hempty x hx

/-! ### The gap lemma and the chain kill -/

private theorem gap_free {B : Set ℝ} (hB : B.Finite) {x x' : ℝ}
    (hx : x ∉ B) (hx' : x' ∉ B)
    (hf : hB.toFinset.filter (fun b => b < x) = hB.toFinset.filter (fun b => b < x')) :
    ∀ b ∈ B, b ∉ Set.Icc (min x x') (max x x') := by
  intro b hbB hbI
  have hbF : b ∈ hB.toFinset := hB.mem_toFinset.mpr hbB
  rcases le_total x x' with hle | hle
  · rw [min_eq_left hle, max_eq_right hle] at hbI
    have hbx' : b < x' := lt_of_le_of_ne hbI.2 (fun h => hx' (h ▸ hbB))
    have hbmem : b ∈ hB.toFinset.filter (fun b => b < x') :=
      Finset.mem_filter.mpr ⟨hbF, hbx'⟩
    rw [← hf] at hbmem
    exact absurd (Finset.mem_filter.mp hbmem).2 (not_lt.mpr hbI.1)
  · rw [min_eq_right hle, max_eq_left hle] at hbI
    have hbx : b < x := lt_of_le_of_ne hbI.2 (fun h => hx (h ▸ hbB))
    have hbmem : b ∈ hB.toFinset.filter (fun b => b < x) :=
      Finset.mem_filter.mpr ⟨hbF, hbx⟩
    rw [hf] at hbmem
    exact absurd (Finset.mem_filter.mp hbmem).2 (not_lt.mpr hbI.1)

/-- **UNIFORM FINITENESS (the Finiteness Lemma).** Definable `A ⊆ ℝ²` with every fiber
finite has uniformly bounded fibers. -/
theorem uniform_finiteness (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    ∃ N : ℕ, ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.ncard ≤ N := by
  classical
  by_contra hunb
  push Not at hunb
  have hne : ∀ k : ℕ, (countSet A k).Nonempty := by
    intro k
    obtain ⟨x, hx⟩ := hunb k
    exact ⟨x, (mem_countSet_iff_le_ncard (hfib x)).mpr hx.le⟩
  have hBfin := abnormal_finite hA hfib
  have hIntEmpty : ∀ x : ℝ, ∃ k, x ∉ countSet A k := by
    intro x
    by_contra h
    push Not at h
    exact infinite_fiber_of_mem_all h (hfib x)
  by_cases hcase : ∃ k₀, countSet A k₀ ⊆
      {a : ℝ | (∃ b, ¬ Normal A a b) ∨ ¬ NormalTop A a ∨ ¬ NormalBot A a}
  · -- a counting set inside a finite set — but D2 puts an interval inside it
    obtain ⟨k₀, hk₀⟩ := hcase
    obtain ⟨c, d, hcd, hsub⟩ := exists_interval_in_countSet hA hfib hne k₀
    exact ((Set.Ioo_infinite hcd).mono (fun x hx => hk₀ (hsub hx))) hBfin
  · push Not at hcase
    -- witnesses off the abnormal set
    have hpick : ∀ k : ℕ, ∃ x, x ∈ countSet A k ∧ x ∉
        {a : ℝ | (∃ b, ¬ Normal A a b) ∨ ¬ NormalTop A a ∨ ¬ NormalBot A a} := by
      intro k
      obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp (hcase k)
      exact ⟨x, hx1, hx2⟩
    choose xs hxs hxsB using hpick
    -- pigeonhole: infinitely many witnesses share one abnormal-gap
    set f : ℕ → {s : Finset ℝ // s ∈ hBfin.toFinset.powerset} := fun k =>
      ⟨hBfin.toFinset.filter (fun b => b < xs k),
        Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩ with hfdef
    obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber f
    have hKinf : (f ⁻¹' {v}).Infinite := Set.infinite_coe_iff.mp hv
    have hKunb : ∀ k : ℕ, ∃ k', k' ∈ f ⁻¹' {v} ∧ k ≤ k' := by
      intro k
      by_contra hno
      push Not at hno
      exact hKinf ((Set.finite_Iio k).subset (fun m hm => (hno m hm)))
    obtain ⟨j₀, hj₀⟩ := hKinf.nonempty
    -- the earliest shared-gap witness lies in every counting set
    have hall : ∀ k : ℕ, xs j₀ ∈ countSet A k := by
      intro k
      obtain ⟨k', hk'K, hkk'⟩ := hKunb k
      have hfeq : hBfin.toFinset.filter (fun b => b < xs j₀)
          = hBfin.toFinset.filter (fun b => b < xs k') := by
        have h1 : f j₀ = v := hj₀
        have h2 : f k' = v := hk'K
        have := h1.trans h2.symm
        exact congrArg Subtype.val this
      have hgap := gap_free hBfin (hxsB j₀) (hxsB k') hfeq
      have hdisj : ∀ z ∈ Set.Icc (min (xs j₀) (xs k')) (max (xs j₀) (xs k')),
          z ∉ frontier (countSet A k') := by
        intro z hz hzfr
        exact hgap z (frontier_countSet_subset hfib k' hzfr) hz
      have hprop : xs j₀ ∈ countSet A k' := by
        rcases preconnected_split isPreconnected_Icc hdisj with hsub | hdis
        · exact hsub ⟨min_le_left _ _, le_max_left _ _⟩
        · exfalso
          have hmem : xs k' ∈ Set.Icc (min (xs j₀) (xs k')) (max (xs j₀) (xs k'))
              ∩ countSet A k' := ⟨⟨min_le_right _ _, le_max_right _ _⟩, hxs k'⟩
          rw [hdis] at hmem
          exact hmem
      exact countSet_anti_le A hkk' hprop
    obtain ⟨k, hk⟩ := hIntEmpty (xs j₀)
    exact hk (hall k)

/-- **UF, counting-set form**: some counting set is empty. -/
theorem exists_empty_countSet (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    ∃ N : ℕ, countSet A (N + 1) = ∅ := by
  obtain ⟨N, hN⟩ := uniform_finiteness hA hfib
  refine ⟨N, Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_⟩
  have := (mem_countSet_iff_le_ncard (hfib x)).mp hx
  have := le_trans this (hN x)
  omega

end Sundog.OMinimalAbstract
