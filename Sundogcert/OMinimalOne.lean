/-
# O-minimality in dimension one: two structures machine-checked tame (o-min ladder, rung 1)

Follow-on to `DefinableRate` (U-4). That module delivered the PL finiteness-modulus; this one takes
the first genuine step toward o-minimality itself. mathlib v4.30.0 has no o-minimal substrate, so
the dimension-one core is built from scratch here, on the **finite-frontier characterization**:

  a set `s ⊆ ℝ` is a finite union of points and open intervals **iff** `frontier s` is finite

(⇐ the frontier is contained in the endpoints; ⇒ the finitely many frontier points cut ℝ into open
intervals, on each of which `s` is clopen, hence full or empty by connectedness). We take
`Tame s := (frontier s).Finite` as the o-minimality predicate; the normal-form equivalence is a
named follow-on, not needed to state or use the axiom.

Two concrete structures are proved o-minimal:

1. **The ReLU/semilinear structure** (`NetDef` / `netDef_tame`): every set built by complement and
   union from strict superlevel sets `{x | c < realize1N g x}` of 1-D ReLU nets is tame. Sublevel
   sets are inside the algebra (`Net.scale (-1) g` mirrors), hence level sets, rays, intervals,
   and points (`Net.var` realizes `id`).
2. **Quantifier-free semialgebraic sets** (`PolyDef` / `polyDef_tame`): every boolean combination
   of polynomial strict sign conditions `{x | c < p.eval x}` is tame — the one-variable,
   quantifier-free shadow of Tarski.

The load-bearing new lemma is `affineAway_levelSet_tame`: a continuous function that is affine
away from a finite cut set has a **finite-frontier level set**. Away from the cuts, mapping a
frontier point to the set of cuts below it is injective — two frontier points over the same cut
pattern would pin their whole stretch to the constant (`line_pinned`), and pinned stretches admit
no frontier point — so the frontier injects into `S ∪ powerset S`.

**Honest fence.** This is o-minimality of two concrete structures **in dimension one**. The full
theory needs closure under *projection* from ℝⁿ (Tarski–Seidenberg quantifier elimination for the
semialgebraic case; formalized in Coq by Cohen–Mahboubi, not in Lean) and the abstract
monotonicity/cell-decomposition machinery — those are the next, genuinely large walls, named in
the ladder and not claimed here.
-/
import Sundogcert.DefinableRate
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial

namespace Sundog.OMinimalOne

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.ExactRepr

/-- **The dimension-one o-minimality predicate.** `s ⊆ ℝ` is tame when its frontier is finite —
equivalently (finitely many frontier points cut ℝ into open intervals on which `s` is clopen,
hence full or empty by connectedness), `s` is a finite union of points and open intervals, the
standard o-minimality axiom for definable subsets of the line. -/
def Tame (s : Set ℝ) : Prop := (frontier s).Finite

theorem tame_empty : Tame (∅ : Set ℝ) := by simp [Tame]

theorem tame_univ : Tame (Set.univ : Set ℝ) := by simp [Tame]

/-- Tame sets are closed under complement (`frontier sᶜ = frontier s`). -/
theorem tame_compl {s : Set ℝ} (h : Tame s) : Tame sᶜ := by
  simpa [Tame, frontier_compl] using h

/-- Tame sets are closed under union (frontiers of unions do not grow). -/
theorem tame_union {s t : Set ℝ} (hs : Tame s) (ht : Tame t) : Tame (s ∪ t) :=
  (hs.union ht).subset ((frontier_union_subset s t).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right))

/-- Tame sets are closed under intersection — so `Tame` sets form a boolean algebra. -/
theorem tame_inter {s t : Set ℝ} (hs : Tame s) (ht : Tame t) : Tame (s ∩ t) := by
  have h := tame_compl (tame_union (tame_compl hs) (tame_compl ht))
  simpa [Set.compl_union, compl_compl] using h

/-- Every 1-D ReLU net realizes a continuous function (induction on the gates). -/
theorem net_continuous : ∀ g : Net 1, Continuous (realize1N g) := by
  intro g
  induction g with
  | var i =>
    have h : realize1N (Net.var i) = (id : ℝ → ℝ) := by funext t; simp [realize1N]
    rw [h]; exact continuous_id
  | const c =>
    have h : realize1N (Net.const c) = (fun _ => c) := by funext t; simp [realize1N]
    rw [h]; exact continuous_const
  | add a b iha ihb => rw [realize1N_add]; exact iha.add ihb
  | scale c a ih => rw [realize1N_scale]; exact continuous_const.mul ih
  | relu a ih => rw [realize1N_relu]; exact ih.max continuous_const

/-- The frontier of a strict superlevel set of a continuous function sits inside the frontier of
the corresponding level set: a boundary point of `{c < f}` satisfies `f x = c` (continuity from
both sides) and is approached by points with `f > c ≠ c`. -/
theorem frontier_superlevel_subset {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    frontier {x | c < f x} ⊆ frontier {x | f x = c} := by
  intro x hx
  have hopen : IsOpen {x : ℝ | c < f x} := isOpen_lt continuous_const hf
  rw [hopen.frontier_eq] at hx
  obtain ⟨hxcl, hxnot⟩ := hx
  have h1 : f x ≤ c := not_lt.mp hxnot
  have h2 : c ≤ f x := by
    have hsub : closure {x : ℝ | c < f x} ⊆ {x : ℝ | c ≤ f x} :=
      closure_minimal (fun y hy => le_of_lt (show c < f y from hy))
        (isClosed_le continuous_const hf)
    exact hsub hxcl
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (le_antisymm h1 h2), ?_⟩
  have hsub : {x : ℝ | c < f x} ⊆ {x : ℝ | f x = c}ᶜ := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at *
    exact (ne_of_lt hy).symm
  exact closure_mono hsub hxcl

/-! ### The level set of a piece-covered continuous function has finite frontier -/

/-- Tail contradiction: `f` equals `c` at two distinct points `x < y` of a cut-free stretch, and a
point `z` beyond `y` in the same stretch has `f z ≠ c` — impossible, since the stretch is a single
affine piece pinned to the constant `c` by the two points. -/
private theorem line_pinned {f : ℝ → ℝ} {S : Finset ℝ} {c x y z : ℝ}
    (hAff : AffineAway f S) (hfx : f x = c) (hfy : f y = c)
    (hxy : x < y) (hyz : y < z)
    (hmiss : ∀ s ∈ S, s ∉ Set.Ioo x z) (hzne : ¬ f z = c) : False := by
  obtain ⟨p, q, hpq⟩ := hAff x z (hxy.trans hyz).le hmiss
  have h1 := hpq x ⟨le_refl x, (hxy.trans hyz).le⟩
  have h2 := hpq y ⟨hxy.le, hyz.le⟩
  rw [hfx] at h1
  rw [hfy] at h2
  have h3 : p * x = p * y := by linarith
  have hp : p = 0 := by
    by_contra h0
    exact absurd (mul_left_cancel₀ h0 h3) (ne_of_lt hxy)
  have hq : q = c := by
    rw [hp, zero_mul, zero_add] at h1
    exact h1.symm
  exact hzne (by rw [hpq z ⟨(hxy.trans hyz).le, le_refl z⟩, hp, hq, zero_mul, zero_add])

/-- Two frontier points of the level set `{f = c}` that avoid the cut set and see the same set of
cuts below them coincide: their stretch is one affine piece pinned to `c`, so points witnessing
"frontier" (arbitrarily near, off the level set) land in the pinned stretch — contradiction. -/
private theorem fiber_aux {f : ℝ → ℝ} {S : Finset ℝ} {c x y : ℝ}
    (hf : Continuous f) (hAff : AffineAway f S)
    (hx : x ∈ frontier {t : ℝ | f t = c}) (hy : y ∈ frontier {t : ℝ | f t = c})
    (hyS : y ∉ S) (hT : S.filter (· < x) = S.filter (· < y)) (hxy : x < y) : False := by
  have hZ : IsClosed {t : ℝ | f t = c} := isClosed_eq hf continuous_const
  have hfx : f x = c := hZ.frontier_subset hx
  have hfy : f y = c := hZ.frontier_subset hy
  -- no cut lies strictly between x and y (they see the same cuts below them)
  have hIoo : ∀ s ∈ S, s ∉ Set.Ioo x y := by
    intro s hs hmem
    have h1 : s ∈ S.filter (· < y) := Finset.mem_filter.mpr ⟨hs, hmem.2⟩
    rw [← hT] at h1
    exact absurd (Finset.mem_filter.mp h1).2 (not_lt.mpr hmem.1.le)
  obtain ⟨p, q, hpq⟩ := hAff x y hxy.le hIoo
  have h1 := hpq x ⟨le_refl x, hxy.le⟩
  have h2 := hpq y ⟨hxy.le, le_refl y⟩
  rw [hfx] at h1
  rw [hfy] at h2
  have h3 : p * x = p * y := by linarith
  have hp : p = 0 := by
    by_contra h0
    exact absurd (mul_left_cancel₀ h0 h3) (ne_of_lt hxy)
  have hq : q = c := by
    rw [hp, zero_mul, zero_add] at h1
    exact h1.symm
  -- y is a frontier point: off-level points approach it; trap one in the pinned stretch
  have hy2 : y ∈ closure {t : ℝ | f t = c}ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hy
    exact hy.2
  by_cases hne : (S.filter fun s => y < s).Nonempty
  · -- there is a first cut b above y: probe inside the open window (x, b)
    have hbmem := (S.filter fun s => y < s).min'_mem hne
    rw [Finset.mem_filter] at hbmem
    obtain ⟨z, hzU, hzc⟩ :=
      mem_closure_iff.mp hy2 (Set.Ioo x ((S.filter fun s => y < s).min' hne)) isOpen_Ioo
        ⟨hxy, hbmem.2⟩
    have hzne : ¬ f z = c := hzc
    rcases le_or_gt z y with hzy | hyz
    · exact hzne (by rw [hpq z ⟨hzU.1.le, hzy⟩, hp, hq, zero_mul, zero_add])
    · refine line_pinned hAff hfx hfy hxy hyz ?_ hzne
      intro s hs hmem
      rcases le_or_gt s y with hsy | hys
      · exact hIoo s hs ⟨hmem.1, lt_of_le_of_ne hsy fun h => hyS (h ▸ hs)⟩
      · have hbs := Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, hys⟩)
        exact absurd (hmem.2.trans hzU.2) (not_lt.mpr hbs)
  · -- no cut above y at all: probe inside the open ray (x, ∞)
    obtain ⟨z, hzU, hzc⟩ := mem_closure_iff.mp hy2 (Set.Ioi x) isOpen_Ioi hxy
    have hzne : ¬ f z = c := hzc
    rcases le_or_gt z y with hzy | hyz
    · exact hzne (by rw [hpq z ⟨hzU.le, hzy⟩, hp, hq, zero_mul, zero_add])
    · refine line_pinned hAff hfx hfy hxy hyz ?_ hzne
      intro s hs hmem
      rcases le_or_gt s y with hsy | hys
      · exact hIoo s hs ⟨hmem.1, lt_of_le_of_ne hsy fun h => hyS (h ▸ hs)⟩
      · exact hne ⟨s, Finset.mem_filter.mpr ⟨hs, hys⟩⟩

/-- **Core: a piece-covered continuous function has a tame level set.** Away from the finite cut
set, the map sending a frontier point of `{f = c}` to the set of cuts below it is injective
(`fiber_aux`), so the frontier injects into `S ∪ powerset S` — finite. -/
theorem affineAway_levelSet_tame {f : ℝ → ℝ} {S : Finset ℝ}
    (hf : Continuous f) (hAff : AffineAway f S) (c : ℝ) : Tame {x | f x = c} := by
  classical
  change (frontier {t : ℝ | f t = c}).Finite
  have hinj : Set.InjOn (fun x => S.filter (· < x))
      (frontier {t : ℝ | f t = c} \ ↑S) := by
    intro x hx y hy hEq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact fiber_aux hf hAff hx.1 hy.1 (fun hyS => hy.2 (Finset.mem_coe.mpr hyS)) hEq h
    · exact fiber_aux hf hAff hy.1 hx.1 (fun hxS => hx.2 (Finset.mem_coe.mpr hxS)) hEq.symm h
  have himg : ((fun x => S.filter (· < x)) '' (frontier {t : ℝ | f t = c} \ ↑S)).Finite := by
    refine Set.Finite.subset (S.powerset).finite_toSet ?_
    rintro _ ⟨x, _, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
  have hdiff : (frontier {t : ℝ | f t = c} \ ↑S).Finite :=
    Set.Finite.of_finite_image himg hinj
  refine Set.Finite.subset (hdiff.union S.finite_toSet) ?_
  intro x hx
  by_cases hxS : x ∈ (S : Set ℝ)
  · exact Set.mem_union_right _ hxS
  · exact Set.mem_union_left _ ⟨hx, hxS⟩

/-- **Every level set of a 1-D ReLU net is tame.** -/
theorem net_levelSet_tame (g : Net 1) (c : ℝ) : Tame {x | realize1N g x = c} := by
  obtain ⟨_, S, _, hAff⟩ := net_hasPieceCover g
  exact affineAway_levelSet_tame (net_continuous g) hAff c

/-- **Every strict superlevel set of a 1-D ReLU net is tame.** -/
theorem net_superlevel_tame (g : Net 1) (c : ℝ) : Tame {x | c < realize1N g x} :=
  Set.Finite.subset (net_levelSet_tame g c)
    (frontier_superlevel_subset (net_continuous g) c)

/-- Sets definable quantifier-free from ReLU-net strict inequalities: the boolean algebra
generated by the strict superlevel sets `{x | c < realize1N g x}`. Sublevel sets are inside the
algebra (`Net.scale (-1) g` mirrors the inequality), hence so are level sets, rays, intervals,
and points (`Net.var` realizes `id`). -/
inductive NetDef : Set ℝ → Prop
  | superlevel (g : Net 1) (c : ℝ) : NetDef {x | c < realize1N g x}
  | compl {s : Set ℝ} : NetDef s → NetDef sᶜ
  | union {s t : Set ℝ} : NetDef s → NetDef t → NetDef (s ∪ t)

/-- **O-minimality of the ReLU/semilinear structure, dimension one.** Every set definable
(quantifier-free) from 1-D ReLU-net inequalities has finite frontier — equivalently, is a finite
union of points and open intervals. -/
theorem netDef_tame {s : Set ℝ} (h : NetDef s) : Tame s := by
  induction h with
  | superlevel g c => exact net_superlevel_tame g c
  | compl _ ih => exact tame_compl ih
  | union _ _ ihs iht => exact tame_union ihs iht

/-- **Every polynomial level set is tame**: either the polynomial is constantly `c` (the level
set is `univ`) or the level set sits inside the finite root set of `p - C c`. -/
theorem poly_levelSet_tame (p : Polynomial ℝ) (c : ℝ) : Tame {x | p.eval x = c} := by
  by_cases hp : p - Polynomial.C c = 0
  · have hall : {x : ℝ | p.eval x = c} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [sub_eq_zero.mp hp, Polynomial.eval_C]
    have h := tame_univ
    rwa [hall]
  · have hfin : {x : ℝ | (p - Polynomial.C c).IsRoot x}.Finite :=
      Polynomial.finite_setOf_isRoot hp
    refine Set.Finite.subset hfin ?_
    intro x hx
    have hcl : IsClosed {x : ℝ | p.eval x = c} :=
      isClosed_eq p.continuous continuous_const
    have hx' : p.eval x = c := hcl.frontier_subset hx
    change (p - Polynomial.C c).eval x = 0
    rw [Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero]
    exact hx'

/-- **Every polynomial strict superlevel set is tame.** -/
theorem poly_superlevel_tame (p : Polynomial ℝ) (c : ℝ) : Tame {x | c < p.eval x} :=
  Set.Finite.subset (poly_levelSet_tame p c) (frontier_superlevel_subset p.continuous c)

/-- Quantifier-free semialgebraic subsets of ℝ: the boolean algebra generated by polynomial
strict sign conditions. -/
inductive PolyDef : Set ℝ → Prop
  | superlevel (p : Polynomial ℝ) (c : ℝ) : PolyDef {x | c < p.eval x}
  | compl {s : Set ℝ} : PolyDef s → PolyDef sᶜ
  | union {s t : Set ℝ} : PolyDef s → PolyDef t → PolyDef (s ∪ t)

/-- **O-minimality of the quantifier-free semialgebraic structure, dimension one** — the
one-variable, quantifier-free shadow of Tarski: every boolean combination of polynomial strict
sign conditions has finite frontier. The full semialgebraic structure needs closure under
projection (Tarski–Seidenberg quantifier elimination): the named next wall, not claimed here. -/
theorem polyDef_tame {s : Set ℝ} (h : PolyDef s) : Tame s := by
  induction h with
  | superlevel p c => exact poly_superlevel_tame p c
  | compl _ ih => exact tame_compl ih
  | union _ _ ihs iht => exact tame_union ihs iht

end Sundog.OMinimalOne
