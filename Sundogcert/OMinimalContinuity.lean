/-
# O-min lane R4-C2a: the order-continuity bridge and the tame discontinuity set.

The structure has no arithmetic atoms, so ε-δ continuity is not expressible — but ℝ's topology
is the order topology, so `ContinuousAt` has a pure `<`-characterization
(`continuousAt_iff_order`, via `nhds_basis_Ioo` + `HasBasis.tendsto_iff`), and *that* is a
formula. Design refinement over the scope: split into **upper and lower semicontinuity** sets
(`uscSet`/`lscSet`) — two five-coordinate formulas instead of one six-coordinate formula — and
recover `ContinuousAt` as their conjunction (`continuousAt_iff_usc_lsc`; the meta-level proof
may use arithmetic freely, only the *formulas* may not). Two new comparison combinators
(`ltCoordGraph`: `x_j < φ(x_i)`, `ltGraphCoord`: `φ(x_i) < x_j`) complete the atom kit.

Headline: **`tame_discSet`** — the discontinuity set of a definable function is tame. C2b will
show it cannot contain an interval; C2c makes it finite and assembles the continuous
Monotonicity Theorem.

**Honest fence.** C2a only: no kill, no assembly. The `-φ` trick remains off-limits wherever
definability is consumed (negation is not an atom) — C2b's decreasing case is mirrored by hand.
-/
import Sundogcert.OMinimalMonotonicity

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne

/-! ### The order-continuity bridge -/

/-- **Continuity in pure order terms** (ℝ's topology is the order topology): `φ` is continuous
at `x` iff every order-bracket of `φ x` pulls back to an order-window of `x`. -/
theorem continuousAt_iff_order (φ : ℝ → ℝ) (x : ℝ) :
    ContinuousAt φ x ↔ ∀ p q : ℝ, p < φ x → φ x < q →
      ∃ u v : ℝ, u < x ∧ x < v ∧ ∀ y, u < y → y < v → p < φ y ∧ φ y < q := by
  have hb := (nhds_basis_Ioo x).tendsto_iff (nhds_basis_Ioo (φ x)) (f := φ)
  constructor
  · intro h p q hp hq
    obtain ⟨ia, ⟨h1, h2⟩, h3⟩ := hb.mp h (p, q) ⟨hp, hq⟩
    refine ⟨ia.1, ia.2, h1, h2, fun y hy1 hy2 => ?_⟩
    exact Set.mem_Ioo.mp (h3 y (Set.mem_Ioo.mpr ⟨hy1, hy2⟩))
  · intro h
    refine hb.mpr ?_
    rintro ⟨p, q⟩ ⟨h1, h2⟩
    obtain ⟨u, v, hu, hv, hw⟩ := h p q h1 h2
    refine ⟨(u, v), ⟨hu, hv⟩, fun y hy => ?_⟩
    have hy' := Set.mem_Ioo.mp hy
    exact Set.mem_Ioo.mpr (hw y hy'.1 hy'.2)

/-! ### Snoc battery extension (literal indices, depths 3→4 and 4→5) -/

private theorem snocF (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocG (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocH (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 2 = g 2 := by
  simp [Fin.snoc]

private theorem snocI (g : Fin 3 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 4 → ℝ) 3 = y := by
  simp [Fin.snoc]

private theorem snocJ (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocK (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocL (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 2 = g 2 := by
  simp [Fin.snoc]

private theorem snocM (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 3 = g 3 := by
  simp [Fin.snoc]

private theorem snocN (g : Fin 4 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 5 → ℝ) 4 = y := by
  simp [Fin.snoc]

private theorem snocA' (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocB' (g : Fin 1 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 2 → ℝ) 1 = y := by
  simp [Fin.snoc]

private theorem snocC' (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 0 = g 0 := by
  simp [Fin.snoc]

private theorem snocD' (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 1 = g 1 := by
  simp [Fin.snoc]

private theorem snocE' (g : Fin 2 → ℝ) (y : ℝ) : (Fin.snoc g y : Fin 3 → ℝ) 2 = y := by
  simp [Fin.snoc]

/-! ### Two more comparison combinators -/

namespace Fml

variable {S : OMinStructure} {n : ℕ}

/-- `x_j < φ(x_i)`. -/
def ltCoordGraph {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (j i : Fin n) : Fml S n :=
  .ex (.and (graphAt hφ (Fin.castSucc i) (Fin.last n))
    (ltAt (Fin.castSucc j) (Fin.last n)))

@[simp] theorem eval_ltCoordGraph {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (j i : Fin n)
    (f : Fin n → ℝ) : (ltCoordGraph hφ j i).eval f ↔ f j < φ (f i) := by
  simp only [ltCoordGraph, eval, eval_graphAt, eval_ltAt, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨w, hg, hlt⟩
    rw [← hg] at hlt
    exact hlt
  · intro h
    exact ⟨φ (f i), rfl, h⟩

/-- `φ(x_i) < x_j`. -/
def ltGraphCoord {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n) : Fml S n :=
  .ex (.and (graphAt hφ (Fin.castSucc i) (Fin.last n))
    (ltAt (Fin.last n) (Fin.castSucc j)))

@[simp] theorem eval_ltGraphCoord {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (i j : Fin n)
    (f : Fin n → ℝ) : (ltGraphCoord hφ i j).eval f ↔ φ (f i) < f j := by
  simp only [ltGraphCoord, eval, eval_graphAt, eval_ltAt, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨w, hg, hlt⟩
    rw [← hg] at hlt
    exact hlt
  · intro h
    exact ⟨φ (f i), rfl, h⟩

end Fml

open Fml

/-! ### The semicontinuity sets -/

variable (φ : ℝ → ℝ)

/-- Order upper semicontinuity at `x`: every upper bracket pulls back to a window. -/
def uscSet : Set ℝ :=
  {x | ∀ q, φ x < q → ∃ u v, u < x ∧ x < v ∧ ∀ y, u < y → y < v → φ y < q}

/-- Order lower semicontinuity at `x`. -/
def lscSet : Set ℝ :=
  {x | ∀ p, p < φ x → ∃ u v, u < x ∧ x < v ∧ ∀ y, u < y → y < v → p < φ y}

variable {φ}

/-- The usc set is tame — a five-coordinate formula (`x=0, ∀q=1, ∃u=2, ∃v=3, ∀y=4`). -/
theorem tame_uscSet {S : OMinStructure} (hφ : S.DefinableFun φ) : Tame (uscSet φ) := by
  have h := Fml.tame_one (S := S)
    (Fml.all ((ltGraphCoord hφ 0 1).imp
      (Fml.ex (Fml.ex ((Fml.and (ltAt 2 0) (Fml.and (ltAt 0 3)
        (Fml.all ((Fml.and (ltAt 2 4) (ltAt 4 3)).imp (ltGraphCoord hφ 4 1))))))))))
  have e : uscSet φ
      = {x : ℝ | Fml.eval (S := S) (n := 1)
          (Fml.all ((ltGraphCoord hφ 0 1).imp
            (Fml.ex (Fml.ex ((Fml.and (ltAt 2 0) (Fml.and (ltAt 0 3)
              (Fml.all ((Fml.and (ltAt 2 4) (ltAt 4 3)).imp (ltGraphCoord hφ 4 1))))))))))
          (fun _ => x)} := by
    ext x
    simp only [uscSet, Set.mem_setOf_eq, Fml.eval, eval_all, eval_imp, eval_ltAt,
      eval_ltGraphCoord, snocA', snocB', snocC', snocD', snocE', snocF, snocG, snocH, snocI,
      snocK, snocL, snocM, snocN, and_imp]
  rw [e]
  exact h

/-- The lsc set is tame (mirror formula with `ltCoordGraph`). -/
theorem tame_lscSet {S : OMinStructure} (hφ : S.DefinableFun φ) : Tame (lscSet φ) := by
  have h := Fml.tame_one (S := S)
    (Fml.all ((ltCoordGraph hφ 1 0).imp
      (Fml.ex (Fml.ex ((Fml.and (ltAt 2 0) (Fml.and (ltAt 0 3)
        (Fml.all ((Fml.and (ltAt 2 4) (ltAt 4 3)).imp (ltCoordGraph hφ 1 4))))))))))
  have e : lscSet φ
      = {x : ℝ | Fml.eval (S := S) (n := 1)
          (Fml.all ((ltCoordGraph hφ 1 0).imp
            (Fml.ex (Fml.ex ((Fml.and (ltAt 2 0) (Fml.and (ltAt 0 3)
              (Fml.all ((Fml.and (ltAt 2 4) (ltAt 4 3)).imp (ltCoordGraph hφ 1 4))))))))))
          (fun _ => x)} := by
    ext x
    simp only [lscSet, Set.mem_setOf_eq, Fml.eval, eval_all, eval_imp, eval_ltAt,
      eval_ltCoordGraph, snocA', snocB', snocC', snocD', snocE', snocF, snocG, snocH, snocI,
      snocK, snocL, snocM, snocN, and_imp]
  rw [e]
  exact h

/-! ### The bridge to `ContinuousAt`, and the tame discontinuity set -/

/-- `ContinuousAt` is exactly usc ∧ lsc, in order terms. -/
theorem continuousAt_iff_usc_lsc (φ : ℝ → ℝ) (x : ℝ) :
    ContinuousAt φ x ↔ x ∈ uscSet φ ∧ x ∈ lscSet φ := by
  rw [continuousAt_iff_order]
  constructor
  · intro h
    constructor
    · intro q hq
      obtain ⟨u, v, hu, hv, hw⟩ := h (φ x - 1) q (by linarith) hq
      exact ⟨u, v, hu, hv, fun y h1 h2 => (hw y h1 h2).2⟩
    · intro p hp
      obtain ⟨u, v, hu, hv, hw⟩ := h p (φ x + 1) hp (by linarith)
      exact ⟨u, v, hu, hv, fun y h1 h2 => (hw y h1 h2).1⟩
  · rintro ⟨husc, hlsc⟩ p q hp hq
    obtain ⟨u₁, v₁, hu₁, hv₁, hw₁⟩ := husc q hq
    obtain ⟨u₂, v₂, hu₂, hv₂, hw₂⟩ := hlsc p hp
    refine ⟨max u₁ u₂, min v₁ v₂, max_lt hu₁ hu₂, lt_min hv₁ hv₂, fun y h1 h2 => ?_⟩
    exact ⟨hw₂ y (lt_of_le_of_lt (le_max_right _ _) h1)
        (lt_of_lt_of_le h2 (min_le_right _ _)),
      hw₁ y (lt_of_le_of_lt (le_max_left _ _) h1)
        (lt_of_lt_of_le h2 (min_le_left _ _))⟩

/-- **The discontinuity set of a definable function is tame (C2a headline).** -/
theorem tame_discSet {S : OMinStructure} (hφ : S.DefinableFun φ) :
    Tame {x : ℝ | ¬ ContinuousAt φ x} := by
  have h := tame_compl (tame_inter (tame_uscSet hφ) (tame_lscSet hφ))
  have e : (uscSet φ ∩ lscSet φ)ᶜ = {x : ℝ | ¬ ContinuousAt φ x} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
      continuousAt_iff_usc_lsc]
  rwa [e] at h

/-! ### C2b — the kill: a strictly monotone definable function has a continuity point

The image of an interval is a formula ⇒ tame; strict monotonicity makes it infinite
(`InjOn` + `Set.infinite_image_iff`), so it contains a value interval `(p,q)`
(`tame_infinite_contains_Ioo`, its fourth use); any preimage point of the midpoint is
order-continuous by the monotone squeeze — bracket values inside `(p,q)` have preimages
bracketing the point, and monotonicity traps the window's image. The decreasing case is
mirrored by hand (the `-φ` trick is unavailable where definability is consumed). -/

/-- The image of an interval under a definable function is tame. -/
theorem tame_image {S : OMinStructure} {φ : ℝ → ℝ} (hφ : S.DefinableFun φ) (c d : ℝ) :
    Tame (φ '' Set.Ioo c d) := by
  have h := Fml.tame_one (S := S)
    (Fml.ex (.and (memAt 1 (S.definable_Ioi c)) (.and (memAt 1 (S.definable_Iio d))
      (graphAt hφ 1 0))))
  have e : φ '' Set.Ioo c d = {p : ℝ | Fml.eval (S := S) (n := 1)
      (Fml.ex (.and (memAt 1 (S.definable_Ioi c)) (.and (memAt 1 (S.definable_Iio d))
        (graphAt hφ 1 0)))) (fun _ => p)} := by
    ext p
    simp only [Set.mem_image, Set.mem_Ioo, Set.mem_setOf_eq, Fml.eval, eval_memAt,
      eval_graphAt, snocA', snocB', Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, h3⟩
      exact ⟨z, h1, h2, h3⟩
    · rintro ⟨z, h1, h2, h3⟩
      exact ⟨z, ⟨h1, h2⟩, h3⟩
  rw [e]
  exact h

/-- **The increasing kill**: a strictly increasing definable function on an interval has a
continuity point (in fact any preimage of an interior image value works). -/
theorem strictMonoOn_exists_continuityPt {S : OMinStructure} {φ : ℝ → ℝ}
    (hφ : S.DefinableFun φ) {c d : ℝ} (hcd : c < d)
    (hmono : StrictMonoOn φ (Set.Ioo c d)) :
    ∃ x ∈ Set.Ioo c d, ContinuousAt φ x := by
  obtain ⟨p, q, hpq, hsub⟩ := tame_infinite_contains_Ioo (tame_image hφ c d)
    ((Set.infinite_image_iff hmono.injOn).mpr (Set.Ioo_infinite hcd))
  have hm : (p + q) / 2 ∈ Set.Ioo p q := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨x₀, hx₀, hφx₀⟩ := hsub hm
  rw [Set.mem_Ioo] at hm
  refine ⟨x₀, hx₀, ?_⟩
  rw [continuousAt_iff_order]
  intro p₀ q₀ hp₀ hq₀
  rw [hφx₀] at hp₀ hq₀
  have hmaxm : max p p₀ < (p + q) / 2 := max_lt hm.1 hp₀
  have hminm : (p + q) / 2 < min q q₀ := lt_min hm.2 hq₀
  have hsA : (max p p₀ + (p + q) / 2) / 2 ∈ Set.Ioo p q := by
    rw [Set.mem_Ioo]
    constructor
    · have := le_max_left p p₀
      linarith
    · linarith
  obtain ⟨u, hu, hφu⟩ := hsub hsA
  have htA : ((p + q) / 2 + min q q₀) / 2 ∈ Set.Ioo p q := by
    rw [Set.mem_Ioo]
    constructor
    · linarith
    · have := min_le_left q q₀
      linarith
  obtain ⟨v, hv, hφv⟩ := hsub htA
  have hux : u < x₀ := by
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hφx₀
      rw [hφx₀] at hφu
      have := le_max_left p p₀
      linarith
    · have hlt2 := hmono hx₀ hu hlt
      rw [hφx₀, hφu] at hlt2
      have := le_max_left p p₀
      linarith
  have hxv : x₀ < v := by
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hφv
      rw [hφx₀] at hφv
      have := min_le_left q q₀
      linarith
    · have hlt2 := hmono hv hx₀ hlt
      rw [hφx₀, hφv] at hlt2
      have := min_le_left q q₀
      linarith
  refine ⟨u, v, hux, hxv, fun y hy1 hy2 => ?_⟩
  have hyIoo : y ∈ Set.Ioo c d := ⟨lt_trans hu.1 hy1, lt_trans hy2 hv.2⟩
  have h1 := hmono hu hyIoo hy1
  have h2 := hmono hyIoo hv hy2
  rw [hφu] at h1
  rw [hφv] at h2
  constructor
  · have := le_max_right p p₀
    linarith
  · have := min_le_right q q₀
    linarith

/-- **The decreasing kill** (mirrored by hand — negation is not an atom). -/
theorem strictAntiOn_exists_continuityPt {S : OMinStructure} {φ : ℝ → ℝ}
    (hφ : S.DefinableFun φ) {c d : ℝ} (hcd : c < d)
    (hanti : StrictAntiOn φ (Set.Ioo c d)) :
    ∃ x ∈ Set.Ioo c d, ContinuousAt φ x := by
  obtain ⟨p, q, hpq, hsub⟩ := tame_infinite_contains_Ioo (tame_image hφ c d)
    ((Set.infinite_image_iff hanti.injOn).mpr (Set.Ioo_infinite hcd))
  have hm : (p + q) / 2 ∈ Set.Ioo p q := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  obtain ⟨x₀, hx₀, hφx₀⟩ := hsub hm
  rw [Set.mem_Ioo] at hm
  refine ⟨x₀, hx₀, ?_⟩
  rw [continuousAt_iff_order]
  intro p₀ q₀ hp₀ hq₀
  rw [hφx₀] at hp₀ hq₀
  have hmaxm : max p p₀ < (p + q) / 2 := max_lt hm.1 hp₀
  have hminm : (p + q) / 2 < min q q₀ := lt_min hm.2 hq₀
  have hsA : (max p p₀ + (p + q) / 2) / 2 ∈ Set.Ioo p q := by
    rw [Set.mem_Ioo]
    constructor
    · have := le_max_left p p₀
      linarith
    · linarith
  obtain ⟨u, hu, hφu⟩ := hsub hsA
  have htA : ((p + q) / 2 + min q q₀) / 2 ∈ Set.Ioo p q := by
    rw [Set.mem_Ioo]
    constructor
    · linarith
    · have := min_le_left q q₀
      linarith
  obtain ⟨v, hv, hφv⟩ := hsub htA
  have hxu : x₀ < u := by
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hφu
      rw [hφx₀] at hφu
      have := le_max_left p p₀
      linarith
    · have hlt2 := hanti hu hx₀ hlt
      rw [hφx₀, hφu] at hlt2
      have := le_max_left p p₀
      linarith
  have hvx : v < x₀ := by
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq] at hφx₀
      rw [hφx₀] at hφv
      have := min_le_left q q₀
      linarith
    · have hlt2 := hanti hx₀ hv hlt
      rw [hφx₀, hφv] at hlt2
      have := min_le_left q q₀
      linarith
  refine ⟨v, u, hvx, hxu, fun y hy1 hy2 => ?_⟩
  have hyIoo : y ∈ Set.Ioo c d := ⟨lt_trans hv.1 hy1, lt_trans hy2 hu.2⟩
  have h1 := hanti hv hyIoo hy1
  have h2 := hanti hyIoo hu hy2
  rw [hφv] at h1
  rw [hφu] at h2
  constructor
  · have := le_max_right p p₀
    linarith
  · have := min_le_right q q₀
    linarith

/-- The constant case: every point of a constancy interval is a continuity point. -/
theorem constOn_continuousAt {φ : ℝ → ℝ} {c d : ℝ}
    (hconst : ∀ x ∈ Set.Ioo c d, ∀ y ∈ Set.Ioo c d, φ x = φ y) :
    ∀ x ∈ Set.Ioo c d, ContinuousAt φ x := by
  intro x hx
  rw [continuousAt_iff_order]
  intro p₀ q₀ hp₀ hq₀
  refine ⟨c, d, hx.1, hx.2, fun y h1 h2 => ?_⟩
  have he := hconst y ⟨h1, h2⟩ x hx
  rw [he]
  exact ⟨hp₀, hq₀⟩

end Sundog.OMinimalAbstract
