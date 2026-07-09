/-
# Dimension-one sigmoid tameness — a mini-witness off R1.

The full sigmoid class needs the o-minimality of the real exponential field (Wilkie),
which no proof assistant has formalized and which the Cohen–Hörmander route cannot
reach. But the DIMENSION-ONE fragment is already ours, straight off R1's finite-frontier
`Tame`, with no exponential structure — only monotonicity and continuity.

- **`tame_sublevel_of_injective` / `tame_superlevel_of_injective` / `_le / _ge / _level`**
  — for a continuous injective `f : ℝ → ℝ`, every threshold set `{x | f x ⋛ c}` and the
  level set `{x | f x = c}` are tame. The engine is R1's `frontier_superlevel_subset`
  (a continuous superlevel frontier sits inside the level-set frontier) plus: an
  injective level set is a subsingleton, hence finite. No monotonicity of the *set*
  structure is invoked — continuity + injectivity suffice.
- **`sigmoid` + `sigmoid_continuous` + `sigmoid_strictMono`** — the concrete logistic
  `σ(x) = (1 + eˣ⁻ ')⁻¹` is continuous and strictly increasing (hence injective), from
  mathlib's `Real.exp` monotonicity. Transcendental, so NOT reachable through the
  semialgebraic witness — this is genuinely the exponential activation, in dimension one.
- **`sigmoid_lt_tame … sigmoid_eq_tame`** — every one-variable sigmoid threshold on an
  affine pre-image `σ(a·x + b)` (any `a ≠ 0`) is tame.
- **`sigmoid_band_tame`, `sigmoid_dnf_tame`** — the class closes: two-sided bands
  (intersections) and arbitrary finite unions of bands (a DNF) stay tame, via R1's
  Boolean closure of `Tame`.

**Honest fence.** Dimension one only. Composition and dimension ≥ 2 — a two-layer
sigmoid net's region in ℝ² — need the projection / quantifier elimination that only the
exponential structure supplies; that witness (`expStructure : OMinStructure`) is a
parked wall, not a build.

*Pre-registered falsifiers* (all cleared): `SIGMOID_MONO_FRONTIER` (continuity+injectivity
fails to bound the threshold frontier — would break the core), `BOOL_CLOSURE_LEAK` (finite
Boolean combinations escape `Tame`), `SIGMOID_INSTANCE_VACUOUS` (the concrete logistic can't
be shown continuous+strictly-monotone in mathlib).
-/
import Sundogcert.OMinimalOne

namespace Sundog.OMinimalSigmoid

open Sundog.OMinimalOne

/-! ### Threshold sets of continuous injective functions are tame -/

/-- A finite set is tame (its frontier sits inside the closed set itself). -/
theorem tame_of_finite {s : Set ℝ} (h : s.Finite) : Tame s := by
  refine h.subset ?_
  calc frontier s ⊆ closure s := frontier_subset_closure
    _ = s := h.isClosed.closure_eq

/-- The level set of an injective function is a single point — tame. -/
theorem tame_level_of_injective {f : ℝ → ℝ} (hinj : Function.Injective f) (c : ℝ) :
    Tame {x | f x = c} :=
  tame_of_finite (Set.Subsingleton.finite fun _x hx _y hy => hinj (hx.trans hy.symm))

/-- Strict superlevel sets of a continuous injective function are tame. -/
theorem tame_superlevel_of_injective {f : ℝ → ℝ} (hf : Continuous f)
    (hinj : Function.Injective f) (c : ℝ) : Tame {x | c < f x} :=
  (tame_level_of_injective hinj c).subset (frontier_superlevel_subset hf c)

/-- Strict sublevel sets are tame (the superlevel argument applied to `-f`). -/
theorem tame_sublevel_of_injective {f : ℝ → ℝ} (hf : Continuous f)
    (hinj : Function.Injective f) (c : ℝ) : Tame {x | f x < c} := by
  have hneg : Function.Injective fun x => -f x := fun a b h => hinj (neg_injective h)
  have h := tame_superlevel_of_injective (f := fun x => -f x) hf.neg hneg (-c)
  have e : {x : ℝ | -c < -f x} = {x | f x < c} := by
    ext x; simp only [Set.mem_setOf_eq, neg_lt_neg_iff]
  rwa [e] at h

/-- Non-strict sublevel (`≤`) sets are tame. -/
theorem tame_le_of_injective {f : ℝ → ℝ} (hf : Continuous f)
    (hinj : Function.Injective f) (c : ℝ) : Tame {x | f x ≤ c} := by
  have h := tame_compl (tame_superlevel_of_injective hf hinj c)
  have e : {x : ℝ | c < f x}ᶜ = {x | f x ≤ c} := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rwa [e] at h

/-- Non-strict superlevel (`≥`) sets are tame. -/
theorem tame_ge_of_injective {f : ℝ → ℝ} (hf : Continuous f)
    (hinj : Function.Injective f) (c : ℝ) : Tame {x | c ≤ f x} := by
  have h := tame_compl (tame_sublevel_of_injective hf hinj c)
  have e : {x : ℝ | f x < c}ᶜ = {x | c ≤ f x} := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rwa [e] at h

/-- Finite unions of tame sets are tame (list fold form). -/
theorem tame_foldr_union : ∀ (l : List (Set ℝ)), (∀ s ∈ l, Tame s) →
    Tame (l.foldr (· ∪ ·) ∅)
  | [], _ => tame_empty
  | a :: l, h =>
    tame_union (h a List.mem_cons_self)
      (tame_foldr_union l fun s hs => h s (List.mem_cons_of_mem _ hs))

/-! ### The logistic sigmoid -/

/-- The logistic sigmoid `σ(x) = 1 / (1 + e^{-x})`. -/
noncomputable def sigmoid (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹

theorem sigmoid_denom_pos (x : ℝ) : (0 : ℝ) < 1 + Real.exp (-x) := by positivity

theorem sigmoid_continuous : Continuous sigmoid := by
  unfold sigmoid
  refine Continuous.inv₀ ?_ ?_
  · exact continuous_const.add (Real.continuous_exp.comp continuous_neg)
  · exact fun x => (sigmoid_denom_pos x).ne'

theorem sigmoid_strictMono : StrictMono sigmoid := by
  intro x y hxy
  have h1 : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  have hy : (0 : ℝ) < 1 + Real.exp (-y) := sigmoid_denom_pos y
  have h2 : (1 : ℝ) + Real.exp (-y) < 1 + Real.exp (-x) := by linarith
  change (1 + Real.exp (-x))⁻¹ < (1 + Real.exp (-y))⁻¹
  gcongr

theorem sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

/-! ### Sigmoid on an affine pre-image -/

theorem sigmoid_affine_continuous (a b : ℝ) :
    Continuous fun x => sigmoid (a * x + b) :=
  sigmoid_continuous.comp ((continuous_const.mul continuous_id).add continuous_const)

theorem sigmoid_affine_injective {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    Function.Injective fun x => sigmoid (a * x + b) := by
  have haff : Function.Injective fun x => a * x + b := by
    intro u v huv
    have hb : a * u + b = a * v + b := huv
    exact mul_left_cancel₀ ha (add_right_cancel hb)
  exact sigmoid_injective.comp haff

/-! ### The dimension-one sigmoid class is tame -/

theorem sigmoid_lt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | sigmoid (a * x + b) < r} :=
  tame_sublevel_of_injective (sigmoid_affine_continuous a b)
    (sigmoid_affine_injective ha b) r

theorem sigmoid_gt_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r < sigmoid (a * x + b)} :=
  tame_superlevel_of_injective (sigmoid_affine_continuous a b)
    (sigmoid_affine_injective ha b) r

theorem sigmoid_le_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | sigmoid (a * x + b) ≤ r} :=
  tame_le_of_injective (sigmoid_affine_continuous a b)
    (sigmoid_affine_injective ha b) r

theorem sigmoid_ge_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | r ≤ sigmoid (a * x + b)} :=
  tame_ge_of_injective (sigmoid_affine_continuous a b)
    (sigmoid_affine_injective ha b) r

theorem sigmoid_eq_tame {a : ℝ} (ha : a ≠ 0) (b r : ℝ) :
    Tame {x | sigmoid (a * x + b) = r} :=
  tame_level_of_injective (sigmoid_affine_injective ha b) r

/-- A two-sided sigmoid band is tame (an intersection of thresholds). -/
theorem sigmoid_band_tame {a : ℝ} (ha : a ≠ 0) (b r₁ r₂ : ℝ) :
    Tame {x | r₁ < sigmoid (a * x + b) ∧ sigmoid (a * x + b) < r₂} := by
  rw [Set.setOf_and]
  exact tame_inter (sigmoid_gt_tame ha b r₁) (sigmoid_lt_tame ha b r₂)

/-- **The class closes.** Any finite union of one-variable sigmoid bands — a disjunctive
normal form over affine-sigmoid thresholds — is tame. The dimension-one sigmoid class
is o-minimal-tame, with no exponential structure required. -/
theorem sigmoid_dnf_tame (specs : List (ℝ × ℝ × ℝ × ℝ))
    (ha : ∀ s ∈ specs, s.1 ≠ 0) :
    Tame ((specs.map fun s =>
        {x | s.2.2.1 < sigmoid (s.1 * x + s.2.1) ∧
          sigmoid (s.1 * x + s.2.1) < s.2.2.2}).foldr (· ∪ ·) ∅) := by
  refine tame_foldr_union _ ?_
  intro t ht
  rw [List.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact sigmoid_band_tame (ha s hs) s.2.1 s.2.2.1 s.2.2.2

end Sundog.OMinimalSigmoid
