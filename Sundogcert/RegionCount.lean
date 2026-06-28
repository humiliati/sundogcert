/-
# Linear regions are an exact (realization-independent) tropical invariant (C-A1)

The Lean realization of slate hook **C-A1**. The number of *linear regions* of a ReLU
network is a much-studied expressivity measure (Montúfar–Pascanu–Cho–Bengio 2014;
Serra–Tjandraatmadja–Ramalingam 2018) — but only *bounds* are known. Here the point is
sharper and provable: because `CircuitNet.compile` is **exact** (`compile_eval`), a compiled
ReLU net computes the *identical* function to its source tropical circuit, so its entire
linear-region structure is **realization-independent** — an intrinsic property of the
tropical function, not of the ReLU wiring.

## What is PROVED here

* **`realize1_compile` / `affine_compile_iff` (the intrinsic-ness, falsifier-killer).** The
  compiled ReLU net's 1-D realization equals the source tropical circuit's, so *any*
  region/affine property is shared. The falsifier `REGIONS_NOT_INTRINSIC` — "the region
  count depends on the realization" — fails *because compilation is exact*.
* **`max_two_not_affine` (the region anchor).** A tropical `max` of two affine functions
  with **distinct slopes** is **not globally affine** — a genuine region boundary, so ≥ 2
  linear regions. Proof: `max ≥ gᵢ` everywhere makes the affine candidate dominate each
  line, and an affine function that is `≥ 0` everywhere has zero slope
  (`affine_nonneg_const`), forcing the candidate's slope to equal *both* `a₁` and `a₂`.
  It is also affine on each half (`max_eq_left`/`right`), so exactly 2 regions.
* **`compiled_maxGate_not_affine` (the capstone).** The compiled ReLU net of a
  distinct-slope tropical `max` gate has ≥ 2 linear regions, and this is intrinsic
  (= the source), by exactness.

## The IMPORTED WALL (named, NOT proved here)

* **The exact region-count *formula* for a general tropical circuit** (regions = chambers of
  the tropical-hypersurface arrangement / mixed volume of Newton polytopes) is the
  geometry the literature bounds rather than computes; this module proves intrinsic-ness
  and the atomic-gate count, not the general closed form. That formula is the named wall.

## References
* Montúfar, Pascanu, Cho, Bengio, *On the number of linear regions of deep neural
  networks*, NeurIPS 2014 (bounds, not exact counts).
* Zhang, Naitzat, Lim, *Tropical geometry of deep neural networks*, ICML 2018
  (ReLU nets ↔ tropical rational maps; regions ↔ tropical hypersurfaces).
-/
import Sundogcert.CircuitNet

namespace Sundog.RegionCount

open Sundog.CircuitNet

/-- A 1-D function is (globally) **affine** — "a single linear region". -/
def Affine (f : ℝ → ℝ) : Prop := ∃ a b : ℝ, ∀ x, f x = a * x + b

/-- An affine function that is `≥ 0` everywhere must have **zero slope** (be constant). The
unboundedness witness `x = -(b+1)/a` makes a nonzero-slope line negative. -/
theorem affine_nonneg_const {a b : ℝ} (h : ∀ x, 0 ≤ a * x + b) : a = 0 := by
  by_contra ha
  have hx := h (-(b + 1) / a)
  have he : a * (-(b + 1) / a) + b = -1 := by field_simp; ring
  rw [he] at hx
  norm_num at hx

/-- **The region anchor.** A tropical `max` of two affine functions with *distinct slopes*
is **not globally affine**: it has a genuine region boundary (≥ 2 linear regions). -/
theorem max_two_not_affine {a₁ b₁ a₂ b₂ : ℝ} (hne : a₁ ≠ a₂) :
    ¬ Affine (fun x => max (a₁ * x + b₁) (a₂ * x + b₂)) := by
  rintro ⟨c, d, h⟩
  have h1 : ∀ x, 0 ≤ (c - a₁) * x + (d - b₁) := by
    intro x
    have hle : a₁ * x + b₁ ≤ c * x + d := by rw [← h x]; exact le_max_left _ _
    have hid : (c - a₁) * x + (d - b₁) = (c * x + d) - (a₁ * x + b₁) := by ring
    rw [hid]; linarith
  have h2 : ∀ x, 0 ≤ (c - a₂) * x + (d - b₂) := by
    intro x
    have hle : a₂ * x + b₂ ≤ c * x + d := by rw [← h x]; exact le_max_right _ _
    have hid : (c - a₂) * x + (d - b₂) = (c * x + d) - (a₂ * x + b₂) := by ring
    rw [hid]; linarith
  have e1 := affine_nonneg_const h1
  have e2 := affine_nonneg_const h2
  exact hne (by linarith)

/-- `max` is affine on the side where the first line dominates (one of the ≤ 2 pieces). -/
theorem max_affine_left {a₁ b₁ a₂ b₂ x : ℝ} (hx : a₂ * x + b₂ ≤ a₁ * x + b₁) :
    max (a₁ * x + b₁) (a₂ * x + b₂) = a₁ * x + b₁ := max_eq_left hx

/-- The 1-D realization of a single-input tropical circuit. -/
def realize1 (e : Trop 1) : ℝ → ℝ := fun t => e.eval (fun _ => t)

/-- The 1-D realization of a single-input ReLU network. -/
def realize1N (g : Net 1) : ℝ → ℝ := fun t => g.eval (fun _ => t)

/-- **Intrinsic-ness (the falsifier-killer).** The compiled ReLU net realizes the *same*
1-D function as the source tropical circuit — by `compile_eval`. So its entire
linear-region structure is realization-independent. -/
theorem realize1_compile (e : Trop 1) : realize1N (compile e) = realize1 e := by
  funext t; exact compile_eval e (fun _ => t)

/-- Consequently any region/affine property transfers between the source and its
compilation: linear regions are an *intrinsic* invariant, because compilation is exact. -/
theorem affine_compile_iff (e : Trop 1) :
    Affine (realize1N (compile e)) ↔ Affine (realize1 e) := by
  rw [realize1_compile]

/-- The affine `Trop` circuit `a·x + b`. -/
def affineCirc (a b : ℝ) : Trop 1 := .add (.scale a (.var 0)) (.const b)

@[simp] theorem affineCirc_realize (a b : ℝ) (t : ℝ) :
    realize1 (affineCirc a b) t = a * t + b := by
  simp [realize1, affineCirc, Trop.eval_add, Trop.eval_scale, Trop.eval_var, Trop.eval_const]

/-- The atomic tropical `max` gate of two affine inputs. -/
def maxGate (a₁ b₁ a₂ b₂ : ℝ) : Trop 1 := .max (affineCirc a₁ b₁) (affineCirc a₂ b₂)

theorem maxGate_realize (a₁ b₁ a₂ b₂ : ℝ) :
    realize1 (maxGate a₁ b₁ a₂ b₂) = fun t => max (a₁ * t + b₁) (a₂ * t + b₂) := by
  funext t
  simp [realize1, maxGate, affineCirc, Trop.eval_max, Trop.eval_add, Trop.eval_scale,
    Trop.eval_var, Trop.eval_const]

/-- **Capstone.** The compiled ReLU net of a distinct-slope tropical `max` gate has ≥ 2
linear regions (not globally affine), and this region structure is *intrinsic* — identical
to the source tropical circuit's — because `compile` is exact. -/
theorem compiled_maxGate_not_affine {a₁ b₁ a₂ b₂ : ℝ} (hne : a₁ ≠ a₂) :
    ¬ Affine (realize1N (compile (maxGate a₁ b₁ a₂ b₂))) := by
  rw [realize1_compile, maxGate_realize]
  exact max_two_not_affine hne

end Sundog.RegionCount

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`, NO `native_decide`.
#print axioms Sundog.RegionCount.realize1_compile
#print axioms Sundog.RegionCount.max_two_not_affine
#print axioms Sundog.RegionCount.compiled_maxGate_not_affine
