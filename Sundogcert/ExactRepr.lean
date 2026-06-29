/-
# Exact representability — every convex continuous-PL function is a finite ReLU net (S3-1)

Slate-3 hook **S3-1**: the *characterization of universal approximation* at ε = 0. A 1-D
function is exactly representable by a finite ReLU network iff it is continuous piecewise-linear
with finitely many pieces. `HasPieceCover f k` is exactly that predicate (`f` is affine off a
finite cut set, hence continuous PL with `≤ k` pieces — `LineOn` is exact equality, and includes
the endpoints, so adjacent pieces agree).

This module lands the **convex case of the converse** (CPL ⟹ ReLU): a convex `HasPieceCover`
function is the realization of an explicit ReLU net. The construction is canonical — a convex PL
function is the upper envelope of its piece-lines (`convex_eq_sup_lines`), the upper envelope is a
tropical `max`-circuit (`linesTrop`), and a tropical circuit compiles exactly to a ReLU net
(`compile`/`realize1_compile`). The general (non-convex) converse — `f` as a difference of two
convex envelopes — and the forward direction (ReLU ⟹ CPL) are the staged extensions.
-/
import Sundogcert.RegionPoly

namespace Sundog.ExactRepr

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.RegionPoly

/-! ### `max` over a list, at the value level (bounds) -/

theorem foldlMax_le {α : Type*} (g : α → ℝ) (l : List α) (base c : ℝ)
    (hb : base ≤ c) (hmem : ∀ a ∈ l, g a ≤ c) :
    l.foldl (fun acc a => max acc (g a)) base ≤ c := by
  induction l generalizing base with
  | nil => simpa using hb
  | cons hd tl ih =>
    rw [List.foldl_cons]
    exact ih (max base (g hd)) (max_le hb (hmem hd List.mem_cons_self))
      (fun a ha => hmem a (List.mem_cons_of_mem hd ha))

theorem le_foldlMax_base {α : Type*} (g : α → ℝ) (l : List α) (base : ℝ) :
    base ≤ l.foldl (fun acc a => max acc (g a)) base := by
  induction l generalizing base with
  | nil => simp
  | cons hd tl ih => rw [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih (max base (g hd)))

theorem le_foldlMax_mem {α : Type*} (g : α → ℝ) {a : α} :
    ∀ (l : List α) (base : ℝ), a ∈ l → g a ≤ l.foldl (fun acc a => max acc (g a)) base := by
  intro l
  induction l with
  | nil => intro base ha; simp at ha
  | cons hd tl ih =>
    intro base ha
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | htl
    · exact le_trans (le_max_right _ _) (le_foldlMax_base g tl _)
    · exact ih (max base (g hd)) htl

/-! ### `max` over a list of lines, as a tropical circuit -/

/-- A nonempty list of lines `(slope, intercept)` as a tropical `max`-circuit. -/
def linesTrop : List (ℝ × ℝ) → Trop 1
  | [] => Trop.const 0
  | pr :: rest => rest.foldl (fun acc q => Trop.max acc (affineCirc q.1 q.2)) (affineCirc pr.1 pr.2)

/-- The realization of a `foldl` of `max`-with-affine-gates is the value-level `foldl` of `max`. -/
theorem realize1_foldl (rest : List (ℝ × ℝ)) (init : Trop 1) (x : ℝ) :
    realize1 (rest.foldl (fun acc q => Trop.max acc (affineCirc q.1 q.2)) init) x
      = rest.foldl (fun acc q => max acc (q.1 * x + q.2)) (realize1 init x) := by
  induction rest generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (Trop.max init (affineCirc hd.1 hd.2))]
    have hbase : realize1 (Trop.max init (affineCirc hd.1 hd.2)) x
        = max (realize1 init x) (hd.1 * x + hd.2) := by
      simp [realize1_max, affineCirc_realize]
    rw [hbase]

/-! ### The converse, convex case -/

/-- **Convex continuous-PL ⟹ ReLU (exact).** Every convex function with a finite piece cover is
the exact realization of a finite ReLU network — built as the upper envelope of its piece-lines,
compiled through the tropical→ReLU compiler. The first ε = 0 representability direction. -/
theorem convexCPL_realizable {f : ℝ → ℝ} {n : ℕ}
    (hconv : ConvexOn ℝ Set.univ f) (hpc : HasPieceCover f n) :
    ∃ g : Net 1, realize1N g = f := by
  obtain ⟨L, _, hle, hach⟩ := convex_eq_sup_lines hconv hpc
  have hne : L.toList ≠ [] := by
    obtain ⟨pr, hpr, _⟩ := hach 0
    intro h
    rw [List.eq_nil_iff_forall_not_mem] at h
    exact h pr (Finset.mem_toList.mpr hpr)
  obtain ⟨hd, tl, hLa⟩ := List.exists_cons_of_ne_nil hne
  have hhdL : hd ∈ L := Finset.mem_toList.mp (by rw [hLa]; exact List.mem_cons_self)
  have htlL : ∀ a ∈ tl, a ∈ L :=
    fun a ha => Finset.mem_toList.mp (by rw [hLa]; exact List.mem_cons_of_mem hd ha)
  refine ⟨compile (linesTrop L.toList), ?_⟩
  rw [realize1_compile]
  funext x
  rw [hLa]
  simp only [linesTrop]
  rw [realize1_foldl, affineCirc_realize]
  apply le_antisymm
  · exact foldlMax_le (fun q => q.1 * x + q.2) tl (hd.1 * x + hd.2) (f x)
      (hle hd hhdL x) (fun a ha => hle a (htlL a ha) x)
  · obtain ⟨pr, hpr, hprx⟩ := hach x
    rw [hprx]
    have hprLa : pr ∈ hd :: tl := by rw [← hLa]; exact Finset.mem_toList.mpr hpr
    rcases List.mem_cons.mp hprLa with rfl | hprtl
    · exact le_foldlMax_base (fun q => q.1 * x + q.2) tl (pr.1 * x + pr.2)
    · exact le_foldlMax_mem (fun q => q.1 * x + q.2) tl (hd.1 * x + hd.2) hprtl

end Sundog.ExactRepr
