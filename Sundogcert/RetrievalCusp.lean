import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Sundogcert.ContextDecay

/-!
# Retrieval cusp — the attractor-memory landscape realizes the rule (H-II mapping)

This is the last H-II step: the bridge from the proved catastrophe germ
(`CuspGerm.lean`) toward an actual memory. It does **not** prove that a real vector
database *is* a cusp — that empirical/modelling claim is, and stays, the named import.
What it does is shrink that import to a crisp, interpretable model and prove the model
realizes `ContextDecay`.

The canonical model of associative / attractor memory (Hopfield-style energy
landscapes) is a double-well energy whose minima are the stored patterns. The
symmetric two-pattern landscape, with control `a` (pattern separation / freshness), is
the symmetric cusp:

  `V_a(x) = x⁴/4 − a·x²/2`,  `V_a'(x) = x³ − a·x = x·(x² − a)`,  `V_a''(x) = 3x² − a`.

Its critical points — the stored memories together with the barrier between them — are
the roots of `V_a'`:

  * `a > 0` → `{0, √a, −√a}`: two **memories** `±√a` (minima, `V'' > 0`) separated by a
    **barrier** `0` (maximum, `V'' < 0`) — three critical points;
  * `a < 0` → `{0}`: the barrier is gone and the wells have merged into one — one
    critical point.

So as freshness `a` decays through 0 the critical-point count drops `3 → 1`: a
fold-pair annihilation, i.e. a `ContextDecay.Decays` event. The two memories become
indistinguishable. The cusp point `a = 0` is the degenerate merge locus; the
annihilation is witnessed strictly between `a₁ > 0` and `a₀ < 0`.

**Named import (now narrow).** The remaining unproved bridge is only: *a real
retrieval landscape is (locally) this attractor energy with a decaying barrier*. That
the model realizes the rule is proved here; whether real memory fits the model is the
empirical question (testable with `scripts/foldpair_detector.py` on real retrieval
curves).
-/

namespace Sundog.RetrievalCusp

open Sundog.ContextDecay

/-- Two-pattern attractor-memory energy with control `a` (pattern separation /
freshness). Stored memories are its minima; retrieval settles into a minimum. -/
noncomputable def V (a x : ℝ) : ℝ := x ^ 4 / 4 - a * x ^ 2 / 2

/-- The gradient `V_a'(x) = x³ − a·x`. Critical points (memories + barrier) are its
roots. (Equals `deriv (V a)` by elementary calculus; used here directly.) -/
def dV (a x : ℝ) : ℝ := x ^ 3 - a * x

/-- The curvature `V_a''(x) = 3x² − a`. The second-derivative test: `> 0` at a stored
memory, `< 0` at the barrier. -/
def ddV (a x : ℝ) : ℝ := 3 * x ^ 2 - a

/-- The retrieval landscape's critical points: the stored memories together with the
barrier between them. -/
def critSetW (a : ℝ) : Set ℝ := {x | dV a x = 0}

/-- Number of critical points (memories + barrier) of the retrieval landscape. -/
noncomputable def critCountW (a : ℝ) : ℕ := (critSetW a).ncard

theorem mem_critSetW {a x : ℝ} : x ∈ critSetW a ↔ x ^ 3 - a * x = 0 := Iff.rfl

/-- For `a < 0` the barrier is gone and the wells have merged: the only critical point
is `0` (`x² − a > 0` everywhere). -/
theorem critSetW_neg {a : ℝ} (ha : a < 0) : critSetW a = {0} := by
  ext x
  simp only [mem_critSetW, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hf : x * (x ^ 2 - a) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp hf with h | h
    · exact h
    · exfalso; nlinarith [sq_nonneg x]
  · rintro rfl; ring

theorem critCountW_neg {a : ℝ} (ha : a < 0) : critCountW a = 1 := by
  unfold critCountW
  rw [critSetW_neg ha, Set.ncard_singleton]

/-- For `a > 0` the landscape has two memories `±√a` and a barrier `0`: three critical
points. -/
theorem critSetW_pos {a : ℝ} (ha : 0 < a) :
    critSetW a = {0, Real.sqrt a, -Real.sqrt a} := by
  set r := Real.sqrt a with hr
  have hr2 : r ^ 2 = a := Real.sq_sqrt ha.le
  ext x
  simp only [mem_critSetW, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hf : x * (x - r) * (x + r) = 0 := by linear_combination hx - x * hr2
    rcases mul_eq_zero.mp hf with h | h
    · rcases mul_eq_zero.mp h with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl)
    · ring
    · linear_combination r * hr2
    · linear_combination (-r) * hr2

theorem critCountW_pos {a : ℝ} (ha : 0 < a) : critCountW a = 3 := by
  unfold critCountW
  rw [critSetW_pos ha]
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [Set.ncard_eq_three]
  refine ⟨0, Real.sqrt a, -Real.sqrt a, ne_of_lt hr, ?_, ?_⟩
  · intro h; linarith
  · refine ⟨?_, rfl⟩
    intro h; linarith

/-- **The two memories are stable minima; the barrier is a maximum.** For `a > 0`,
`V'' > 0` at the stored memories `±√a` and `V'' < 0` at the barrier `0`. As `a → 0⁺`
the barrier vanishes and the two memories merge — the annihilation `critCountW` records
(3 → 1). -/
theorem memories_are_minima {a : ℝ} (ha : 0 < a) :
    0 < ddV a (Real.sqrt a) ∧ 0 < ddV a (-Real.sqrt a) ∧ ddV a 0 < 0 := by
  have hr2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  simp only [ddV]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hr2, ha]

/-- **Mapping grounding — the attractor-memory landscape realizes a `ContextDecay`
annihilation.** For freshness `a₀ < 0 < a₁`, the critical-count family
`[critCountW a₁, critCountW a₀] = [3, 1]` is a `ContextDecay.Decays` event: as freshness
decays the two stored memories merge, exactly the abstract drop-by-two the quarantine
rule keys on. The model realizes the rule; only the model-fits-reality bridge remains
imported. -/
theorem retrieval_realizes_annihilation {a₀ a₁ : ℝ} (h0 : a₀ < 0) (h1 : 0 < a₁) :
    Decays [critCountW a₁, critCountW a₀] := by
  rw [critCountW_pos h1, critCountW_neg h0]
  exact ⟨[], 3, 1, [], rfl, rfl⟩

/-- Read through the `ContextDecay` headline: the memory landscape's critical-count
family exhibits a genuine fold pair (≥ 2) annihilating as freshness decays. -/
theorem retrieval_foldpair_witness {a₀ a₁ : ℝ} (h0 : a₀ < 0) (h1 : 0 < a₁) :
    ∃ l a b r, [critCountW a₁, critCountW a₀] = l ++ a :: b :: r ∧ 2 ≤ a ∧ a = b + 2 :=
  decays_iff_foldpair.mp (retrieval_realizes_annihilation h0 h1)

end Sundog.RetrievalCusp

-- Axiom audit (real-analysis attractor model ⇒ expect the full foundational triple).
#print axioms Sundog.RetrievalCusp.critCountW_neg
#print axioms Sundog.RetrievalCusp.critCountW_pos
#print axioms Sundog.RetrievalCusp.memories_are_minima
#print axioms Sundog.RetrievalCusp.retrieval_realizes_annihilation
#print axioms Sundog.RetrievalCusp.retrieval_foldpair_witness
