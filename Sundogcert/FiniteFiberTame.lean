/-
# The finite-fiber core — threshold tameness beyond monotonicity.

The monotone-activation factory (`SigmoidTame`) proves threshold sets tame from
CONTINUITY + INJECTIVITY. Injectivity is only used to make the level set a subsingleton,
hence finite. This module makes that explicit: the real hypothesis is a **finite level
set**, and injectivity is one way (not the only way) to get it.

- `tame_level_of_finite` / `tame_superlevel_of_finite` / `tame_sublevel_of_finite` /
  `tame_le_of_finite` / `tame_ge_of_finite` — for a continuous `f` with a finite fiber
  `{x | f x = c}`, every threshold set at `c` is tame. Same proofs as the injective
  core (R1's `frontier_superlevel_subset` sends the threshold frontier into the level
  set), with "subsingleton" relaxed to "finite".

This is the entry point for **non-monotone** activations: any continuous `f` that is
piecewise-strictly-monotone with finitely many pieces has finite fibers, so its
threshold sets are tame — the injective core is the one-piece special case. The first
consumer is GELU (two monotone branches).
-/
import Sundogcert.SigmoidTame

namespace Sundog.OMinimalFiber

open Sundog.OMinimalOne Sundog.OMinimalSigmoid

/-- A finite level set is tame. -/
theorem tame_level_of_finite {f : ℝ → ℝ} {c : ℝ}
    (hfin : {x | f x = c}.Finite) : Tame {x | f x = c} :=
  tame_of_finite hfin

/-- Strict superlevel sets are tame when the level set is finite. -/
theorem tame_superlevel_of_finite {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hfin : {x | f x = c}.Finite) : Tame {x | c < f x} :=
  (tame_of_finite hfin).subset (frontier_superlevel_subset hf c)

/-- Strict sublevel sets are tame when the level set is finite. -/
theorem tame_sublevel_of_finite {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hfin : {x | f x = c}.Finite) : Tame {x | f x < c} := by
  have hnegfin : {x | (fun x => -f x) x = -c}.Finite := by
    have e : {x | (fun x => -f x) x = -c} = {x | f x = c} := by
      ext x; simp only [Set.mem_setOf_eq, neg_inj]
    rw [e]; exact hfin
  have h := tame_superlevel_of_finite (f := fun x => -f x) hf.neg hnegfin
  have e2 : {x : ℝ | -c < -f x} = {x | f x < c} := by
    ext x; simp only [Set.mem_setOf_eq, neg_lt_neg_iff]
  rwa [e2] at h

/-- Non-strict sublevel (`≤`) sets are tame when the level set is finite. -/
theorem tame_le_of_finite {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hfin : {x | f x = c}.Finite) : Tame {x | f x ≤ c} := by
  have h := tame_compl (tame_superlevel_of_finite hf hfin)
  have e : {x : ℝ | c < f x}ᶜ = {x | f x ≤ c} := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rwa [e] at h

/-- Non-strict superlevel (`≥`) sets are tame when the level set is finite. -/
theorem tame_ge_of_finite {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hfin : {x | f x = c}.Finite) : Tame {x | c ≤ f x} := by
  have h := tame_compl (tame_sublevel_of_finite hf hfin)
  have e : {x : ℝ | f x < c}ᶜ = {x | c ≤ f x} := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rwa [e] at h

end Sundog.OMinimalFiber
