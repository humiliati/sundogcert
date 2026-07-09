/-
# Finite critical points ⇒ finite fibers (Rolle counting).

The reusable engine for non-monotone fiber-finiteness. If a differentiable
`g : ℝ → ℝ` has finitely many critical points (`{g' = 0}` finite), then every level set
`{g = c}` is finite: an infinite level set would yield, by Rolle between consecutive
points, arbitrarily many distinct critical points.

`finite_fiber_of_finite_deriv_zeros` — the statement. Applied twice it cracks any
`C²` activation whose SECOND derivative has finitely many zeros: `{g'' = 0}` finite ⇒
`{g' = 0}` finite ⇒ `{g = c}` finite. GELU is the first consumer (`g'' = φ·(2 − x²)`,
`φ > 0`, so `{g'' = 0} = {±√2}`).
-/
import Sundogcert.SigmoidTame
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace Sundog.OMinimalFiber

/-- **Rolle counting.** A differentiable function with finitely many critical points has
finite fibers. -/
theorem finite_fiber_of_finite_deriv_zeros {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hZ : {x : ℝ | g' x = 0}.Finite) (c : ℝ) :
    {x : ℝ | g x = c}.Finite := by
  classical
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  by_contra hinf
  rw [Set.not_finite] at hinf
  set N := hZ.toFinset.card with hN
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (N + 2)
  set e := T.orderEmbOfFin hTcard with he
  have hgval : ∀ i : Fin (N + 2), g (e i) = c := fun i =>
    hTsub (Finset.mem_coe.mpr (Finset.orderEmbOfFin_mem T hTcard i))
  -- Rolle between consecutive sample points
  have hz : ∀ i : Fin (N + 1), ∃ z, e i.castSucc < z ∧ z < e i.succ ∧ g' z = 0 := by
    intro i
    have hlt : e i.castSucc < e i.succ := e.strictMono Fin.castSucc_lt_succ
    obtain ⟨z, hzI, hz0⟩ := exists_hasDerivAt_eq_zero (f := g) (f' := g') hlt
      hgc.continuousOn ((hgval i.castSucc).trans (hgval i.succ).symm) (fun x _ => hg x)
    exact ⟨z, hzI.1, hzI.2, hz0⟩
  choose z hz1 hz2 hz3 using hz
  -- the critical points are distinct (strictly increasing in i)
  have hzmono : StrictMono z := by
    intro i j hij
    have h1 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      have : (i : ℕ) < (j : ℕ) := hij
      omega
    calc z i < e i.succ := hz2 i
      _ ≤ e j.castSucc := e.monotone h1
      _ < z j := hz1 j
  -- N+1 distinct critical points, but there are only N — contradiction
  have hsub : Finset.univ.image z ⊆ hZ.toFinset := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨i, _, rfl⟩ := hw
    rw [Set.Finite.mem_toFinset]
    exact hz3 i
  have hcard : (Finset.univ.image z).card = N + 1 := by
    rw [Finset.card_image_of_injective _ hzmono.injective, Finset.card_univ,
      Fintype.card_fin]
  have := Finset.card_le_card hsub
  omega

end Sundog.OMinimalFiber
