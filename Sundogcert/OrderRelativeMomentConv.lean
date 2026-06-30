/-
# OrderRelative — the moment axis is join-homomorphic under convolution (the analysis residual)

Closes the one prose-fenced claim of the composition-law slate. The moment / integrability order
(order `1` if the first moment exists, `⊤` if not — see `OrderRelativeMoment`) is
**join-homomorphic under the independent sum** (= convolution of the laws):

> for independent `X, Y` on a probability space, `X + Y` is integrable **iff both `X` and `Y` are**.

The forward half is `Integrable.add`. The reverse half — *independent + sum-integrable ⟹ both
integrable* — is the part that genuinely needs independence (it is FALSE without it: take
`Y = -X` with `X` non-integrable, then `X + Y = 0`). It was the lane's lone analysis residual.
Here it is machine-checked, via the product-measure law of independence
(`indepFun_iff_map_prod_eq_prod_map_map`) + Fubini for integrability
(`integrable_prod_iff` / `integrable_prod_iff'`): the double integral being finite forces a finite
fibre for a.e. coordinate, and a good fibre EXISTS because the marginal laws are probability
measures (so their a.e. filter is `NeBot`); subtracting that fibre's constant leaves the marginal.
-/
import Sundogcert.OrderRelativeMoment
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace Sundog.OrderRelative.MomentConv

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

/-- **The moment / integrability order is join-homomorphic under the independent sum.** For
independent `X, Y` on a probability space, `X + Y` is integrable iff both `X` and `Y` are. In the
order language (`OrderRelativeMoment`): `ord (X+Y) = ord X ⊔ ord Y` on the `{1, ⊤}` chain. The
forward direction is `Integrable.add`; the reverse — the part that needs independence — is the
measure-theoretic residual, proved via the product-measure law + Fubini for integrability. -/
theorem indepFun_integrable_add_iff [IsProbabilityMeasure μ]
    (hXY : IndepFun X Y μ) (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => X ω + Y ω) μ ↔ Integrable X μ ∧ Integrable Y μ := by
  refine ⟨fun h => ?_, fun h => h.1.add h.2⟩
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  -- Independence ⟹ the joint law is the product of the marginals.
  have hmap : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hXY
  -- Transport integrability of the sum onto the product measure.
  have hprod : Integrable (fun p : ℝ × ℝ => p.1 + p.2) ((μ.map X).prod (μ.map Y)) := by
    rw [← hmap, integrable_map_measure hadd.aestronglyMeasurable (hX.prodMk hY).aemeasurable]
    exact h
  have hgidX : AEStronglyMeasurable (fun x : ℝ => x) (μ.map X) := measurable_id.aestronglyMeasurable
  have hgidY : AEStronglyMeasurable (fun y : ℝ => y) (μ.map Y) := measurable_id.aestronglyMeasurable
  -- Fubini: a finite fibre for a.e. coordinate (both orientations).
  obtain ⟨hYa, -⟩ := (integrable_prod_iff hadd.aestronglyMeasurable).mp hprod
  obtain ⟨hXa, -⟩ := (integrable_prod_iff' hadd.aestronglyMeasurable).mp hprod
  refine ⟨?_, ?_⟩
  · -- `Integrable X μ`: pick a good fibre `y₀`, subtract the constant, pull back through the map.
    obtain ⟨y₀, hy₀⟩ := hXa.exists
    have h2 : Integrable (fun x : ℝ => x) (μ.map X) :=
      (hy₀.sub (integrable_const y₀)).congr (ae_of_all _ fun x => by simp)
    rw [integrable_map_measure hgidX hX.aemeasurable] at h2
    exact h2
  · obtain ⟨x₀, hx₀⟩ := hYa.exists
    have h2 : Integrable (fun y : ℝ => y) (μ.map Y) :=
      (hx₀.sub (integrable_const x₀)).congr (ae_of_all _ fun y => by simp)
    rw [integrable_map_measure hgidY hY.aemeasurable] at h2
    exact h2

end Sundog.OrderRelative.MomentConv
