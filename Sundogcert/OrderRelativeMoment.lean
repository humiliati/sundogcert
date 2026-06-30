/-
# OrderRelative — a spectral / moment-order axis (the determine/resist law's own home)

A fifth instance family for the Order-Relative Resolution Law, drawn from the measure-theoretic
determine/resist law (`ShadowDecayCauchy`): DETERMINE needs a finite first moment (the mean), so the
**moment order** of a population is `1` if its mean exists and `⊤` if it does not.

This brings the law's progenitor — the determine/resist split — into the schema, and it reveals a
BOUNDARY: the determine side is essentially **binary** (mean exists → order 1; no mean → `⊤`), NOT
a richly graded order like denominator/radical. So the determine/resist split fits the schema, but
as a finite-mean-vs-no-mean dichotomy (order 1 vs `⊤`) — the content is in the EARNED `⊤` pole —
the standard **Cauchy** population (no first moment), via the machine-checked
`ShadowDecayCauchy.cauchy_no_mean`. (Gaussian, with a finite mean, is order 1.)
-/
import Sundogcert.OrderRelative
import Sundogcert.ShadowDecayCauchy

namespace Sundog.OrderRelative.Moment

open Sundog.OrderRelative Sundog.ShadowDecay Sundog.ShadowDecayGeneral Sundog.ShadowDecayCauchy
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A budget of `≥ 1` moment resolves the latent iff the population's first moment exists. -/
def MomentResolves (μ : Measure ℝ) (k : ℕ) : Prop := 1 ≤ k ∧ Integrable (fun x : ℝ => x) μ

/-- **A finite-mean population has moment order 1** — the determine side: the mean pins it. -/
def momentProblem (μ : Measure ℝ) (hμ : Integrable (fun x : ℝ => x) μ) : Problem where
  Target := Unit
  ord _ := 1
  Resolves k _ := MomentResolves μ k
  resolves_iff k _ := by
    simp only [MomentResolves, hμ, and_true]
    exact_mod_cast Iff.rfl

/-- **The Cauchy population has moment order `⊤`** — the EARNED resist pole: it has no first moment
(`ShadowDecayCauchy.cauchy_no_mean`), so no finite moment budget pins it. -/
def cauchyMomentProblem (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) : Problem where
  Target := Unit
  ord _ := ⊤
  Resolves k _ := MomentResolves (cauchyMeasure x₀ γ) k
  resolves_iff k _ := by
    constructor
    · rintro ⟨_, hInt⟩
      exact (cauchy_no_mean x₀ γ hγ hInt).elim
    · intro hk
      exact absurd (top_le_iff.mp hk) WithTop.coe_ne_top

/-- The Cauchy moment instance is an EARNED resist pole — no finite moment budget resolves it
(instantiating `resists_iff_infinite`, grounded on `cauchy_no_mean`). -/
theorem cauchyMoment_resists (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    ∀ k : ℕ, ¬ (cauchyMomentProblem x₀ γ hγ).Resolves k () :=
  (resists_iff_infinite (cauchyMomentProblem x₀ γ hγ) (t := ())).2 rfl

/-- **The moment axis is binary — determine order 1 vs resist `⊤`.** A Gaussian population (finite
mean) has moment order 1; a Cauchy population (no mean) has moment order `⊤`. The determine/resist
law fits the schema, but as a finite-mean-vs-no-mean dichotomy — not a richly graded order. -/
theorem moment_gaussian_vs_cauchy (x₀ : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) :
    (momentProblem stdGaussian gaussian_resist_and_determine.2.1).ord () = 1
      ∧ (cauchyMomentProblem x₀ γ hγ).ord () = ⊤ :=
  ⟨rfl, rfl⟩

end Sundog.OrderRelative.Moment
