/-
# OrderRelative — an approximation axis: exactness is order-relative, ε-approximation is not

A fresh instance family for the Order-Relative Resolution Law, off the algo-approx lane
(`ExactRepr` / `UniversalApprox`). The break-first lesson: **pick the right axis**.

- The **ε-approximation axis COLLAPSES.** `continuous_relu_approximable` says *every*
  continuous `f` on `[0,1]` is ε-approximable by a ReLU net for every `ε > 0` — so "ε-approximable
  within budget" is always satisfiable, never `⊤`. Universality kills the determine/resist structure
  on this axis.

- The **EXACTNESS axis (`ε = 0`) does NOT collapse.** Order = exact ReLU-representability.
  **DETERMINE** = the function *is* a finite ReLU net (a continuous-PL function, finite order);
  **RESIST** = it is only approximable, never exact. The earned resist pole is `x²`: it is
  approximable (`AnalyticGate`) yet **not** a finite net (`sq_not_exactly_net`): a finite net
  is piecewise-linear (`ExactRepr.net_hasPieceCover`) and `x²` has no finite piece cover
  (`sq_no_pieceCover`, by strict convexity: on any gap interval it would be affine, impossible).

So approximation is order-relative on exactness, not on ε-approximation — universality is precisely
what forces the move to the `ε = 0` axis.
-/
import Sundogcert.OrderRelative
import Sundogcert.ExactRepr
import Sundogcert.UniversalApprox

namespace Sundog.OrderRelative.Approx

open Sundog.OrderRelative Sundog.ExactRepr Sundog.CircuitNet Sundog.PieceCover Sundog.RegionCount

/-- **`x²` has no finite piece cover** (it is not continuous-piecewise-linear). Any finite cut set
`S` leaves a gap interval beyond `max S` on whose interior `x²` would have to be affine — impossible
by strict convexity (the midpoint test on three points gives `(a-b)² = 0`). -/
theorem sq_no_pieceCover : ¬ ∃ k, HasPieceCover (fun x : ℝ => x ^ 2) k := by
  rintro ⟨k, S, _, hAff⟩
  obtain ⟨M, hM⟩ := S.bddAbove
  have hmiss : ∀ s ∈ S, s ∉ Set.Ioo (M + 1) (M + 2) := by
    intro s hs hsio
    have hsM : s ≤ M := hM (Finset.mem_coe.mpr hs)
    exact absurd hsio.1 (by linarith)
  obtain ⟨p, q, hpq⟩ := hAff (M + 1) (M + 2) (by linarith) hmiss
  have h1 := hpq (M + 1) (Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩)
  have h2 := hpq (M + 2) (Set.mem_Icc.mpr ⟨by linarith, le_refl _⟩)
  have h3 := hpq (M + 3 / 2) (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  nlinarith [h1, h2, h3]

/-- A function is **exactly representable** iff it is the realization of a finite ReLU net. -/
def ExactlyNet (f : ℝ → ℝ) : Prop := ∃ g : Net 1, realize1N g = f

/-- **`x²` is not exactly any ReLU net** — the earned resist. A finite net is piecewise-linear
(`net_hasPieceCover`), but `x²` has no finite piece cover (`sq_no_pieceCover`). -/
theorem sq_not_exactly_net : ¬ ExactlyNet (fun x : ℝ => x ^ 2) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, hk⟩ := net_hasPieceCover g
  rw [hg] at hk
  exact sq_no_pieceCover ⟨k, hk⟩

/-- **DETERMINE: a continuous-PL function (any net's realization) is exactly representable** — finite
exactness-order (here `0`). -/
def exactProblem (g : Net 1) : Problem where
  Target := Unit
  ord _ := 0
  Resolves _ _ := ExactlyNet (realize1N g)
  resolves_iff _ _ := by
    constructor
    · intro _; exact zero_le
    · intro _; exact ⟨g, rfl⟩

/-- **RESIST: `x²` is only approximable, never exact** — exactness-order `⊤` (earned via
`sq_not_exactly_net`). -/
def sqResistProblem : Problem where
  Target := Unit
  ord _ := ⊤
  Resolves _ _ := ExactlyNet (fun x : ℝ => x ^ 2)
  resolves_iff _ _ := by
    constructor
    · intro h; exact absurd h sq_not_exactly_net
    · intro h; simp at h

/-- **The exactness axis splits determine/resist.** A PL function (net realization) has finite
exactness-order; `x²` — approximable but not exactly a net — has order `⊤`. -/
theorem exact_determine_vs_resist (g : Net 1) :
    (exactProblem g).ord () = 0 ∧ sqResistProblem.ord () = ⊤ :=
  ⟨rfl, rfl⟩

/-- **The ε-approximation axis collapses (the contrast).** Every continuous `f` on `[0,1]` is
ε-approximable by a ReLU net for every `ε > 0` — so on this axis nothing resists; that is why
the determine/resist structure must live on the exactness axis above instead. -/
theorem approx_axis_collapses (f : C(↥(Set.Icc (0 : ℝ) 1), ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Net 1, ∀ x : ↥(Set.Icc (0 : ℝ) 1), |f x - realize1N g (x : ℝ)| ≤ ε := by
  obtain ⟨m, q, h⟩ := Sundog.UniversalApprox.continuous_relu_approximable f ε hε
  exact ⟨_, h⟩

#print axioms sq_no_pieceCover
#print axioms sq_not_exactly_net
#print axioms exact_determine_vs_resist
#print axioms approx_axis_collapses

end Sundog.OrderRelative.Approx
