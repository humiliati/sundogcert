/-
# Halo minimum-deviation geometry (textbook geometric optics)

A standalone, machine-checked formalization of the **minimum-deviation principle**
for a ray of light passing through an ice prism — the geometry behind the 22-degree
atmospheric halo (Greenler 1980, Tape 1994; fully public, textbook material).

## What is PROVED here (the deductive core)

For a prism of apex angle `A` and refractive index `n`, with Snell's law
`sin θᵢ = n · sin rᵢ` holding at each face and the two refraction angles summing to
the apex (`r₂ = A − r₁`), the total angular deviation of the ray is

  `dev n A r = arcsin (n · sin r) + arcsin (n · sin (A − r)) − A`.

We prove:

* `dev_value` — at the symmetric ray `r = A/2` the deviation equals
  `2 · arcsin (n · sin (A/2)) − A` (because `sin (A − A/2) = sin (A/2)`).
* `min_deviation_stationary` (THE CORE) — the deviation is **stationary** at the
  symmetric ray: `HasDerivAt (dev n A) 0 (A/2)`.  The proof is the clean symmetry
  argument: writing `g r = arcsin (n · sin r)`, we have `dev r = g r + g (A − r) − A`,
  so `dev' r = g' r − g' (A − r)`; at `r = A/2` both arguments coincide and the two
  derivative terms cancel.  No explicit value of `g'` is ever needed.
* `symmetric_ray_isLocalMin_of_secondDeriv` — a clean wrapper of the textbook
  second-derivative test: IF the deviation is convex at the symmetric ray
  (positive second derivative), THEN that stationary ray is a genuine local
  minimum.  (Convexity itself is the physical input, not re-derived here.)

## The IMPORTED WALL (named, NOT proved here)

The pure geometry above is what this module certifies.  The following are physical /
observational facts taken as given, NOT derived:

* that atmospheric ice crystals present **hexagonal 60-degree prism** geometry
  (apex `A = π/3`);
* the refractive index of ice `n ≈ 1.31` (empirical measurement);
* that light obeys **Snell's law** at each crystal face;
* that the ray actually **refracts out** of the second face — i.e. there is no total
  internal reflection.  This is exactly the hypothesis `-1 < n · sin r` and
  `n · sin r < 1` that `arcsin` differentiability requires, and we carry it as an
  explicit hypothesis rather than asserting it;
* that the **observed bright ring** of the halo forms at the deviation extremum
  (the ray pile-up where deviation is stationary — an observational/optical fact).

The method proves the geometry of minimum deviation.  That the sky *realizes* this
geometry as a visible halo is named, not proved.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.DerivativeTest

namespace Sundog.HaloGeometry

open Real

/-- Total angular deviation of a ray through a prism of apex angle `A` and
refractive index `n`, as a function of the first-face refraction angle `r`.
Snell's law at each face gives the incidence angles `arcsin (n · sin r)` and
`arcsin (n · sin (A − r))`; the geometric total deviation subtracts the apex `A`. -/
noncomputable def dev (n A r : ℝ) : ℝ :=
  Real.arcsin (n * Real.sin r) + Real.arcsin (n * Real.sin (A - r)) - A

/-- The single-face deviation contribution `g r = arcsin (n · sin r)`.  The full
deviation is `dev n A r = g r + g (A − r) − A`. -/
noncomputable def faceDev (n r : ℝ) : ℝ := Real.arcsin (n * Real.sin r)

/-- `dev` is `faceDev` at `r` plus `faceDev` at the reflected angle `A − r`,
minus the apex. -/
theorem dev_eq_faceDev (n A r : ℝ) :
    dev n A r = faceDev n r + faceDev n (A - r) - A := rfl

/-- **Deviation value at the symmetric ray.**  Since `sin (A − A/2) = sin (A/2)`,
the two face contributions coincide and the symmetric-ray deviation is
`2 · arcsin (n · sin (A/2)) − A` — the 22-degree halo radius for `A = π/3`,
`n ≈ 1.31`. -/
theorem dev_value (n A : ℝ) :
    dev n A (A / 2) = 2 * Real.arcsin (n * Real.sin (A / 2)) - A := by
  unfold dev
  have hsub : A - A / 2 = A / 2 := by ring
  rw [hsub]
  ring

/-- The derivative of the single-face contribution `g r = arcsin (n · sin r)`,
as a `HasDerivAt` fact, under the no-total-internal-reflection hypothesis
`n · sin r ≠ ±1` (the ray exits the face).  The derivative value is
`(1 / √(1 − (n · sin r)²)) * (n * cos r)` but its explicit form is never needed
downstream — only that `g` is differentiable with *some* derivative `Dg`. -/
theorem faceDev_hasDerivAt {n r : ℝ} (h₁ : n * Real.sin r ≠ -1)
    (h₂ : n * Real.sin r ≠ 1) :
    HasDerivAt (faceDev n)
      ((1 / Real.sqrt (1 - (n * Real.sin r) ^ 2)) * (n * Real.cos r)) r := by
  have hsin : HasDerivAt (fun r => n * Real.sin r) (n * Real.cos r) r :=
    (Real.hasDerivAt_sin r).const_mul n
  have harc :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (n * Real.sin r) ^ 2))
        (n * Real.sin r) :=
    Real.hasDerivAt_arcsin h₁ h₂
  exact harc.comp r hsin

/-- **Minimum-deviation principle (THE DEDUCTIVE CORE).**

The angular deviation `dev n A` is **stationary at the symmetric ray** `r = A/2`:
its derivative there is `0`.

Hypotheses (the imported optical wall, named explicitly): the ray refracts out at
the symmetric ray, i.e. `n · sin (A/2) ≠ ±1` (no total internal reflection), so the
`arcsin` is differentiable there.

The proof is pure symmetry: `dev r = g r + g (A − r) − A` with `g = faceDev n`.
The first term contributes `Dg`, the reflected term `g (A − ·)` contributes `−Dg`
(chain rule, inner derivative `−1`), and at `r = A/2` both `Dg`'s are evaluated at
the SAME point `A/2`, so they cancel: `Dg + (−Dg) = 0`. -/
theorem min_deviation_stationary {n A : ℝ}
    (h₁ : n * Real.sin (A / 2) ≠ -1) (h₂ : n * Real.sin (A / 2) ≠ 1) :
    HasDerivAt (fun r => dev n A r) 0 (A / 2) := by
  -- abbreviation for the single-face derivative value at the symmetric point
  set Dg : ℝ := (1 / Real.sqrt (1 - (n * Real.sin (A / 2)) ^ 2)) * (n * Real.cos (A / 2))
    with hDg
  -- first face: g has derivative Dg at A/2
  have hface1 : HasDerivAt (faceDev n) Dg (A / 2) := faceDev_hasDerivAt h₁ h₂
  -- inner reflection map A - · has derivative -1 at A/2
  have hrefl : HasDerivAt (fun r : ℝ => A - r) (-1) (A / 2) :=
    ((hasDerivAt_id (A / 2)).const_sub A)
  -- the reflected point A - A/2 = A/2
  have hpt : A - A / 2 = A / 2 := by ring
  -- second face: g (A - ·) has derivative Dg * (-1) at A/2
  have hfacepre : HasDerivAt (faceDev n) Dg (A - A / 2) := by
    rw [hpt]; exact hface1
  have hface2 : HasDerivAt (fun r => faceDev n (A - r)) (Dg * (-1)) (A / 2) :=
    hfacepre.comp (A / 2) hrefl
  -- dev = (g r) + (g (A - r)) - A; combine and subtract the constant A
  have hsum :
      HasDerivAt (fun r => faceDev n r + faceDev n (A - r)) (Dg + Dg * (-1)) (A / 2) :=
    hface1.add hface2
  have hdev :
      HasDerivAt (fun r => faceDev n r + faceDev n (A - r) - A)
        (Dg + Dg * (-1)) (A / 2) := by
    simpa using hsum.sub_const A
  -- the derivative value collapses to 0
  have hzero : Dg + Dg * (-1) = 0 := by ring
  rw [hzero] at hdev
  -- rewrite the goal's `dev` to the faceDev form
  have hfun : (fun r => dev n A r) = (fun r => faceDev n r + faceDev n (A - r) - A) := by
    funext r; rfl
  rw [hfun]
  exact hdev

/-- **The symmetric ray is a genuine local minimum (stretch, textbook second-
derivative test).**

Given (i) the stationarity already proved (`min_deviation_stationary`, supplied here
as `deriv (dev n A) (A/2) = 0`), (ii) the deviation is convex at the symmetric ray —
positive curvature `deriv (deriv (dev n A)) (A/2) > 0` (the physical convexity input,
an optical fact about the deviation curve, named not re-derived), and (iii)
continuity at the point, the symmetric ray is a local minimum of the deviation.

This is the formal statement of "minimum-deviation": the stationary symmetric ray is
where deviation is smallest, and the halo forms at that minimum-deviation angle. -/
theorem symmetric_ray_isLocalMin_of_secondDeriv {n A : ℝ}
    (hpos : deriv (deriv (fun r => dev n A r)) (A / 2) > 0)
    (hstat : deriv (fun r => dev n A r) (A / 2) = 0)
    (hcont : ContinuousAt (fun r => dev n A r) (A / 2)) :
    IsLocalMin (fun r => dev n A r) (A / 2) :=
  isLocalMin_of_deriv_deriv_pos hpos hstat hcont

end Sundog.HaloGeometry

-- Axiom audit: the deductive core depends only on mathlib's foundational axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`.
#print axioms Sundog.HaloGeometry.min_deviation_stationary
#print axioms Sundog.HaloGeometry.dev_value
#print axioms Sundog.HaloGeometry.symmetric_ray_isLocalMin_of_secondDeriv
