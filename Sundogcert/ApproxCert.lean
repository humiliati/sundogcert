/-
# Approximation certificates: the find/check ledger for ε-approximation (Slate-4 U-2)

The `Certifies` ledger certifies **exact** optima (a cheap CHECK; FIND imported). This module
extends it to **approximation**: a certificate that an approximant `g` is within `ε` of a target
`f` on an interval, with a **cheap, finite CHECK**.

The honest crux (the slate's `APPROX_CHECK_NOT_CHEAP` falsifier): verifying `|f − g| ≤ ε` over a
*continuum* is not a finite computation — *unless* a structural input is carried. The resolution
is the **a-posteriori sampling certificate** (`approx_from_samples`): a finite set of sample points
where `|f − g| ≤ η`, plus a **Lipschitz modulus** `L` for `f − g` and a `δ`-cover of the interval
by the samples, certifies `|f − g| ≤ η + L·δ` *everywhere*. The CHECK is then `O(#samples)` —
genuinely cheap and separated from FIND — but the modulus `L` is the named carried input (without
it the continuum check does not separate; that is exactly when the falsifier fires).

So `ApproxCert` is a real `Certifies.Ledger` instance whose `checkCost` is the sample count, and —
since for the lane's *constructed* approximants FIND (the construction) is itself in Lean — it joins
`QueryGap` as a ledger entry where neither side is imported.
-/
import Sundogcert.Certifies

namespace Sundog.ApproxCertLedger

/-- **The a-posteriori sampling bound (the cheap CHECK's soundness).** If `f − g` is `L`-Lipschitz
on `[a,b]`, is within `η` at every sample, and the samples `δ`-cover `[a,b]`, then it is within
`η + L·δ` everywhere on `[a,b]` — a finite check certifying a continuum bound. -/
theorem approx_from_samples {a b L η δ : ℝ} {f g : ℝ → ℝ} {S : Finset ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |(f x - g x) - (f y - g y)| ≤ L * |x - y|)
    (hsamp : ∀ s ∈ S, |f s - g s| ≤ η)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ s ∈ S, s ∈ Set.Icc a b ∧ |x - s| ≤ δ) :
    ∀ x ∈ Set.Icc a b, |f x - g x| ≤ η + L * δ := by
  intro x hx
  obtain ⟨s, hsS, hsab, hxs⟩ := hcover x hx
  have h1 : |(f x - g x) - (f s - g s)| ≤ L * δ :=
    le_trans (hlip x hx s hsab) (mul_le_mul_of_nonneg_left hxs hL)
  calc |f x - g x| = |((f x - g x) - (f s - g s)) + (f s - g s)| := by congr 1; ring
    _ ≤ |(f x - g x) - (f s - g s)| + |f s - g s| := abs_add_le _ _
    _ ≤ L * δ + η := add_le_add h1 (hsamp s hsS)
    _ = η + L * δ := by ring

/-! ### The approximation certificate as a ledger instance -/

/-- An **approximation certificate**: the target `f`, approximant `g`, interval `[a,b]`, a Lipschitz
modulus `L` for `f − g`, a per-sample tolerance `η`, a cover radius `δ`, and the finite sample set —
with the cheap-check data (sample bounds, cover) and the carried modulus as proof fields. -/
structure ApproxCert where
  a : ℝ
  b : ℝ
  f : ℝ → ℝ
  g : ℝ → ℝ
  L : ℝ
  η : ℝ
  δ : ℝ
  hL : 0 ≤ L
  samples : Finset ℝ
  lipschitz : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
    |(f x - g x) - (f y - g y)| ≤ L * |x - y|
  sampleBound : ∀ s ∈ samples, |f s - g s| ≤ η
  cover : ∀ x ∈ Set.Icc a b, ∃ s ∈ samples, s ∈ Set.Icc a b ∧ |x - s| ≤ δ

/-- The certified uniform error bound `η + L·δ`. -/
def ApproxCert.bound (c : ApproxCert) : ℝ := c.η + c.L * c.δ

/-- **Soundness.** A valid approximation certificate certifies the continuum L∞ bound. -/
theorem ApproxCert.sound (c : ApproxCert) :
    ∀ x ∈ Set.Icc c.a c.b, |c.f x - c.g x| ≤ c.bound :=
  approx_from_samples c.hL c.lipschitz c.sampleBound c.cover

/-- The certificate's straight-line CHECK cost is its sample count — a *finite* verifier for a
continuum approximation property. -/
instance : StraightLineCost.HasStraightLineCost ApproxCert where
  program c := StraightLineCost.StraightLineProgram.ofCost c.samples.card

/-- `ApproxCert` is a find/check ledger instance (the CHECK is the finite sample evaluation). -/
instance : Certifies.Ledger ApproxCert := ⟨⟩

@[simp] theorem ApproxCert.checkCost_eq (c : ApproxCert) :
    Certifies.checkCost c = c.samples.card := rfl

/-- **The ledger headline.** The cheap (finite, `#samples`-cost) CHECK certifies the continuum
approximation bound: `checkCost` counts the samples, and passing them gives `|f − g| ≤ bound`
everywhere on `[a,b]`. -/
theorem ApproxCert.cheap_check_certifies (c : ApproxCert) :
    Certifies.checkCost c = c.samples.card ∧
      (∀ x ∈ Set.Icc c.a c.b, |c.f x - c.g x| ≤ c.bound) :=
  ⟨rfl, c.sound⟩

end Sundog.ApproxCertLedger
