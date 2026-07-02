/-
# AveragingDecodability — amplitude washes; a rescaling readout does not (AT-6 anchor)

The AT-6 run (`sundog/docs/chatv2/AT6_CHARFUN_TYPING_RECEIPT.md`, 2026-07-02) measured a
sharp split on a deterministic Kolmogorov cell: window-averaging drives the phase-type
signal's AMPLITUDE toward zero (the in-tree charFun dichotomy), yet the label stays
DECODABLE — a z-scored linear readout rescales the attenuated ripple, and with no noise
floor decodability tracks separability, not amplitude. This module pins both halves:

* **Amplitude half (packaged from in-tree):** `averaging_types_shadows` — under the
  spread/window parameter, the absolutely-continuous population's averaged fringe tends
  to 0 (`absCont_resists`) while the lattice two-point population's fringe recurs and
  does not (`twoPoint_shadow_survives`). The charFun typing, as one statement.
* **Decodability half (new, elementary):** `decodable_mul_iff` — attenuation by ANY
  nonzero factor preserves exact decodability (the readout rescales);
  `zero_shadow_not_decodable` — only the zero (constant) shadow kills a non-constant
  label; `amplitude_washes_readout_does_not` — the punchline: the Debye–Waller-damped
  channel `exp(−2π²λ²t²)·s` is decodable at EVERY finite spread λ (the factor is never
  zero) even though the amplitude tends to 0 as λ → ∞, and only the limit shadow is
  undecodable. **Wash-out is a limit / noise-floor phenomenon, not a finite-window one.**

## Fences (what this does NOT prove)

* The bridge "physical time-average over a trajectory window = averaging over a measure"
  is a NAMED IMPORT with a **measured boundary** (the AT-6 receipt: it holds in the
  presence of an observation-noise floor; the noiseless cell violates the decodability
  reading, exactly as this module predicts).
* `Decodable` here is exact deterministic factoring; SNR/noisy decodability is NOT
  formalized — that half is empirical and stays with the AT-6 receipt.
* Types shadows, not resistance; nothing about NSE, the C1 cell, or any model/ledger.
-/
import Mathlib
import Sundogcert.ShadowDecayLattice

namespace Sundog.AveragingDecodability

open Filter MeasureTheory Topology Sundog.ShadowDecayLattice

/-- A label is **decodable** from a real shadow if it factors through it — the
`IsSufficient` / `BagSufficient` idiom, pointwise form. -/
def Decodable {X : Type*} (s : X → ℝ) (L : X → Bool) : Prop :=
  ∃ g : ℝ → Bool, ∀ x, g (s x) = L x

/-- **Attenuation by any nonzero factor preserves decodability** — the readout rescales.
This is the formal core of the AT-6 finding: a damped-but-nonzero channel loses amplitude,
never (exact) decodability. -/
theorem decodable_mul_iff {X : Type*} (s : X → ℝ) (L : X → Bool) {c : ℝ} (hc : c ≠ 0) :
    Decodable (fun x => c * s x) L ↔ Decodable s L := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨fun r => g (c * r), fun x => hg x⟩
  · rintro ⟨g, hg⟩
    refine ⟨fun r => g (r / c), fun x => ?_⟩
    change g (c * s x / c) = L x
    rw [mul_div_cancel_left₀ _ hc]
    exact hg x

/-- **Only the zero (constant) shadow kills a non-constant label.** -/
theorem zero_shadow_not_decodable {X : Type*} {L : X → Bool}
    (hnc : ∃ x y, L x ≠ L y) : ¬ Decodable (fun _ : X => (0 : ℝ)) L := by
  rintro ⟨g, hg⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy ((hg x).symm.trans (hg y))

/-- The Debye–Waller attenuation factor is **never zero** at any finite spread. -/
theorem debyeWaller_ne_zero (lam t : ℝ) :
    Real.exp (-(2 * Real.pi ^ 2) * lam ^ 2 * t ^ 2) ≠ 0 :=
  Real.exp_ne_zero _

/-- The Debye–Waller attenuation factor **tends to zero** as the spread grows (`t ≠ 0`). -/
theorem debyeWaller_tendsto_zero (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun lam : ℝ => Real.exp (-(2 * Real.pi ^ 2) * lam ^ 2 * t ^ 2))
      atTop (𝓝 0) := by
  have hC : 0 < 2 * Real.pi ^ 2 * t ^ 2 := by positivity
  have hsq : Tendsto (fun lam : ℝ => lam ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hup : Tendsto (fun lam : ℝ => 2 * Real.pi ^ 2 * t ^ 2 * lam ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop hC hsq
  have hdown : Tendsto (fun lam : ℝ => -(2 * Real.pi ^ 2) * lam ^ 2 * t ^ 2) atTop atBot := by
    have h := tendsto_neg_atBot_iff.mpr hup
    exact h.congr fun lam => by ring
  exact Real.tendsto_exp_atBot.comp hdown

/-- **The punchline (AT-6, both halves in one statement).** For any decodable non-constant
label and any probe `t ≠ 0`: the Debye–Waller-damped channel remains decodable at EVERY
finite spread λ, the amplitude tends to zero as λ → ∞, and the limit (zero) shadow alone
is undecodable. Amplitude-washing is a limit phenomenon; finite-window decodability
survives — exactly the measured G=200 behavior (cycle-timing 0.99-decodable under 5-cycle
averaging on a noiseless cell). -/
theorem amplitude_washes_readout_does_not {X : Type*} (s : X → ℝ) (L : X → Bool)
    (hdec : Decodable s L) (hnc : ∃ x y, L x ≠ L y) (t : ℝ) (ht : t ≠ 0) :
    (∀ lam : ℝ,
        Decodable (fun x => Real.exp (-(2 * Real.pi ^ 2) * lam ^ 2 * t ^ 2) * s x) L)
      ∧ Tendsto (fun lam : ℝ => Real.exp (-(2 * Real.pi ^ 2) * lam ^ 2 * t ^ 2))
          atTop (𝓝 0)
      ∧ ¬ Decodable (fun _ : X => (0 : ℝ)) L :=
  ⟨fun lam => (decodable_mul_iff s L (debyeWaller_ne_zero lam t)).mpr hdec,
   debyeWaller_tendsto_zero t ht,
   zero_shadow_not_decodable hnc⟩

/-- **The amplitude half, packaged (the charFun typing as one statement).** Under the
spread parameter, the absolutely-continuous population's averaged fringe washes out while
the lattice two-point population's fringe recurs — the in-tree AC-resist / lattice-survive
separation, stated as the AT-6 typing. The bridge to physical time-averages is the named
import in the module header. -/
theorem averaging_types_shadows (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) [IsProbabilityMeasure (absContMeasure f)]
    (a c t : ℝ) (ha : a ≠ 0) (ht : 0 < t)
    (hc : Real.cos (2 * Real.pi * c * t) ≠ 0) :
    Tendsto (fun lam : ℝ =>
        ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂absContMeasure f)
      atTop (𝓝 0)
      ∧ ¬ Tendsto (fun lam : ℝ =>
          ∫ x, Real.cos (2 * Real.pi * (c + lam * x) * t) ∂twoPoint a)
        atTop (𝓝 0) :=
  ⟨absCont_resists f hf_meas hf_nonneg c t ht, twoPoint_shadow_survives a c t ha ht hc⟩

end Sundog.AveragingDecodability

-- Axiom audit (exact sets read at first build, then gated in AxiomAudit.lean).
#print axioms Sundog.AveragingDecodability.decodable_mul_iff
#print axioms Sundog.AveragingDecodability.zero_shadow_not_decodable
#print axioms Sundog.AveragingDecodability.amplitude_washes_readout_does_not
#print axioms Sundog.AveragingDecodability.averaging_types_shadows
