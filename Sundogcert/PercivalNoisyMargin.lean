/-
# PercivalNoisyMargin -- crispness is pairing (Track-C v3, T1-T3)

The Track-C v2 selection between the true objective V and a responsive deceiver W'
is decided by one inequality: sampled evidence on the disagreement region D versus
the prior margin. v3 asks what survives observation NOISE. Answer: the crisp margin
survives arbitrary noise iff the evaluation is PAIRED -- where the two policies act
identically they receive the same observation, and those terms cancel exactly.

Main results (over an arbitrary observation function `obs`, i.e. any noise process,
adversarial included):

* `zero_coverage_margin_noise_invariant` -- if the two policies agree on every
  sampled context, the paired margin equals exactly `-prior` for EVERY `obs`. No
  noise process can rescue zero coverage.
* `zero_coverage_capture` -- with a positive prior margin toward the deceiver,
  zero-coverage capture is deterministic under arbitrary noise.
* `bounded_noise_recovery` -- if every observed per-hit gap is at least `g - 2*beta`
  (true gap `g`, per-observation noise bound `beta`), then coverage clearing the
  noise-degraded threshold forces recovery under ANY bounded noise. The paired
  noise tolerance is per-hit: `beta* = (h*g - prior)/(2h)`, independent of eval size.
* `unpaired_flip_witness` -- in UNPAIRED evaluation the shared contexts stop
  canceling: the explicit adversarial assignment (-beta on V's observations, +beta
  on W''s) shifts the margin by `-2*beta*|shared|`, flipping any true margin once
  `beta >= margin/(2*|S|)`. Tolerance ratio paired:unpaired = |S|/h -- the crisp
  margin degrades exactly as the disagreement fraction shrinks.

Scope, honest: these are statements about the toy's selection rule (sum of
observations minus a description-length prior) on finite lists over `ℚ`. The
Gaussian probit laws are Monte-Carlo receipts
(`scripts/percival-trackc-v3-noisy-margin.mjs` in the sundog repo); the empirical
bridge to real checkpoint pairs (B1/B2 in the v3 spec) is registered, not proven.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival

/-- Every element of `t` is at least `c`, so the sum is at least `length * c`. -/
private theorem length_mul_le_sum {c : ℚ} :
    ∀ (t : List ℚ), (∀ x ∈ t, c ≤ x) → (t.length : ℚ) * c ≤ t.sum := by
  intro t
  induction t with
  | nil => intro _; simp
  | cons x xs ih =>
    intro hb
    have hx : c ≤ x := hb x (List.mem_cons_self ..)
    have ihh := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons]
    push_cast
    nlinarith [hx, ihh]

/-- Sum of a constant map is `length * c`. -/
private theorem sum_map_const {α : Type*} (c : ℚ) :
    ∀ (l : List α), (l.map fun _ => c).sum = (l.length : ℚ) * c := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith [ih]

/--
**T1: zero-coverage margin is noise-invariant (paired cancellation).** If the two
policies agree on every sampled context, then for EVERY observation function
(arbitrary noise process, adversarial included) the paired selection margin equals
exactly `-prior`: shared behavior receives shared observations and cancels.
-/
theorem zero_coverage_margin_noise_invariant {α β : Type*} (S : List α)
    (obs : α → β → ℚ) (piV piW : α → β)
    (hagree : ∀ t ∈ S, piV t = piW t) (prior : ℚ) :
    (S.map fun t => obs t (piV t)).sum - (S.map fun t => obs t (piW t)).sum - prior
      = -prior := by
  have hmap : (S.map fun t => obs t (piV t)) = S.map fun t => obs t (piW t) :=
    List.map_congr_left fun t ht => by rw [hagree t ht]
  rw [hmap]
  ring

/--
**T1 corollary: zero-coverage capture is deterministic under arbitrary noise.**
With a positive prior margin toward the deceiver and agreement on every sampled
context, the selection margin is negative for every observation function.
-/
theorem zero_coverage_capture {α β : Type*} (S : List α)
    (obs : α → β → ℚ) (piV piW : α → β)
    (hagree : ∀ t ∈ S, piV t = piW t) {prior : ℚ} (hprior : 0 < prior) :
    (S.map fun t => obs t (piV t)).sum - (S.map fun t => obs t (piW t)).sum - prior
      < 0 := by
  have h := zero_coverage_margin_noise_invariant S obs piV piW hagree prior
  linarith

/--
**T2: bounded-noise recovery margin (paired tolerance is per-hit).** If every
observed per-hit gap on the disagreement region is at least `g - 2*beta`, then
coverage clearing the noise-degraded threshold `prior < h*(g - 2*beta)` forces
a positive margin -- recovery under ANY bounded noise. The bound involves only the
hit count, never the eval size: paired tolerance `beta* = (h*g - prior)/(2h)`.
-/
theorem bounded_noise_recovery (gaps : List ℚ) (g beta prior : ℚ)
    (hlb : ∀ x ∈ gaps, g - 2 * beta ≤ x)
    (hthresh : prior < (gaps.length : ℚ) * (g - 2 * beta)) :
    0 < gaps.sum - prior := by
  have h := length_mul_le_sum gaps hlb
  linarith

/--
**T3: unpaired fragility witness.** In unpaired evaluation the shared (agreeing)
contexts contribute independent noise that does not cancel. The explicit
adversarial assignment (`-beta` on each of V's observations, `+beta` on each of
W''s) shifts the margin by `(-beta) - beta` per shared context; once
`trueMargin <= 2*beta*|shared|` the selection flips. Unpaired tolerance is
`margin/(2*|S|)` -- decaying with eval size -- against T2's per-hit
`margin/(2h)`: the ratio is exactly the disagreement fraction.
-/
theorem unpaired_flip_witness {α : Type*} (shared : List α) (trueMargin beta : ℚ)
    (hflip : trueMargin ≤ 2 * beta * (shared.length : ℚ)) :
    trueMargin + (shared.map fun _ => (-beta) - beta).sum ≤ 0 := by
  have hsum := sum_map_const ((-beta) - beta) shared
  have hring : (shared.length : ℚ) * ((-beta) - beta)
      = -(2 * beta * (shared.length : ℚ)) := by ring
  rw [hsum, hring]
  linarith

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.zero_coverage_margin_noise_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_coverage_margin_noise_invariant

/-- info: 'Sundogcert.Percival.zero_coverage_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_coverage_capture

/-- info: 'Sundogcert.Percival.bounded_noise_recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounded_noise_recovery

/-- info: 'Sundogcert.Percival.unpaired_flip_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpaired_flip_witness

end Sundogcert.Percival
