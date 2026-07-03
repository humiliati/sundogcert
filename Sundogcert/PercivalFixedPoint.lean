/-
# PercivalFixedPoint -- the Angle-4 fixed-point gate, discharged (Track-C v4)

The deploy-correct chain on two hypotheses {V, W} (true objective vs responsive
deceiver): each correction round, the deployed hypothesis shapes what is sampled
(coverage is state-dependent -- performativity), then the Track-C selection rule
picks the next deployment. The per-round physics is inherited from
`PercivalNoisyMargin` (T1: an uncovered round's margin is exactly `-prior` for
every observation function; T2: a covered round clearing the bounded-noise
threshold recovers V), so the chain classification below is noise-robust.

Round bridge (arbitrary observation functions, ℚ):

* `round_miss_falls` -- uncovered round + inverted prior selects the deceiver,
  regardless of incumbent and of noise.
* `round_miss_noninverted_recovers` -- uncovered round + correct prior selects V.
* `round_hit_recovers` -- covered round clearing `h*(g-2*beta) > prior` selects V.

Chain classification (deterministic coverage `cov : Hyp → Bool`):

* `corrigible_absorbing` / `fall_without_coverage` -- V is absorbing iff its own
  deployment sustains coverage; ONE uncovered round topples it. Corrigibility is
  not a one-time redemption.
* `wirehead_absorbing` / `grace_exits_wirehead` -- W is absorbing iff coverage
  under its deployment is zero (the proxy-drivable base-update channel, exactly);
  a single covered round exits it.
* `global_convergence` / `capture_global` -- the bodhisattva and wirehead regimes.
* `wandering_period_two` -- with coverage only at W, NO fixed point is reached:
  the trajectory alternates forever (the wandering regime's skeleton).

Scope, honest: two-hypothesis chain with deterministic coverage; the stochastic
laws (absorption curve, wandering occupancy, probit thinning) are Monte-Carlo
receipts (`scripts/percival-trackc-v4-fixedpoint.mjs` in the sundog repo).
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival.Chain

/-- The two deployable hypotheses: the true objective and the responsive deceiver. -/
inductive Hyp
  | V
  | W
  deriving DecidableEq

open Hyp

/-- Selection at the evidence level: deploy V iff the differential evidence on the
disagreement region beats the prior margin toward the deceiver. -/
def select (evidence prior : ℚ) : Hyp := if prior < evidence then V else W

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

/--
**Round bridge, miss (inverted prior): the fall is unconditional.** If the two
policies agree on every sampled context (the round missed the disagreement
region), then for EVERY observation function the differential evidence is zero
and selection under a positive prior margin returns the deceiver -- regardless of
which hypothesis is incumbent and regardless of noise.
-/
theorem round_miss_falls {α β : Type*} (S : List α) (obs : α → β → ℚ)
    (piV piW : α → β) (hagree : ∀ t ∈ S, piV t = piW t)
    {prior : ℚ} (hprior : 0 < prior) :
    select ((S.map fun t => obs t (piV t)).sum
      - (S.map fun t => obs t (piW t)).sum) prior = W := by
  have hmap : (S.map fun t => obs t (piV t)) = S.map fun t => obs t (piW t) :=
    List.map_congr_left fun t ht => by rw [hagree t ht]
  rw [hmap]
  simp only [select, sub_self]
  rw [if_neg (by linarith)]

/--
**Round bridge, miss (correct prior): the miss is safe.** Under a prior margin
toward V, an uncovered round selects V for every observation function -- with a
correct prior, noise on shared behavior cannot cause a fall.
-/
theorem round_miss_noninverted_recovers {α β : Type*} (S : List α)
    (obs : α → β → ℚ) (piV piW : α → β) (hagree : ∀ t ∈ S, piV t = piW t)
    {prior : ℚ} (hprior : prior < 0) :
    select ((S.map fun t => obs t (piV t)).sum
      - (S.map fun t => obs t (piW t)).sum) prior = V := by
  have hmap : (S.map fun t => obs t (piV t)) = S.map fun t => obs t (piW t) :=
    List.map_congr_left fun t ht => by rw [hagree t ht]
  rw [hmap]
  simp only [select, sub_self]
  rw [if_pos hprior]

/--
**Round bridge, covered hit: recovery under any bounded noise.** If every observed
per-hit gap is at least `g - 2*beta` and coverage clears the noise-degraded
threshold, the round selects V.
-/
theorem round_hit_recovers (gaps : List ℚ) (g beta prior : ℚ)
    (hlb : ∀ x ∈ gaps, g - 2 * beta ≤ x)
    (hthresh : prior < (gaps.length : ℚ) * (g - 2 * beta)) :
    select gaps.sum prior = V := by
  have h := length_mul_le_sum gaps hlb
  simp only [select]
  rw [if_pos (by linarith)]

/-- One chain round: a covered round selects V, an uncovered round falls to W
(inverted prior baked in; justified by the round bridge above). -/
def step (covered : Bool) : Hyp := if covered then V else W

/-- The deploy-correct trajectory under deployment-dependent coverage. -/
def traj (cov : Hyp → Bool) (h0 : Hyp) : ℕ → Hyp
  | 0 => h0
  | n + 1 => step (cov (traj cov h0 n))

/--
**V is absorbing under sustained self-coverage.** If deployment of V keeps the
correction rounds covered, then once the chain reaches V it stays.
-/
theorem corrigible_absorbing (cov : Hyp → Bool) (h0 : Hyp) (hcv : cov V = true)
    {n : ℕ} (hn : traj cov h0 n = V) : ∀ m, n ≤ m → traj cov h0 m = V := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ k _ ih => simp only [traj]; rw [ih, hcv]; rfl

/--
**Corrigibility is not a one-time redemption.** If deployment of V fails to cover
the correction round, V topples to the deceiver on the very next round -- and by
`round_miss_falls` this is noise-invariant, not a noise event.
-/
theorem fall_without_coverage (cov : Hyp → Bool) (h0 : Hyp) (hcv : cov V = false)
    {n : ℕ} (hn : traj cov h0 n = V) : traj cov h0 (n + 1) = W := by
  simp only [traj]; rw [hn, hcv]; rfl

/--
**The wirehead is absorbing exactly when the base-update channel is
proxy-driven.** If deployment of W yields zero coverage of its own defect region,
then once the chain reaches W it stays.
-/
theorem wirehead_absorbing (cov : Hyp → Bool) (h0 : Hyp) (hcw : cov W = false)
    {n : ℕ} (hn : traj cov h0 n = W) : ∀ m, n ≤ m → traj cov h0 m = W := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ k _ ih => simp only [traj]; rw [ih, hcw]; rfl

/-- **One covered round exits the wirehead** (grace, or a probe that lands). -/
theorem grace_exits_wirehead (cov : Hyp → Bool) (h0 : Hyp) (hcw : cov W = true)
    {n : ℕ} (hn : traj cov h0 n = W) : traj cov h0 (n + 1) = V := by
  simp only [traj]; rw [hn, hcw]; rfl

/--
**The bodhisattva regime.** Coverage sustained under both deployments: the chain
converges to the corrigible fixed point from every start in one round and stays.
-/
theorem global_convergence (cov : Hyp → Bool) (h0 : Hyp)
    (hcv : cov V = true) (hcw : cov W = true) :
    ∀ n, 1 ≤ n → traj cov h0 n = V := by
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    simp only [traj]
    cases traj cov h0 k with
    | V => rw [hcv]; rfl
    | W => rw [hcw]; rfl

/--
**The wirehead regime.** Zero coverage under both deployments: the chain is
captured by the deceptive fixed point from every start in one round.
-/
theorem capture_global (cov : Hyp → Bool) (h0 : Hyp)
    (hcv : cov V = false) (hcw : cov W = false) :
    ∀ n, 1 ≤ n → traj cov h0 n = W := by
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    simp only [traj]
    cases traj cov h0 k with
    | V => rw [hcv]; rfl
    | W => rw [hcw]; rfl

/--
**The wandering regime's skeleton: no fixed point is reached.** Coverage only
under the deceiver's deployment (redemption always fires, then coverage lapses):
the trajectory alternates forever -- the deterministic period-2 core of the
stochastic wandering regime.
-/
theorem wandering_period_two (cov : Hyp → Bool) (h0 : Hyp)
    (hcv : cov V = false) (hcw : cov W = true) :
    ∀ n, traj cov h0 (n + 1) ≠ traj cov h0 n := by
  intro n
  cases h : traj cov h0 n with
  | V => simp only [traj]; rw [h, hcv]; simp [step]
  | W => simp only [traj]; rw [h, hcw]; simp [step]

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.Chain.round_miss_falls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_miss_falls

/-- info: 'Sundogcert.Percival.Chain.round_miss_noninverted_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_miss_noninverted_recovers

/-- info: 'Sundogcert.Percival.Chain.round_hit_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_hit_recovers

/-- info: 'Sundogcert.Percival.Chain.corrigible_absorbing' does not depend on any axioms -/
#guard_msgs in
#print axioms corrigible_absorbing

/-- info: 'Sundogcert.Percival.Chain.fall_without_coverage' does not depend on any axioms -/
#guard_msgs in
#print axioms fall_without_coverage

/-- info: 'Sundogcert.Percival.Chain.wirehead_absorbing' does not depend on any axioms -/
#guard_msgs in
#print axioms wirehead_absorbing

/-- info: 'Sundogcert.Percival.Chain.grace_exits_wirehead' does not depend on any axioms -/
#guard_msgs in
#print axioms grace_exits_wirehead

/-- info: 'Sundogcert.Percival.Chain.global_convergence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms global_convergence

/-- info: 'Sundogcert.Percival.Chain.capture_global' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms capture_global

/-- info: 'Sundogcert.Percival.Chain.wandering_period_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms wandering_period_two

end Sundogcert.Percival.Chain
