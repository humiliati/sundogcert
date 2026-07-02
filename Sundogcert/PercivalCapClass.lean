/-
# PercivalCapClass -- the Sov_opt classification anchor (Angle-2 gate)

The S1 cleanliness law pinned the arbiter-authority cap's classification by the
variable it constrains: the realized downstream action-swing through the actuator
(an OUTGOING-influence bound), not the arbiter's internal input-combination (an
INCOMING/response-dependence bound). The law's registered falsifier: if the cap
is really an incoming-dependence constraint, S1 is void until recut.

This module machine-checks the classification in the minimal model of the cap as
actually implemented (NS-1-c / B1.0 lineage): the committed action is the raw
arbiter output clamped into the `kappa`-ball around the frozen presider action
`p`.  Three anchors give the two-sided separation:

* `cap_sov_le_kappa` -- cap validity: the committed action never deviates from
  the presider by more than `kappa` (the audited `Sov_opt <= kappa` gate).
* `cap_bounds_outgoing_swing` -- for ANY two raw outputs (i.e., under ANY
  intervention on ANY upstream component, however it moves the raw output), the
  committed-action swing is at most `2*kappa`.  The outgoing influence of every
  upstream component is bounded, with no assumption on internals.
* `cap_ignores_incoming_sensitivity` -- for every bound `M` there is a raw map
  with input-sensitivity exceeding `M` that still satisfies the cap everywhere:
  the cap places NO constraint on incoming dependence.

Together: the cap constrains the outgoing variable for all internal behavior and
the incoming variable for none -- the classification is exact, not argued.
Scope, honest: a 1-D minimal model (the NS cap is this clamp per dimension); the
anchor pins the classification, not the NS training dynamics.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival

/-- The capped commit: raw arbiter output clamped into the `kappa`-ball around
the presider action `p`. -/
def cappedCommit (p kappa a : ℚ) : ℚ :=
  max (p - kappa) (min (p + kappa) a)

private theorem cappedCommit_le {p kappa a : ℚ} (hk : 0 ≤ kappa) :
    cappedCommit p kappa a ≤ p + kappa := by
  unfold cappedCommit
  have h1 : p - kappa ≤ p + kappa := by linarith
  have h2 : min (p + kappa) a ≤ p + kappa := min_le_left _ _
  exact max_le h1 h2

private theorem le_cappedCommit {p kappa a : ℚ} :
    p - kappa ≤ cappedCommit p kappa a :=
  le_max_left _ _

/--
**Cap validity (`Sov_opt <= kappa`).**  The committed action never deviates from
the frozen presider action by more than `kappa`.
-/
theorem cap_sov_le_kappa {p kappa a : ℚ} (hk : 0 ≤ kappa) :
    |cappedCommit p kappa a - p| ≤ kappa := by
  have h1 := le_cappedCommit (p := p) (kappa := kappa) (a := a)
  have h2 := cappedCommit_le (p := p) (kappa := kappa) (a := a) hk
  rw [abs_le]
  constructor <;> linarith

/--
**Outgoing influence is bounded, unconditionally.**  Under ANY intervention on
ANY upstream component -- whatever it does to the raw arbiter output, taking it
from `a1` to `a2` -- the committed-action swing is at most `2*kappa`.  This is
the audited `Sov` (max unilateral action-swing) bound, with no assumption on the
arbiter's internals.
-/
theorem cap_bounds_outgoing_swing {p kappa a1 a2 : ℚ} (hk : 0 ≤ kappa) :
    |cappedCommit p kappa a1 - cappedCommit p kappa a2| ≤ 2 * kappa := by
  have h1l := le_cappedCommit (p := p) (kappa := kappa) (a := a1)
  have h1u := cappedCommit_le (p := p) (kappa := kappa) (a := a1) hk
  have h2l := le_cappedCommit (p := p) (kappa := kappa) (a := a2)
  have h2u := cappedCommit_le (p := p) (kappa := kappa) (a := a2) hk
  rw [abs_le]
  constructor <;> linarith

/--
**Incoming dependence is unconstrained.**  For every sensitivity bound `M` there
is a raw arbiter map whose input-sensitivity exceeds `M` (witness: `x ↦ M * x + M`
moves by more than `M` between inputs `0` and `2`) while the capped commit still
satisfies the `Sov_opt <= kappa` audit at every input.  The cap does not
constrain the incoming arrow at all -- it is not a response-dependence bound.
-/
theorem cap_ignores_incoming_sensitivity {p kappa : ℚ} (hk : 0 ≤ kappa) (M : ℚ)
    (hM : 0 < M) :
    ∃ raw : ℚ → ℚ,
      (∃ x1 x2 : ℚ, M < |raw x1 - raw x2|) ∧
        ∀ x : ℚ, |cappedCommit p kappa (raw x) - p| ≤ kappa := by
  refine ⟨fun x => M * x + M, ⟨2, 0, ?_⟩, fun x => cap_sov_le_kappa hk⟩
  have : M * 2 + M - (M * 0 + M) = 2 * M := by ring
  rw [show (M * 2 + M) - (M * 0 + M) = 2 * M by ring, abs_of_pos (by linarith)]
  linarith

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.cap_sov_le_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_sov_le_kappa

/-- info: 'Sundogcert.Percival.cap_bounds_outgoing_swing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_bounds_outgoing_swing

/-- info: 'Sundogcert.Percival.cap_ignores_incoming_sensitivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_ignores_incoming_sensitivity

end Sundogcert.Percival
