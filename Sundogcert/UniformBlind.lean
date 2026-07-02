/-
# The uniformization blind point — ∀-probe blindness at exactly-uniform pushforward

The `AuditCost` pillar proves channel-level blindness for the POOLED observable: for every decidable
verifier there are per-unit-different systems with identical verdicts. This module proves the
SAMPLE-LEVEL impossibility that sits underneath it at the uniform blind point: when a hidden phase
`c` enters the observable only through a pushforward that is **exactly uniform mod the period**, the
full observation distribution is the same for every `c` — so EVERY sample-level probe (any verdict
map on observations, evaluated in distribution) is blind to `c`. Not an estimation-difficulty claim:
an identity of distributions, hence impossibility for all probes at once.

Finite counting form (ZMod n = the period lattice; the uniform distribution = counting measure):

- `uniform_shift_blind` — for ANY verdict map `V : ZMod n → α` and any phases `c c'`, the
  multiset of verdicts `{V (x + c)}` equals `{V (x + c')}`: acceptance counts, and hence every
  statistic of every probe, are identical for all phases.
- `verdict_count_eq` — the Boolean special case in the `AuditCost` verifier style: acceptance CARDS
  are equal for all shifts.
- `nonuniform_probe_exists` — non-vacuity: blindness is a property OF uniformity, not of the probe
  class. Off the uniform point (a point mass at `0`, `n ≥ 2`), the identity probe distinguishes
  shifts.

Scope (per the slate's refuter, binding): this is the uniformization blind point ONLY — "no-probe
wall" language is restricted to exactly-uniform pushforward, where it is an identity. Away from
uniform, recovery is classical deconvolution (Fan 1991; Meister 2009) and is NOT walled.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

namespace Sundog.UniformBlind

variable {n : ℕ} [NeZero n]

/-- **The uniformization blind point, in full generality.** If the observable is `x + c` with `x`
uniform on the period lattice, then for ANY verdict map `V` into any type, the verdict multiset is
the same for every phase `c` — stated as equality of preimage counts for every verdict value. Every
statistic of every sample-level probe is therefore phase-independent: blindness against ALL probes,
as one identity. -/
theorem uniform_shift_blind {α : Type*} [DecidableEq α] (V : ZMod n → α) (c c' : ZMod n) (a : α) :
    (Finset.univ.filter (fun x => V (x + c) = a)).card
      = (Finset.univ.filter (fun x => V (x + c') = a)).card := by
  apply Finset.card_bij (fun x _ => x + c - c')
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, by rw [sub_add_cancel]; exact hx.2⟩
  · intro x _ y _ h
    simpa using h
  · intro y hy
    rw [Finset.mem_filter] at hy
    exact ⟨y + c' - c, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [sub_add_cancel]; exact hy.2⟩,
      by ring⟩

/-- **The Boolean verifier form** (the `AuditCost` style): at the uniform blind point, every
decidable verifier's acceptance COUNT is identical for all phases — the verifier's verdict
distribution carries zero information about `c`. -/
theorem verdict_count_eq (V : ZMod n → Bool) (c c' : ZMod n) :
    (Finset.univ.filter (fun x => V (x + c) = true)).card
      = (Finset.univ.filter (fun x => V (x + c') = true)).card :=
  uniform_shift_blind V c c' true

omit [NeZero n] in
/-- **Non-vacuity: the wall is uniformity's, not the probe class's.** Off the uniform point — the
point mass at `0`, observed as `0 + c = c` — the IDENTITY probe already distinguishes distinct
phases. So `uniform_shift_blind` is about the exactly-uniform pushforward, not about any weakness
of sample-level probes. -/
theorem nonuniform_probe_exists (hn : 2 ≤ n) :
    ∃ (V : ZMod n → Bool) (c c' : ZMod n), V ((0 : ZMod n) + c) ≠ V ((0 : ZMod n) + c') := by
  refine ⟨fun x => x = 0, 0, 1, ?_⟩
  have h1 : (1 : ZMod n) ≠ 0 := by
    haveI : Fact (1 < n) := ⟨hn⟩
    exact one_ne_zero
  simp [h1]

end Sundog.UniformBlind
