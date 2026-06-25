/-
# Tauroctony — formal core of the non-sovereignty argument

Three machine-checked statements that pin down what the "pantheon vs. monolith"
narrative does and does not establish. The point of formalizing is to separate the
*near-trivial* claim (competence dominance) from the *non-trivial, still-open* one
(a non-sovereignty premium), and to be exact about the load-bearing caveats the
prose tends to smudge.

Four distinct objects must not be conflated: policy **expressivity** (`Π_D`),
**training/selection** (`L_D`), **fault/authority** semantics, and **ruin**. A
theorem about one is not a theorem about the others.

This module is constructive term/`linarith`/`ring` only — no `sorry`,
no `native_decide` — so it stays inside the repository's axiom-clean promise
(`#print axioms` blocks at the foot of the file pin this).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Sundogcert.Tauroctony

universe u

/-! ## 1. Competence-dominance lemma

`IsOptimal S J π`: `π` attains the maximum of score `J` over set `S`. -/

/-- `π` is optimal in `S` under score `J`. -/
def IsOptimal {Policy : Type u} (S : Set Policy) (J : Policy → ℝ) (π : Policy) : Prop :=
  π ∈ S ∧ ∀ ρ ∈ S, J ρ ≤ J π

/-- **Competence-dominance lemma.** If the council's realizable class is *contained*
in the monolith's (`C ⊆ M`) and both attain an optimum under a score `J`, then the
monolith's optimum weakly dominates. The proof is one line — this is definitional:
maximizing over a superset cannot lower the optimum.

Two caveats are load-bearing and are *not* discharged here:

* The score `J` is **arbitrary**. Instantiating `J := robustValue` or a CVaR /
  corrigibility score does **not** escape the lemma if the monolith is permitted to
  optimize *that* score over the same superset. The escape is therefore never "use a
  different objective."
* The hypothesis is `C ⊆ M`, a genuine *containment*. Equal inputs and equal
  parameter budget do **not** by themselves prove it; that requires an extensional
  class definition or a constructive simulation. -/
theorem optimum_mono {Policy : Type u} {C M : Set Policy} {J : Policy → ℝ}
    (hCM : C ⊆ M) {πC πM : Policy}
    (hC : IsOptimal C J πC) (hM : IsOptimal M J πM) :
    J πC ≤ J πM :=
  hM.2 πC (hCM hC.1)

/-! ## 2. The field, as channel noninterference (not "measurement = state")

"The measurement *is* the target state" is a type error: a measurement is a signal,
a target state is a state. The defensible core is *noninterference*: if a policy
factors through a signature channel, any attack that preserves the signature cannot
move the policy. This **relocates** the attack surface (to the sensor, the dynamics,
or the controller) — it does not reduce it to zero. -/

variable {Obs Act Signature : Type u}

/-- A policy factors through a signature channel `sig`. -/
def FactorsThrough (π : Obs → Act) (sig : Obs → Signature) : Prop :=
  ∃ f : Signature → Act, ∀ o, π o = f (sig o)

/-- An attack `α` preserves the signature channel. -/
def Preserves (sig : Obs → Signature) (α : Obs → Obs) : Prop :=
  ∀ o, sig (α o) = sig o

/-- **Signature noninterference.** A policy factoring through `sig` is invariant under
any signature-preserving attack. This is the exact, defensible content of the "field"
claim: an attacker who only edits channels *outside* the factorized signature cannot
steer the controller. To steer it they must alter the signature sensor, the underlying
state/dynamics, or the controller itself — the surface is relocated and cost-separated,
not deleted. -/
theorem signature_noninterference
    {π : Obs → Act} {sig : Obs → Signature} {α : Obs → Obs}
    (hπ : FactorsThrough π sig) (hα : Preserves sig α) :
    ∀ o, π (α o) = π o := by
  intro o
  obtain ⟨f, hf⟩ := hπ
  calc
    π (α o) = f (sig (α o)) := hf (α o)
    _ = f (sig o) := congrArg f (hα o)
    _ = π o := (hf o).symm

/-! ## 3. Parallel-ruin break-even

A scalar risk-adjusted value `V_L(D) = B(D) − L·p(D)`. The break-even below is exact
arithmetic; what it *cannot* supply is the premise `Δp > 0` (that a non-sovereign
design actually lowers ruin probability), which is the empirical/mechanistic claim.
The break-even is stated division-free as `ΔB < L·Δp`, equivalent to `L > ΔB/Δp`
when `Δp > 0`. -/

/-- Risk-adjusted value: ordinary benefit minus catastrophe-weighted ruin. -/
def riskAdjusted (benefit ruinProb catastropheLoss : ℝ) : ℝ :=
  benefit - catastropheLoss * ruinProb

/-- **Ruin break-even.** With `Δp := pM − pN > 0`, the non-sovereign design `N` has
higher risk-adjusted value than the sovereign `M` iff the catastrophe loss `L` clears
the benefit/risk ratio: `B(M) − B(N) < L·(pM − pN)` (i.e. `L > ΔB/Δp`). The capability
tax becomes rational exactly once ruin is priced past this threshold — *given* that
`Δp > 0`, which this lemma does not establish. -/
theorem ruin_break_even {BM BN pM pN L : ℝ} (_hΔp : 0 < pM - pN) :
    riskAdjusted BN pN L > riskAdjusted BM pM L ↔ BM - BN < L * (pM - pN) := by
  unfold riskAdjusted
  have hxp : L * (pM - pN) = L * pM - L * pN := by ring
  rw [hxp]
  constructor <;> intro h <;> linarith

/-! ## 4. Axiom audit — these stay inside the foundational triple. -/

/-- info: 'Sundogcert.Tauroctony.optimum_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms optimum_mono

/-- info: 'Sundogcert.Tauroctony.ruin_break_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruin_break_even

end Sundogcert.Tauroctony
