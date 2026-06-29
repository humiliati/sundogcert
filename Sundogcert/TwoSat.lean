/-
# 2-SAT — a satisfying assignment certifies satisfiability (N-3, find/check ledger)

The **decision-problem** representative of the find/check ledger, alongside the optimization
instances `MaxFlowMinCut` and `MatchingCover`. A satisfying assignment is a cheap-to-check
witness: the verifier evaluates every clause (`O(|φ|)`) and `check_correct` proves it decides
the language exactly, so `cert_sound` turns an accepted assignment into a proof of
`Satisfiable`. This is the NP "verification is easy" half, machine-checked.

Only the CHECK is here. *Finding* the assignment — the 2-SAT implication-graph / SCC algorithm
(Aspvall–Plass–Tarjan), or any search — is the imported wall, exactly as for the optimization
certs. (2-SAT is in P, but the *certificate* shape is the same: a witness whose verifier is a
cheap straight-line scan.)
-/
import Sundogcert.Certifies

namespace Sundog.TwoSat

variable {n : ℕ}

/-- A literal: a variable index with a polarity (`pos = true` ↦ the variable, `false` ↦ its
negation). -/
structure Lit (n : ℕ) where
  var : Fin n
  pos : Bool

/-- A 2-clause: the disjunction of two literals. -/
structure Clause (n : ℕ) where
  l₁ : Lit n
  l₂ : Lit n

/-- A 2-CNF formula: a list of 2-clauses. -/
abbrev Formula (n : ℕ) := List (Clause n)

/-- Evaluate a literal under an assignment. -/
def Lit.eval (α : Fin n → Bool) (l : Lit n) : Bool := if l.pos then α l.var else !α l.var

/-- Evaluate a clause: the disjunction of its two literals. -/
def Clause.eval (α : Fin n → Bool) (c : Clause n) : Bool := c.l₁.eval α || c.l₂.eval α

/-- An assignment **satisfies** a formula when every clause evaluates to `true`. -/
def Sat (φ : Formula n) (α : Fin n → Bool) : Prop := ∀ c ∈ φ, c.eval α = true

/-- A formula is **satisfiable** when some assignment satisfies it. -/
def Satisfiable (φ : Formula n) : Prop := ∃ α, Sat φ α

/-- The cheap **verifier**: evaluate every clause under the candidate assignment. -/
def check (φ : Formula n) (α : Fin n → Bool) : Bool := φ.all (fun c => c.eval α)

/-- **The verifier decides the language exactly.** `check φ α = true` iff `α` satisfies `φ`. -/
theorem check_correct (φ : Formula n) (α : Fin n → Bool) :
    check φ α = true ↔ Sat φ α := by
  simp [check, Sat, List.all_eq_true]

/-- **The certificate (NP verification, the cheap CHECK).** An accepted assignment certifies
satisfiability: the witness *is* the proof. -/
theorem cert_sound (φ : Formula n) (α : Fin n → Bool) (h : check φ α = true) :
    Satisfiable φ :=
  ⟨α, (check_correct φ α).mp h⟩

/-! ## The verification cost — and the find/check ledger instance -/

/-- A 2-SAT certificate's data: the formula and the candidate assignment. -/
structure SatCert (n : ℕ) where
  φ : Formula n
  α : Fin n → Bool

/-- Checking scans every clause: two literal evaluations and one disjunction per clause. -/
def SatCert.verifyCost (c : SatCert n) : ℕ := 3 * c.φ.length + 1

/-- The 2-SAT certificate plugs into the shared find/check ledger. -/
instance satCertifies : Certifies.Ledger (SatCert n) where
  program c := StraightLineCost.StraightLineProgram.ofCost c.verifyCost

/-- **Checking is cheap (`O(|φ|)`).** Verifying an assignment costs `3·|φ| + 1` operations —
the cheap-CHECK half; *finding* the assignment (the implication-graph algorithm) is the wall. -/
theorem satcert_cost_le (c : SatCert n) :
    Certifies.checkCost c ≤ 3 * c.φ.length + 1 := le_refl _

end Sundog.TwoSat
