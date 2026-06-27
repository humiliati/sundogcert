/-
# Shared straight-line cost interface

This file closes the H-A1 bookkeeping hook: the approximation lane's DAG gate count
and the certificate lane's verifier operation count are both instances of one
straight-line-program cost interface.

The claim is deliberately narrow. This does **not** identify construction with
verification, and it does not erase the find/check asymmetry. It only gives both sides
the same typed ledger: a straight-line program has a natural-number operation count,
and the already-proved linear bounds can be stated through that common `costOf`.
-/
import Sundogcert.CheckCost
import Sundogcert.CircuitNet

namespace Sundog.StraightLineCost

universe u

/-- A minimal straight-line program ledger: only the operation count is part of the
common interface. Individual modules remain responsible for justifying that their
ledger faithfully counts the intended operations. -/
structure StraightLineProgram where
  opCount : ℕ

/-- The shared cost measure. -/
def StraightLineProgram.cost (P : StraightLineProgram) : ℕ := P.opCount

/-- Package a raw operation count as a straight-line cost ledger. -/
def StraightLineProgram.ofCost (k : ℕ) : StraightLineProgram :=
  ⟨k⟩

@[simp] theorem StraightLineProgram.cost_ofCost (k : ℕ) :
    (StraightLineProgram.ofCost k).cost = k := rfl

/-- Types with a faithful straight-line cost ledger. -/
class HasStraightLineCost (α : Type u) where
  program : α → StraightLineProgram

/-- Read the common straight-line cost of an object with a ledger instance. -/
def costOf {α : Type u} [HasStraightLineCost α] (a : α) : ℕ :=
  (HasStraightLineCost.program a).cost

/-- A typed ReLU DAG's straight-line cost is its gate count. -/
instance rprogHasStraightLineCost {n m : ℕ} : HasStraightLineCost (CircuitNet.RProg n m) where
  program p := StraightLineProgram.ofCost p.gateCount

@[simp] theorem rprog_cost_eq_gateCount {n m : ℕ} (p : CircuitNet.RProg n m) :
    costOf p = p.gateCount := rfl

/-- A certificate verifier's straight-line cost is the audited `verifyCost` formula. -/
instance schemeHasStraightLineCost {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    HasStraightLineCost (Certificate.Scheme F) where
  program S := StraightLineProgram.ofCost (Certificate.verifyCost S)

@[simp] theorem verifier_cost_eq_verifyCost {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S : Certificate.Scheme F) :
    costOf S = Certificate.verifyCost S := rfl

/-- The recursive tropical-tree → ReLU-DAG compiler has linear straight-line cost. -/
theorem compileToDag_cost_le {n m : ℕ} (p : CircuitNet.RProg n m) (e : CircuitNet.Trop n) :
    costOf (CircuitNet.compileToDag p e).prog ≤ costOf p + 4 * e.nodeCount := by
  simpa [costOf, StraightLineProgram.cost, StraightLineProgram.ofCost, CircuitNet.RProg.gateCount]
    using CircuitNet.compileToDag_gate_count p e

/-- The certificate verifier has linear straight-line cost in the parity-check size. -/
theorem verifier_cost_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S : Certificate.Scheme F) :
    costOf S ≤ 2 * (S.m * S.n) + S.n + S.m + 2 := by
  simpa [costOf, StraightLineProgram.cost, StraightLineProgram.ofCost]
    using Certificate.verifyCost_le S

/-- The H-A1 bridge in one statement: the same `costOf` interface reads as DAG gate
count on the constructive approximation side and as verifier op-count on the
certificate side. -/
theorem shared_cost_instances {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (p : CircuitNet.RProg n m) (S : Certificate.Scheme F) :
    costOf p = p.gateCount ∧ costOf S = Certificate.verifyCost S := by
  exact ⟨rfl, rfl⟩

end Sundog.StraightLineCost

-- Axiom audit helpers: these should remain axiom-clean along the same foundations as
-- their source bounds.
#print axioms Sundog.StraightLineCost.compileToDag_cost_le
#print axioms Sundog.StraightLineCost.verifier_cost_le
#print axioms Sundog.StraightLineCost.shared_cost_instances
