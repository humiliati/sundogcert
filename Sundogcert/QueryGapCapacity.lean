/-
# QueryGapCapacity -- the capacity-resistance certificate (the "third axis", non-imported)

The cross-substrate notes name three resistance modes for a lossy shadow: dimensional
(informational — the body has more bits than the shadow), topological (a continuous fibre
resists), and **computational / capacity** (the shadow DETERMINES the answer, yet FINDING it
is hard while CHECKING is cheap). The syndrome instance witnesses the third axis but IMPORTS its
hardness (syndrome decoding is NP-hard) and reports an upper bound against tested attackers.

This module supplies a **non-imported** witness for the capacity axis, by packaging
`Sundog.QueryGap`'s proved decision-tree gap into the determine/resist vocabulary. The point of
the axis is that capacity resistance is *orthogonal to information*: the object is fully
DETERMINABLE (finite query order — `n` queries settle it, unlike the σ = ∞ informational resist),
yet FIND resists and CHECK is flat.

`capacity_certificate` bundles the three cell properties, all machine-checked, nothing imported:

* **CHECK is flat** — verifying any supplied witness costs one query (`checkTree_depth`).
* **DETERMINABLE** — a correct decider of depth exactly `n` exists (`scanFull`, the linear scan):
  the problem has *finite* query order, so the resistance is not informational.
* **FIND resists** — every correct decider needs `≥ n` queries (`search_needs_n_queries`, the
  adversary). The gap `n : 1` grows unboundedly in `n`.

So the capacity axis occupies a determine/resist cell the informational axis cannot: *determinable
but find-resisting*. Unconditional in the query model — the honest replacement for the syndrome
instance's imported hardness.
-/
import Sundogcert.QueryGap

namespace Sundog.QueryGapCapacity

open Sundog.QueryGap

variable {n : ℕ}

/-- The linear scan over a list of positions: query each in turn, answer `true` at the first
marked one. The DETERMINABILITY witness — a total, correct decider whose depth is the list length. -/
def scanList : List (Fin n) → DTree n Bool
  | [] => .leaf false
  | i :: is => .query i (scanList is) (.leaf true)

/-- The scan answers `true` iff some listed position is marked. -/
theorem scanList_eval_iff (l : List (Fin n)) (x : Fin n → Bool) :
    (scanList l).eval x = true ↔ ∃ i ∈ l, x i = true := by
  induction l with
  | nil => simp [scanList, DTree.eval]
  | cons i is ih =>
    simp only [scanList, DTree.eval, List.mem_cons]
    by_cases h : x i = true
    · rw [if_pos h]
      exact ⟨fun _ => ⟨i, Or.inl rfl, h⟩, fun _ => rfl⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨j, hj, hxj⟩; exact ⟨j, Or.inr hj, hxj⟩
      · rintro ⟨j, rfl | hj, hxj⟩
        · exact absurd hxj h
        · exact ⟨j, hj, hxj⟩

/-- The scan has depth equal to the list length: one query per position. -/
theorem scanList_depth (l : List (Fin n)) : (scanList l).depth = l.length := by
  induction l with
  | nil => simp [scanList, DTree.depth]
  | cons i is ih =>
    simp only [scanList, DTree.depth, List.length_cons, ih, Nat.max_zero]
    omega

/-- The full linear scan over all `n` positions: a correct existence-decider of depth `n`. -/
def scanFull (n : ℕ) : DTree n Bool := scanList (List.finRange n)

/-- `scanFull` correctly decides `∃ i, x i = true`. -/
theorem scanFull_correct (x : Fin n → Bool) :
    (scanFull n).eval x = true ↔ ∃ i, x i = true := by
  rw [scanFull, scanList_eval_iff]
  simp [List.mem_finRange]

/-- `scanFull` has depth exactly `n`. -/
theorem scanFull_depth : (scanFull n).depth = n := by
  rw [scanFull, scanList_depth, List.length_finRange]

/--
**The capacity-resistance certificate (non-imported).** For `n ≥ 2`, the unstructured-search
shadow occupies the computational determine/resist cell, all three properties machine-checked:

* CHECK is flat — every witness-check costs one query;
* DETERMINABLE — a correct decider of depth exactly `n` exists (finite query order: the resistance
  is NOT informational);
* FIND resists — every correct decider needs `≥ n` queries.

Hence `check (= 1) ≪ find (≥ n)` with a gap growing unboundedly in `n`, proved in the query model,
nothing imported — the honest replacement for the syndrome instance's imported hardness.
-/
theorem capacity_certificate (hn : 2 ≤ n) :
    (∀ i : Fin n, (checkTree i).depth = 1) ∧
    (∃ t : DTree n Bool, (∀ x, (t.eval x = true ↔ ∃ i, x i = true)) ∧ t.depth = n) ∧
    (∀ t : DTree n Bool, (∀ x, (t.eval x = true ↔ ∃ i, x i = true)) → n ≤ t.depth) := by
  refine ⟨fun i => checkTree_depth i, ⟨scanFull n, fun x => scanFull_correct x, scanFull_depth⟩,
    fun t ht => search_needs_n_queries t ht⟩

/-! ## Local axiom audit -/

/-- info: 'Sundog.QueryGapCapacity.capacity_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms capacity_certificate

end Sundog.QueryGapCapacity
