/-
# OrderRelative — the keyed-composition boundary instance (OR-2)

Instantiates `OrderRelativeComposeLaw`'s boundary — **join-homomorphic iff
cancellation-free** — on the two structures pre-registered by the ORDERRELATIVE
lane's OR-2 (mark 3): cap margins in `(ℚ≥0, +)` and the court's threshold
satisfaction in the idempotent Boolean algebra.  The same-lemma fence binds:
the working lemmas here are the BANKED ones, applied verbatim —
`coproduct_nsmul_eq_zero` / `addOrderOf_prod_eq_lcm` on the cap side,
`idempotent_eq_one` on the court side.  The two new lemmas
(`margin_zerosumfree`, `threshold_readout_not_hom`) are glue forced by the S3
objects (margins are nonnegative; the guarantee IS the threshold readout —
OR-1's `courtValue`), not structure engineered for the verdict.

**Cap side = the cancellation-free pole.**
* `margin_zerosumfree` — in `ℚ≥0` a sum vanishes iff both parts do: the
  within-monoid aggregation cannot cancel.  The exact contrast with the banked
  `within_group_cancels` (`ZMod 2`: `1 + 1 = 0`, the order drops): torsion vs
  torsion-free is the boundary, and the cap side sits on the free side.
* `margin_torsion_free` — no positive budget annihilates a nonzero margin:
  the order never drops under aggregation.
* `cap_margins_coproduct` / `cap_margin_order_join` — the banked coproduct and
  grading laws VERBATIM at margin tuples: per-agent margins are coordinates of
  the cancellation-free coproduct, annihilation factorizes with no interaction
  — the algebraic face of OR-1's `cap_marginal_profile_independent`.

**Court side = the idempotent pole.**
* `court_readout_idempotent` — the value algebra `(Bool, ∨)` has a nontrivial
  idempotent (`true ∨ true = true`, `true ≠ false`) — the same degeneracy class
  as the moment semilattice.
* `court_readout_not_group_order` — the banked `idempotent_eq_one` VERBATIM:
  any operation-respecting map into any group collapses `true` to the identity,
  so the court's value algebra embeds in no group — the algebraic WHY behind
  OR-1's `court_value_not_additive` (additivity would embed the value in `ℚ`).
* `threshold_readout_not_hom` — **the readout locus, machine-checked**: the
  threshold map `a ↦ (τ ≤ a)` is NOT a homomorphism `(ℚ≥0, +) → (Bool, ∨)`
  (witness `τ/2 + τ/2`).  Upstream of the readout everything is
  cancellation-free (`margin_zerosumfree`); the non-homomorphism enters exactly
  at the readout — mark 3's caution resolved in the model's favor: keying to
  the post-readout algebra is not bespoke, it is where the guarantee's value
  lives by definition, and this lemma pins that the boundary is crossed there
  and nowhere earlier.

**Fence verdict: PASS (literal instance).**  Both poles are classified by the
banked boundary — cancellation-free coproduct ⟹ join-homomorphic (grading law,
applied verbatim); idempotent value algebra ⟹ no group order (converse
obstruction, applied verbatim) — with the S3 contrast supplying only the
objects, not new lemmas.  Honest note: `ℚ≥0` margin orders are degenerate
(`0` or unreachable — torsion-free), so the join law holds on the free pole
the way the moment axis holds the semilattice pole: the boundary's two
degenerate ends, which is exactly where the lane's law says they must sit.

Scope: the aggregation skeleton only (as OR-1); `(ℚ≥0, +)` stands for the
margin calculus (OR-1's margins `κ − |d|` are nonnegative exactly when the
guarantee holds); `(Bool, ∨)` for the honored/disgraced value with coalition
disjunction; no court dynamics.
-/
import Sundogcert.OrderRelativeGrading
import Mathlib.Data.NNRat.Defs

namespace Sundog.OrderRelative.Keyed

open Sundog.OrderRelative.Converse Sundog.OrderRelative.Grading

/-! ## The cap side: `(ℚ≥0, +)` is cancellation-free -/

/-- **The margin aggregation cannot cancel (zerosumfree).**  In `ℚ≥0` a sum
vanishes iff both parts do — the within-monoid aggregation is
cancellation-free, the exact opposite of the banked `within_group_cancels`
(`ZMod 2`, where `1 + 1 = 0` drops the order). -/
theorem margin_zerosumfree (a b : ℚ≥0) : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha : a ≤ 0 := h ▸ le_self_add
    have hb : b ≤ 0 := h ▸ le_add_self
    exact ⟨le_zero_iff.mp ha, le_zero_iff.mp hb⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb, add_zero]

/-- **No positive budget annihilates a nonzero margin (torsion-free).**  The
order never drops under aggregation — why the cap side sits on the
join-homomorphic side of the boundary. -/
theorem margin_torsion_free (x : ℚ≥0) (hx : x ≠ 0) (j : ℕ) (hj : j ≠ 0) :
    j • x ≠ 0 := by
  intro h
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with hj' | hx'
  · exact hj (by exact_mod_cast hj')
  · exact hx hx'

/-- **The banked coproduct law, verbatim, at margin tuples.**  A budget
annihilates the pair of per-agent margins iff it annihilates each — no
interaction across agents.  This is `coproduct_nsmul_eq_zero` applied as-is:
the algebraic face of OR-1's profile-independent marginal. -/
theorem cap_margins_coproduct (x y : ℚ≥0) (j : ℕ) :
    j • ((x, y) : ℚ≥0 × ℚ≥0) = 0 ↔ j • x = 0 ∧ j • y = 0 :=
  coproduct_nsmul_eq_zero x y j

/-- **The banked grading law, verbatim, at margin tuples.**  The additive order
of a margin pair is the divisibility-join of the coordinate orders —
`addOrderOf_prod_eq_lcm` applied as-is. -/
theorem cap_margin_order_join (x y : ℚ≥0) :
    addOrderOf ((x, y) : ℚ≥0 × ℚ≥0) = Nat.lcm (addOrderOf x) (addOrderOf y) :=
  addOrderOf_prod_eq_lcm x y

/-! ## The court side: the threshold readout is the idempotent pole -/

/-- The court's value algebra `(Bool, ∨)` has a **nontrivial idempotent**:
`true ∨ true = true` yet `true ≠ false` — the same degeneracy class as the
moment semilattice's `⊤ ⊔ ⊤ = ⊤`. -/
theorem court_readout_idempotent : (true || true) = true ∧ true ≠ false := by
  refine ⟨rfl, ?_⟩
  decide

/-- **The court's value algebra embeds in no group** — the banked
`idempotent_eq_one`, verbatim: any map `ψ` into a group that respects the
operation at the idempotent `true` must collapse it to the identity.  The
algebraic obstruction behind OR-1's `court_value_not_additive`. -/
theorem court_readout_not_group_order {G : Type*} [Group G] (ψ : Bool → G)
    (hψ : ψ true * ψ true = ψ (true || true)) : ψ true = 1 :=
  idempotent_eq_one hψ

/-- **The readout locus, machine-checked.**  The threshold map
`a ↦ (τ ≤ a)` is NOT a homomorphism `(ℚ≥0, +) → (Bool, ∨)`: two sub-threshold
contributions can sum past the threshold (`τ/2 + τ/2 = τ`).  Upstream, the
aggregation is cancellation-free (`margin_zerosumfree`); the boundary is
crossed exactly at the readout. -/
theorem threshold_readout_not_hom (τ : ℚ≥0) (hτ : 0 < τ) :
    ¬ ∀ a b : ℚ≥0, (τ ≤ a + b ↔ τ ≤ a ∨ τ ≤ b) := by
  intro h
  have hhalf : τ / 2 + τ / 2 = τ := add_halves τ
  have hcross : τ ≤ τ / 2 ∨ τ ≤ τ / 2 := (h (τ / 2) (τ / 2)).mp (by rw [hhalf])
  have hlt : τ / 2 < τ := half_lt_self hτ
  rcases hcross with h' | h' <;> exact absurd h' (not_le.mpr hlt)

/-! ## The packaged boundary instance -/

/-- **The keyed-composition boundary instance, packaged.**  The cap side is
cancellation-free (zerosumfree aggregation), the court's value algebra carries
a nontrivial idempotent, and the threshold readout is not a homomorphism at any
positive threshold: the S3 contrast is the banked boundary's two poles, one
lemma, two costumes. -/
theorem keyed_boundary_instance :
    (∀ a b : ℚ≥0, a + b = 0 ↔ a = 0 ∧ b = 0)
    ∧ ((true || true) = true ∧ true ≠ false)
    ∧ (∀ τ : ℚ≥0, 0 < τ → ¬ ∀ a b : ℚ≥0, (τ ≤ a + b ↔ τ ≤ a ∨ τ ≤ b)) :=
  ⟨margin_zerosumfree, court_readout_idempotent, threshold_readout_not_hom⟩

/-! ## Local axiom audit -/

/-- info: 'Sundog.OrderRelative.Keyed.margin_zerosumfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms margin_zerosumfree

/-- info: 'Sundog.OrderRelative.Keyed.margin_torsion_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms margin_torsion_free

/-- info: 'Sundog.OrderRelative.Keyed.cap_margins_coproduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_margins_coproduct

/-- info: 'Sundog.OrderRelative.Keyed.cap_margin_order_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_margin_order_join

/-- info: 'Sundog.OrderRelative.Keyed.court_readout_idempotent' does not depend on any axioms -/
#guard_msgs in
#print axioms court_readout_idempotent

/-- info: 'Sundog.OrderRelative.Keyed.court_readout_not_group_order' depends on axioms: [propext] -/
#guard_msgs in
#print axioms court_readout_not_group_order

/-- info: 'Sundog.OrderRelative.Keyed.threshold_readout_not_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threshold_readout_not_hom

/-- info: 'Sundog.OrderRelative.Keyed.keyed_boundary_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keyed_boundary_instance

end Sundog.OrderRelative.Keyed
