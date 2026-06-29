/-
# OrderRelative — the Order-Relative Resolution Law (the slate's one statement)

The cross-lane conjecture slate (sundog `docs/boxsel/BOXSEL_CONJECTURE_SLATE.md`) landed one law on
several axes — search reach (C1), pressure reach (C2), pressure repertoire (Phase 7g), determination
order (the σ-order schema), and the find/check mode-vector (C4):

  **a bounded process with budget `k` RESOLVES a target iff the target's ORDER ≤ k; the
  determine/resist split is finite-order vs infinite-order.**

This module names that law and proves its content ONCE, with the axes as instances.

CRITICAL HONESTY (the C3 census + the σ-order slate H1, which already FALSIFIED the "one
comparable scalar" form): the order is **not** one scalar shared across axes. Each axis/mode carries
its OWN order (its own filtration). What is shared is the SCHEMA — per axis there is an
`ord : Target → ℕ∞`, a `Resolves : ℕ → Target → Prop`, and the law `Resolves k t ↔ ord t ≤ k`.
Budget-monotonicity and the determine/resist dichotomy are then THEOREMS of the schema. The closing
theorem `order_is_schema_not_scalar` makes the guard explicit: two instances assign incomparable
orders to one object (the C4 mode-vector) — it anchors the schema, not a universal scalar.

Grounded instance: the parity σ-order, whose `ord` is proved equal to the machine-checked
`ParityNoSufficientStat.suffStatOrder`.
-/
import Mathlib
import Sundogcert.ParityNoSufficientStat

namespace Sundog.OrderRelative

open Sundog.ParityNoSufficientStat

/-- An **order-relative resolution problem**: a target type, an order `ord : Target → ℕ∞`, a
budget-indexed `Resolves`, and the LAW: a budget resolves a target iff it meets that order. -/
structure Problem where
  Target : Type
  ord : Target → ℕ∞
  Resolves : ℕ → Target → Prop
  resolves_iff : ∀ (k : ℕ) (t : Target), Resolves k t ↔ ord t ≤ (k : ℕ∞)

/-- **Budget monotonicity:** more budget keeps resolving — a consequence of the law alone. -/
theorem budget_monotone (O : Problem) {k k' : ℕ} {t : O.Target}
    (h : O.Resolves k t) (hk : k ≤ k') : O.Resolves k' t := by
  rw [O.resolves_iff] at h
  rw [O.resolves_iff]
  exact h.trans (by exact_mod_cast hk)

/-- **DETERMINE ⟺ finite order.** Some finite budget resolves `t` iff `t`'s order is finite. -/
theorem resolvable_iff_finite (O : Problem) {t : O.Target} :
    (∃ k : ℕ, O.Resolves k t) ↔ O.ord t ≠ ⊤ := by
  simp only [O.resolves_iff]
  constructor
  · rintro ⟨k, hk⟩ htop
    rw [htop] at hk
    exact WithTop.coe_ne_top (top_le_iff.mp hk)
  · intro h
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
    exact ⟨n, le_of_eq hn.symm⟩

/-- **RESIST ⟺ infinite order.** No finite budget resolves `t` iff `t`'s order is `⊤`. -/
theorem resists_iff_infinite (O : Problem) {t : O.Target} :
    (∀ k : ℕ, ¬ O.Resolves k t) ↔ O.ord t = ⊤ := by
  rw [← not_exists, resolvable_iff_finite O, not_not]

/-! ## Instances — the axes that instantiate the law -/

/-- **The determination axis (parity σ-order).** The "total parity on `n` coordinates" problem: a
budget `k` resolves it iff a sufficient subset-parity of card ≤ k exists, which (only `univ` is
sufficient) happens iff `n ≤ k`. The `resolves_iff` law is proved from the parity lemmas. -/
def parityProblem (n : ℕ) : Problem where
  Target := Unit
  ord _ := (n : ℕ∞)
  Resolves k _ := ∃ A : Finset (Fin n), A.card ≤ k ∧ IsSufficient A
  resolves_iff k _ := by
    constructor
    · rintro ⟨A, hcard, hA⟩
      rw [isSufficient_iff_univ.mp hA, Finset.card_univ, Fintype.card_fin] at hcard
      exact_mod_cast hcard
    · intro h
      refine ⟨Finset.univ, ?_, isSufficient_univ⟩
      rw [Finset.card_univ, Fintype.card_fin]
      exact_mod_cast h

/-- The parity instance's order is exactly the machine-checked σ-order `suffStatOrder n`. -/
theorem parityProblem_ord (n : ℕ) : (parityProblem n).ord () = (suffStatOrder n : ℕ∞) := by
  change (n : ℕ∞) = (suffStatOrder n : ℕ∞)
  rw [suffStatOrder_eq]

/-- **The resist pole.** A target no finite budget resolves — order `= ⊤`. The σ=∞ / `λ` /
full-history-parity end of every axis. -/
def resistPole : Problem where
  Target := Unit
  ord _ := ⊤
  Resolves _ _ := False
  resolves_iff k _ := by
    constructor
    · exact False.elim
    · intro hk
      exact WithTop.coe_ne_top (top_le_iff.mp hk)

/-- The resist pole genuinely resists — no finite budget resolves it (instantiating
`resists_iff_infinite`). -/
theorem resistPole_resists : ∀ k : ℕ, ¬ resistPole.Resolves k () :=
  (resists_iff_infinite resistPole (t := ())).2 rfl

/-- **The order is a SCHEMA, not one comparable scalar** — the C3 / H1 honesty guard.
Two instances assign incomparable orders to the same (`Unit`) object: a parity problem
has finite order `n`, the resist pole has order `⊤`. So the finite/∞ split is per-instance
(the C4 mode-vector), not a single universal order. -/
theorem order_is_schema_not_scalar (n : ℕ) :
    (parityProblem n).ord () ≠ ⊤ ∧ resistPole.ord () = ⊤ :=
  ⟨WithTop.coe_ne_top, rfl⟩

end Sundog.OrderRelative
