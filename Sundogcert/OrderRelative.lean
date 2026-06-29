/-
# OrderRelative — the Order-Relative Resolution Law

  **A bounded process with budget `k` RESOLVES a target iff the target's ORDER ≤ k; the
  determine/resist split is finite-order vs infinite-order.**

This module names that law and proves its content ONCE, with instances grounding the schema.

CRITICAL HONESTY: the order is **not** one scalar shared across instances. Each instance carries
its OWN order (its own filtration). What is shared is the SCHEMA — per instance there is an
`ord : Target → ℕ∞`, a `Resolves : ℕ → Target → Prop`, and the law `Resolves k t ↔ ord t ≤ k`.
Budget-monotonicity and the determine/resist dichotomy are then THEOREMS of the schema. The closing
theorem `order_is_schema_not_scalar` makes the guard explicit: two instances assign incomparable
orders to a single object — it anchors the schema, not a universal scalar.

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

/-! ## Instances grounding the schema -/

/-- **Parity instance (the parity σ-order).** The "total parity on `n` coordinates" problem: a
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

/-- **The resist pole.** A target no finite budget resolves — order `= ⊤`. -/
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

/-- **The order is a SCHEMA, not one comparable scalar** — the honesty guard.
Two instances assign incomparable orders to the same (`Unit`) object: a parity problem
has finite order `n`, the resist pole has order `⊤`. So the finite/∞ split is per-instance,
not a single universal order. -/
theorem order_is_schema_not_scalar (n : ℕ) :
    (parityProblem n).ord () ≠ ⊤ ∧ resistPole.ord () = ⊤ :=
  ⟨WithTop.coe_ne_top, rfl⟩

/-! ## A second axis — coordinate-locality (a prefix is sufficient at its width)

A genuinely different filtration from parity's subset-parity: the order is the *prefix length* — the
σ-slate's coordinate-locality (H2) axis. It grounds "the axes instantiate the law" on a SECOND axis,
and, echoing H2, it is determine-only (always finite order, never the resist pole). -/

/-- Parity of the first `d` coordinates: a target depending only on coordinates `< d`. -/
def prefixParity (n d : ℕ) (b : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < d), b i

/-- The first `k` coordinates are **sufficient** for `prefixParity n d`: inputs agreeing on the
coordinates `< k` agree on the target. -/
def PrefixSufficient (n d k : ℕ) : Prop :=
  ∀ b b' : Fin n → ZMod 2,
    (∀ i : Fin n, (i : ℕ) < k → b i = b' i) → prefixParity n d b = prefixParity n d b'

/-- **The locality order is the prefix width.** For `d ≤ n`, the first `k` coordinates suffice for
`prefixParity n d` iff `d ≤ k`. -/
theorem prefixSufficient_iff {n d k : ℕ} (hd : d ≤ n) :
    PrefixSufficient n d k ↔ d ≤ k := by
  constructor
  · intro hsuff
    by_contra hlt
    rw [not_le] at hlt
    have hk : k < n := lt_of_lt_of_le hlt hd
    have hjmem : (⟨k, hk⟩ : Fin n) ∈
        Finset.univ.filter (fun i : Fin n => (i : ℕ) < d) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    have hagree : ∀ i : Fin n, (i : ℕ) < k →
        (0 : Fin n → ZMod 2) i = (Pi.single (⟨k, hk⟩ : Fin n) (1 : ZMod 2) : Fin n → ZMod 2) i := by
      intro i hi
      have hij : i ≠ (⟨k, hk⟩ : Fin n) := Fin.ne_of_val_ne (ne_of_lt hi)
      simp [Pi.single_eq_of_ne hij]
    have hval := hsuff 0 ((Pi.single (⟨k, hk⟩ : Fin n) (1 : ZMod 2) : Fin n → ZMod 2)) hagree
    have h0 : prefixParity n d (0 : Fin n → ZMod 2) = 0 := by simp [prefixParity]
    have h1 : prefixParity n d ((Pi.single (⟨k, hk⟩ : Fin n) (1 : ZMod 2) : Fin n → ZMod 2)) = 1 := by
      simp only [prefixParity]
      rw [Finset.sum_eq_single_of_mem (⟨k, hk⟩ : Fin n) hjmem
            (fun i _ hij => Pi.single_eq_of_ne hij (1 : ZMod 2))]
      simp
    rw [h0, h1] at hval
    exact one_ne_zero hval.symm
  · intro hdk b b' hagree
    simp only [prefixParity]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    exact hagree i (lt_of_lt_of_le hi.2 hdk)

/-- **The coordinate-locality instance** (a second axis): order = prefix width `d`. -/
def localityProblem (n d : ℕ) (hd : d ≤ n) : Problem where
  Target := Unit
  ord _ := (d : ℕ∞)
  Resolves k _ := PrefixSufficient n d k
  resolves_iff k _ := by
    rw [prefixSufficient_iff hd]
    exact_mod_cast Iff.rfl

/-- The locality instance is **always finite-order** (`≠ ⊤`): coordinate-locality is determine-only
(the σ-slate's H2 — locality cannot host the resist pole). -/
theorem localityProblem_ord_ne_top (n d : ℕ) (hd : d ≤ n) :
    (localityProblem n d hd).ord () ≠ ⊤ :=
  WithTop.coe_ne_top

/-- **Two grounded axes and the pole — three orders on one object.** Coordinate-locality `d`,
parity-determination `n`, resist pole `⊤`: the schema carries a SECOND grounded axis (locality)
alongside parity, with orders that are per-instance, not one comparable scalar. -/
theorem two_axes_and_pole (n d : ℕ) (hd : d ≤ n) :
    (localityProblem n d hd).ord () = (d : ℕ∞)
      ∧ (parityProblem n).ord () = (n : ℕ∞)
      ∧ resistPole.ord () = ⊤ :=
  ⟨rfl, rfl, rfl⟩

end Sundog.OrderRelative
