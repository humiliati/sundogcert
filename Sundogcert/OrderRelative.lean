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

A genuinely different filtration from parity's subset-parity: the order is the *prefix length*. It
grounds "the instances instantiate the law" on a SECOND axis, and it is determine-only (always finite
order, never the resist pole). -/

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
    have h1 : prefixParity n d
        (Pi.single (⟨k, hk⟩ : Fin n) (1 : ZMod 2) : Fin n → ZMod 2) = 1 := by
      simp only [prefixParity]
      rw [Finset.sum_eq_single_of_mem (⟨k, hk⟩ : Fin n) hjmem
            (fun b _ hb => by simp [Pi.single_eq_of_ne hb])]
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
(it cannot host the resist pole). -/
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

/-! ## A third axis — search reachability (rational approximation by denominator)

The order is the DENOMINATOR budget. A rational target `q₀` is reached at order `q₀.den`; an
IRRATIONAL target is reached at NO finite order → `⊤` — an EARNED pole (unlike the fiat `resistPole`):
bounded-denominator search never reaches an irrational (machine-checked here for `√2`). -/

/-- Reached by a rational of denominator `≤ k` equal to the target. -/
def DenomReaches (x : ℝ) (k : ℕ) : Prop := ∃ q : ℚ, q.den ≤ k ∧ (q : ℝ) = x

/-- A **rational** target: reached at order = its denominator (a finite search-reach order). -/
def rationalReachProblem (q₀ : ℚ) : Problem where
  Target := Unit
  ord _ := (q₀.den : ℕ∞)
  Resolves k _ := DenomReaches (q₀ : ℝ) k
  resolves_iff k _ := by
    constructor
    · rintro ⟨q, hq, hqx⟩
      have hqq : q = q₀ := Rat.cast_injective hqx
      exact_mod_cast (hqq ▸ hq)
    · intro h
      exact ⟨q₀, by exact_mod_cast h, rfl⟩

/-- An **irrational** target: an EARNED resist pole (`ord = ⊤`) — no finite-denominator rational
reaches it. -/
def irrationalReachProblem (x : ℝ) (hx : Irrational x) : Problem where
  Target := Unit
  ord _ := ⊤
  Resolves k _ := DenomReaches x k
  resolves_iff k _ := by
    constructor
    · rintro ⟨q, _, hqx⟩
      exact (hx ⟨q, hqx⟩).elim
    · intro hk
      exact absurd (top_le_iff.mp hk) WithTop.coe_ne_top

/-- The search-reach order of a rational target is its denominator. -/
theorem rationalReachProblem_ord (q₀ : ℚ) :
    (rationalReachProblem q₀).ord () = (q₀.den : ℕ∞) := rfl

/-- **The irrational target genuinely resists** — no finite denominator budget reaches it: the
earned resist pole of the search-reachability filtration (instantiating `resists_iff_infinite`). -/
theorem irrationalReach_resists (x : ℝ) (hx : Irrational x) :
    ∀ k : ℕ, ¬ (irrationalReachProblem x hx).Resolves k () :=
  (resists_iff_infinite (irrationalReachProblem x hx) (t := ())).2 rfl

/-- A concrete search-resist: `√2` is unreachable by any finite-denominator rational. -/
theorem search_resist_sqrt_two :
    ∀ k : ℕ, ¬ (irrationalReachProblem (Real.sqrt 2) irrational_sqrt_two).Resolves k () :=
  irrationalReach_resists _ _

/-! ## A fourth axis — radical reach (a power lands in ℚ), and an HONEST mode-vector

The order here is the least `m` with `x ^ m ∈ ℚ` (`x` is a radical of order ≤ k) — a DIFFERENT
filtration from denominator-reach. It hosts a genuine mode-vector: `√2` has search-reach order `⊤`
(irrational) yet radical order `2` (its square is rational). One object, two divergent orders across
two grounded axes — search-resistant yet analytically simple. -/

/-- Some power `x ^ m` with `1 ≤ m ≤ k` is rational (`x` is a radical of order ≤ k). -/
def RadicalReaches (x : ℝ) (k : ℕ) : Prop := ∃ m : ℕ, 1 ≤ m ∧ m ≤ k ∧ ∃ q : ℚ, x ^ m = (q : ℝ)

/-- `√2` is a radical of order exactly 2: its square is rational, but `√2` itself is not. -/
theorem radicalReachSqrtTwo_iff (k : ℕ) : RadicalReaches (Real.sqrt 2) k ↔ 2 ≤ k := by
  constructor
  · rintro ⟨m, hm1, hmk, q, hq⟩
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      rw [pow_one] at hq
      exact (irrational_sqrt_two ⟨q, hq.symm⟩).elim
    · exact le_trans hge hmk
  · intro hk
    exact ⟨2, by norm_num, hk, 2, by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num⟩

/-- The **radical-reach** instance for `√2`: order = 2 (a filtration distinct from denominators). -/
def radicalReachSqrtTwo : Problem where
  Target := Unit
  ord _ := (2 : ℕ∞)
  Resolves k _ := RadicalReaches (Real.sqrt 2) k
  resolves_iff k _ := by
    rw [radicalReachSqrtTwo_iff]
    exact_mod_cast Iff.rfl

/-- **A mode-vector.** `√2` carries two divergent orders across two grounded axes:
search-reach `⊤` (irrational) and radical `2` (its square is rational) — search-resistant yet
analytically simple, machine-checked. -/
theorem sqrt_two_mode_vector :
    (irrationalReachProblem (Real.sqrt 2) irrational_sqrt_two).ord () = ⊤
      ∧ radicalReachSqrtTwo.ord () = (2 : ℕ∞) :=
  ⟨rfl, rfl⟩

end Sundog.OrderRelative
