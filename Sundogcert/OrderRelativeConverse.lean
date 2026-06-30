/-
# OrderRelative — the converse FAILS, and the coproduct law unified

The characterization "join-homomorphic axes = group-order axes" has a true direction (group order ⇒
join-homomorphic on the coproduct — `annihilates_prod` / `mul_annihilates_prod`) and a FALSE
converse, broken here with its exact obstruction.

**The converse fails (idempotency is the obstruction).** The moment axis is join-homomorphic, but
its order monoid is a join-**semilattice**: the "no-mean" class `c` is **idempotent** under
convolution (`c ⊛ c = c` — two no-mean populations convolve to no-mean) yet has `ord c = ⊤`. A
**group has no nontrivial idempotent** (`idempotent_eq_one`: `g·g = g ⟹ g = 1`), so any monoid map
from the moment order monoid to a group collapses `c` to the identity — order `1`, not `⊤`. Hence
the moment order canNOT be a group order — *why* moment is "degenerate": a semilattice, not a group.

**Coproduct law unified.** `coproduct_pow_eq_one` is the single monoid statement
`(x,y)ʲ = 1 ↔ xʲ = 1 ∧ yʲ = 1`; additive `annihilates_prod` and multiplicative
`mul_annihilates_prod`
are its two faces.
-/
import Sundogcert.OrderRelative

namespace Sundog.OrderRelative.Converse

/-- **The obstruction: a group has no nontrivial idempotent.** `g · g = g ⟹ g = 1`. -/
theorem idempotent_eq_one {G : Type*} [Group G] {g : G} (h : g * g = g) : g = 1 := by
  have h2 : g * g = g * 1 := by rwa [mul_one]
  exact mul_left_cancel h2

/-- The moment / semilattice order monoid `(ℕ∞, ⊔, ⊥)` has a **nontrivial idempotent**: `⊤` (the
no-mean class) — `⊤ ⊔ ⊤ = ⊤` yet `⊤ ≠ 0`. A group's only idempotent is the identity. -/
theorem moment_idempotent_nontrivial : (⊤ : ℕ∞) ⊔ ⊤ = ⊤ ∧ (⊤ : ℕ∞) ≠ 0 := by
  refine ⟨?_, ?_⟩ <;> simp

/-- **The converse FAILS: the moment order is not a group order.** Any map `ψ` from the moment order
monoid `(ℕ∞, ⊔)` to a group that respects the operation at the idempotent `⊤` must send `⊤` to the
identity (`ψ ⊤ = 1`, order `1`) — it cannot match `ord(⊤-class) = ⊤`. So a join-homomorphic order
can fail to be a group order; idempotency is the obstruction. -/
theorem converse_fails {G : Type*} [Group G] (ψ : ℕ∞ → G)
    (hψ : ψ ⊤ * ψ ⊤ = ψ (⊤ ⊔ ⊤)) : ψ ⊤ = 1 := by
  rw [sup_idem] at hψ
  exact idempotent_eq_one hψ

/-- **The coproduct law, unified — one source, both faces.** In ANY monoid, a budget `j` annihilates
the coproduct `(x, y)` iff it annihilates both coordinates. `@[to_additive]` generates the additive
face `coproduct_nsmul_eq_zero` (`j • (x,y) = 0 ↔ j • x = 0 ∧ j • y = 0`); the cohomological
`annihilates_prod` and radical `mul_annihilates_prod` are its two concrete-group instances. -/
@[to_additive]
theorem coproduct_pow_eq_one {G H : Type*} [Monoid G] [Monoid H] (x : G) (y : H) (j : ℕ) :
    (x, y) ^ j = 1 ↔ x ^ j = 1 ∧ y ^ j = 1 := by
  simp [Prod.ext_iff]

end Sundog.OrderRelative.Converse
