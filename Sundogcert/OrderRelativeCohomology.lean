/-
# OrderRelative — a topological / cohomological order axis (torsion vs free)

A seventh instance family for the Order-Relative Resolution Law. The order is the **additive
(torsion) order** of a (co)homology class: the least budget `k` whose `k`-fold sum annihilates
the class. **DETERMINE ⟺ the class is TORSION** (finite order, killed by some finite `k`);
**RESIST ⟺ the class is FREE** (infinite order, never killed).

Grounded: the torsion side on `ZMod m` (a torsion cohomology group — e.g. `H¹` of a lens space),
the EARNED resist pole on `ℤ`, the free class. `ℤ = H¹(S¹)` is the Aharonov–Bohm winding / `∮A`
flux period (companion module `FaradayAB`, `loop_integral_eq_flux`): a free `ℤ`-class no finite
local budget resolves — "the local loop is blind to the global `∮A`." The group-theoretic core
(`ℤ` torsion-free, `ZMod m` torsion) is machine-checked here; that `ℤ` IS the `H¹` flux period is
the named topological wall, exactly as `FaradayAB` names it.
-/
import Sundogcert.OrderRelative

namespace Sundog.OrderRelative.Cohomology

open Sundog.OrderRelative

/-- A budget of `k` resolves a class `g` iff some multiple `1 ≤ j ≤ k` annihilates it
(`j • g = 0`) — i.e. the class is torsion of order `≤ k`. -/
def AnnihilatedBy {G : Type*} [AddMonoid G] (g : G) (k : ℕ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ j • g = 0

/-- **The free class (`1 : ℤ`) — order `⊤`, the EARNED resist pole.** `ℤ = H¹(S¹)` is the
Aharonov–Bohm winding / `∮A` flux period (`FaradayAB.loop_integral_eq_flux`): torsion-free, so no
finite budget annihilates it — the local loop is blind to the global flux. -/
def freeClassProblem : Problem where
  Target := Unit
  ord _ := ⊤
  Resolves k _ := AnnihilatedBy (1 : ℤ) k
  resolves_iff k _ := by
    constructor
    · rintro ⟨j, hj1, _, hj0⟩
      rw [nsmul_eq_mul, mul_one] at hj0
      have : j = 0 := by exact_mod_cast hj0
      exact absurd this (by omega)
    · intro hk
      exact absurd (top_le_iff.mp hk) WithTop.coe_ne_top

/-- **A torsion class (`1 : ZMod m`, `m ≥ 1`) — order `m`, the determine side.** A torsion
cohomology group (e.g. `H¹` of a lens space): the generator is annihilated by the budget `m`,
and by no smaller one. -/
def torsionClassProblem (m : ℕ) (hm : 1 ≤ m) : Problem where
  Target := Unit
  ord _ := (m : ℕ∞)
  Resolves k _ := AnnihilatedBy (1 : ZMod m) k
  resolves_iff k _ := by
    haveI : NeZero m := ⟨by omega⟩
    constructor
    · rintro ⟨j, hj1, hjk, hj0⟩
      rw [nsmul_eq_mul, mul_one, CharP.cast_eq_zero_iff (ZMod m) m] at hj0
      have hmj : m ≤ j := Nat.le_of_dvd (by omega) hj0
      exact_mod_cast le_trans hmj hjk
    · intro hk
      have hmk : m ≤ k := by exact_mod_cast hk
      exact ⟨m, hm, hmk, by rw [nsmul_eq_mul, mul_one]; exact ZMod.natCast_self m⟩

/-- The free class is an EARNED resist pole — no finite budget resolves it (instantiating
`resists_iff_infinite`, grounded on `ℤ` being torsion-free). -/
theorem freeClass_resists : ∀ k : ℕ, ¬ freeClassProblem.Resolves k () :=
  (resists_iff_infinite freeClassProblem (t := ())).2 rfl

/-- **The topological dichotomy: determine ⟺ torsion, resist ⟺ free.** A torsion class
(`ZMod m`) has finite order `m`; the free class (`ℤ`, the AB flux period) has order `⊤`. -/
theorem torsion_vs_free (m : ℕ) (hm : 1 ≤ m) :
    (torsionClassProblem m hm).ord () = (m : ℕ∞) ∧ freeClassProblem.ord () = ⊤ :=
  ⟨rfl, rfl⟩

/-!
### The cohomological mode-vector — the order of a MIXED class is genuinely a vector

For a mixed class `(1,1) ∈ ℤ × ZMod m` (free ⊕ torsion), the scalar additive-order COLLAPSES to
`⊤`: the free part forces infinite order, so the scalar verdict says "resist" and HIDES that the
torsion part is resolvable at budget `m`. The faithful order is the free/torsion projection vector
`(⊤, m)` — determine in the torsion coordinate, resist in the free coordinate, on one object.

Unlike the `√2` / box-optimum mode-vectors (two *chosen* filtrations), this is the CANONICAL
free/torsion decomposition — an intrinsic mode-vector. Honest caveat: it is **structural, not
deep** — the divergence is built into the direct sum (the structure theorem), not an earned
surprise. The content is precisely that the scalar resolution verdict is *lossy on mixed classes*.
-/

/-- **The mixed class `(1,1) ∈ ℤ × ZMod m` — scalar order `⊤`.** The free part dominates the
additive order, so the scalar verdict collapses to resist regardless of the torsion part. -/
def mixedClassProblem (m : ℕ) (_hm : 1 ≤ m) : Problem where
  Target := Unit
  ord _ := ⊤
  Resolves k _ := AnnihilatedBy ((1, 1) : ℤ × ZMod m) k
  resolves_iff k _ := by
    constructor
    · rintro ⟨j, hj1, _, hj0⟩
      have hj : j = 0 := by
        have h := congrArg Prod.fst hj0
        have h' : (j : ℤ) = 0 := by simpa [nsmul_eq_mul] using h
        exact_mod_cast h'
      exact absurd hj (by omega)
    · intro hk
      exact absurd (top_le_iff.mp hk) WithTop.coe_ne_top

/-- The mixed class is a resist pole under the SCALAR order (the free part dominates). -/
theorem mixed_scalar_resists (m : ℕ) (hm : 1 ≤ m) :
    ∀ k : ℕ, ¬ (mixedClassProblem m hm).Resolves k () :=
  (resists_iff_infinite (mixedClassProblem m hm) (t := ())).2 rfl

/-- **The cohomological mode-vector.** On the single object `(1,1) ∈ ℤ × ZMod m`: the scalar order
collapses to `⊤`, yet the free/torsion projection-vector is `(⊤, m)` — and the teeth are that the
torsion projection genuinely RESOLVES at budget `m` while the joint class never resolves. The scalar
determine/resist verdict is therefore strictly lossy: it reports the free coordinate and hides the
resolvable torsion coordinate. -/
theorem mixed_mode_vector (m : ℕ) (hm : 1 ≤ m) :
    (mixedClassProblem m hm).ord () = ⊤
      ∧ freeClassProblem.ord () = ⊤
      ∧ (torsionClassProblem m hm).ord () = (m : ℕ∞)
      ∧ (torsionClassProblem m hm).Resolves m ()
      ∧ (∀ k, ¬ (mixedClassProblem m hm).Resolves k ()) :=
  ⟨rfl, rfl, rfl,
    ⟨m, hm, le_rfl, by rw [nsmul_eq_mul, mul_one]; exact ZMod.natCast_self m⟩,
    mixed_scalar_resists m hm⟩

end Sundog.OrderRelative.Cohomology
