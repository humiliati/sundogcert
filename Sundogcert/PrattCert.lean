/-
# Pratt — a primitive-root witness certifies primality (N-3, find/check ledger)

The number-theoretic instance of the find/check ledger: the classic Pratt certificate showing
**primality is in NP**. A witness for `p` is a primitive root `a mod p` of order `p-1` —
`a^(p-1) = 1` and `a^((p-1)/q) ≠ 1` for every prime `q ∣ p-1` — verifiable by a handful of
modular exponentiations. `cert_sound` (Lucas's theorem, imported from mathlib) turns the witness
into a proof `p.Prime`; `cert_complete` (a primitive root of a cyclic group) shows every prime
has one, so `prime_iff_witness` characterizes primality as exactly the certifiable property.

Only the CHECK is here. *Finding* the witness — a primitive root plus the factorization of
`p-1`, each prime factor itself recursively Pratt-certified — is the imported wall (factoring
`p-1` is the hard search; the soundness `lucas_primality` and completeness
`reverse_lucas_primality` are mathlib's).
-/
import Sundogcert.Certifies
import Mathlib.NumberTheory.LucasPrimality

namespace Sundog.PrattCert

/-- A **Pratt witness** for `p`: a primitive root `a mod p` of order `p-1` — `a^(p-1) = 1`
and `a^((p-1)/q) ≠ 1` for every prime `q ∣ p-1`. -/
structure Witness (p : ℕ) where
  a : ZMod p
  pow_eq : a ^ (p - 1) = 1
  pow_div_ne : ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1

/-- **Soundness (cert ⟹ prime).** A Pratt witness certifies primality — exactly Lucas's
theorem. The witness *is* the proof; checking it is a handful of modular exponentiations. -/
theorem cert_sound {p : ℕ} (w : Witness p) : p.Prime :=
  lucas_primality p w.a w.pow_eq w.pow_div_ne

/-- **Completeness (prime ⟹ a cert exists).** Every prime has a Pratt witness (a primitive
root of the cyclic unit group), so primality is exactly the certifiable property. -/
theorem cert_complete {p : ℕ} (hp : p.Prime) : Nonempty (Witness p) :=
  let ⟨a, ha, hb⟩ := reverse_lucas_primality p hp
  ⟨⟨a, ha, hb⟩⟩

/-- **Primality is certifiable (the capstone).** `p` is prime **iff** it has a Pratt witness —
the Lucas characterization, packaged as the certificate's soundness + completeness. -/
theorem prime_iff_witness {p : ℕ} : p.Prime ↔ Nonempty (Witness p) :=
  ⟨cert_complete, fun ⟨w⟩ => cert_sound w⟩

/-! ## The verification cost — and the find/check ledger instance -/

/-- A Pratt certificate's data: `p`, the prime factors of `p-1`, and the primitive root. -/
structure PrattData where
  p : ℕ
  factors : List ℕ
  root : ℕ

/-- Checking: one modular exponentiation for `a^(p-1)`, plus one per prime factor of `p-1`
(`a^((p-1)/q)`); each modexp is `O(log p)`. -/
def PrattData.verifyCost (d : PrattData) : ℕ := d.factors.length + 1

/-- The Pratt certificate plugs into the shared find/check ledger. -/
instance prattCertifies : Certifies.Ledger PrattData where
  program d := StraightLineCost.StraightLineProgram.ofCost d.verifyCost

/-- **Checking is cheap.** Verifying a Pratt witness costs `|factors| + 1` modular
exponentiations (each `O(log p)`) — the cheap-CHECK half; *finding* the root and the
factorization of `p-1` is the imported wall. -/
theorem prattcert_cost_le (d : PrattData) :
    Certifies.checkCost d ≤ d.factors.length + 1 := le_refl _

end Sundog.PrattCert
