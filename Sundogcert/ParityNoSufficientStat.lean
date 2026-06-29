/-
# P-1: the parity barrier as a no-finite-order-sufficient-statistic theorem (toy half)

Parity-barrier hooks slate (`docs/parity/PARITY_BARRIER_HOOKS_SLATE.md`, Rank-1 P-1),
seeded by the H9-strong result. The H9-strong toy: uniform bits `b : Fin n → ZMod 2`;
the readout latent rides the TOTAL parity `T b = ∑ i, b i` (the causal state, which
needs the whole history). A "finite-order statistic" is a partial parity
`pS A b = ∑ i ∈ A, b i` over a fixed index set `A`.

## What is PROVED here (about the TOY, NOT about λ)

* `parity_split` — `T b = pS A b + pS Aᶜ b` (total parity = partial ⊕ complementary).
* `pS_flip` / `pS_compl_flip` — flipping a coordinate `j ∉ A` (adding `Pi.single j 1`)
  leaves the partial parity over `A` unchanged and flips the complementary parity.
* `partial_parity_underdetermines_total` — for any proper `A` (some `j ∉ A`) and any
  `b`, the flip produces `b'` with the SAME partial parity but the OPPOSITE total
  parity. The complementary parity is a free fair coin.
* `partial_not_sufficient` — hence for `A ≠ univ` there exist two inputs agreeing on
  the partial parity but disagreeing on the total: a partial (finite-order) parity is
  **not a sufficient statistic** for the total parity.

## The IMPORTED WALL (named, NOT proved; the toy's positive does NOT transfer)

Sarnak's conjecture — the Liouville function `λ(n) = (−1)^Ω(n)` is disjoint from every
zero-entropy sequence — and Chowla. `λ` is the SAME object class (a parity of a driver
with no finite-order sufficient statistic), but its driver is the primes, whose causal
state we cannot compute; that is exactly why Sarnak/Chowla are open. The toy theorem
below says nothing about `λ`. See `docs/parity/PARITY_DICTIONARY.md` for the
definitions-level dictionary and the explicit non-transfer fence.
-/
import Mathlib

namespace Sundog.ParityNoSufficientStat

variable {n : ℕ}

/-- Partial parity over a finite index set `A` (a finite-order statistic). -/
def pS (A : Finset (Fin n)) (b : Fin n → ZMod 2) : ZMod 2 := ∑ i ∈ A, b i

/-- Total parity — the toy's causal-state latent (needs the whole history). -/
def T (b : Fin n → ZMod 2) : ZMod 2 := ∑ i, b i

/-- **Total parity decomposes as partial ⊕ complementary.** This is the structural
heart: the total parity is the partial parity over `A` plus the parity over its
complement. -/
theorem parity_split (A : Finset (Fin n)) (b : Fin n → ZMod 2) :
    T b = pS A b + pS Aᶜ b := by
  simp only [T, pS]
  exact (Finset.sum_add_sum_compl A b).symm

/-- **Flipping a coordinate outside `A` preserves the partial parity over `A`.** -/
theorem pS_flip (A : Finset (Fin n)) {j : Fin n} (hj : j ∉ A) (b : Fin n → ZMod 2) :
    pS A (b + Pi.single j 1) = pS A b := by
  simp only [pS, Pi.add_apply, Finset.sum_add_distrib]
  have hz : ∑ i ∈ A, (Pi.single j (1 : ZMod 2)) i = 0 :=
    Finset.sum_eq_zero (fun i hi => Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi hj) 1)
  rw [hz, add_zero]

/-- **Flipping a coordinate `j ∉ A` flips the complementary parity.** The complementary
parity is the free fair coin that randomizes the total. -/
theorem pS_compl_flip (A : Finset (Fin n)) {j : Fin n} (hj : j ∉ A) (b : Fin n → ZMod 2) :
    pS Aᶜ (b + Pi.single j 1) = pS Aᶜ b + 1 := by
  have hjc : j ∈ Aᶜ := Finset.mem_compl.mpr hj
  simp only [pS, Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single_of_mem j hjc
        (fun i _ hij => Pi.single_eq_of_ne hij 1)]
  exact Pi.single_eq_same j 1

/-- **The complementary parity randomizes the total (per input).** For any proper `A`
(`j ∉ A`) and any `b`, flipping `j` keeps the partial parity over `A` fixed while
flipping the total parity: the partial parity does not determine the total. -/
theorem partial_parity_underdetermines_total (A : Finset (Fin n)) {j : Fin n} (hj : j ∉ A)
    (b : Fin n → ZMod 2) :
    pS A (b + Pi.single j 1) = pS A b ∧ T (b + Pi.single j 1) = T b + 1 := by
  refine ⟨pS_flip A hj b, ?_⟩
  rw [parity_split A (b + Pi.single j 1), parity_split A b, pS_flip A hj b, pS_compl_flip A hj b]
  ring

/-- **No finite-order sufficient statistic (toy).** For any proper index set `A ≠ univ`,
there are two inputs that agree on the partial parity over `A` yet disagree on the total
parity. So a finite-order partial parity is not a sufficient statistic for the
full-history total parity — the content of the parity barrier, proved on the toy. -/
theorem partial_not_sufficient (A : Finset (Fin n)) (hA : A ≠ Finset.univ) :
    ∃ b b' : Fin n → ZMod 2, pS A b = pS A b' ∧ T b ≠ T b' := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ A := by
    by_contra h
    exact hA (Finset.eq_univ_iff_forall.mpr (by simpa using h))
  refine ⟨0, 0 + Pi.single j 1, (pS_flip A hj 0).symm, ?_⟩
  rw [(partial_parity_underdetermines_total A hj 0).2]
  intro h
  have h0 : T (0 : Fin n → ZMod 2) + (0 : ZMod 2) = T (0 : Fin n → ZMod 2) + 1 := by
    rw [add_zero]; exact h
  exact one_ne_zero (add_left_cancel h0).symm

end Sundog.ParityNoSufficientStat
