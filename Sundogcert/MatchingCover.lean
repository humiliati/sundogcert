/-
# König — a vertex cover certifies a maximum matching (N-3, find/check ledger)

The second LP-duality instance of `Certifies.weakDuality_tight`, after `MaxFlowMinCut`. A
**vertex cover** is a cheap-to-check *dual* witness that upper-bounds *every* matching's size
(`matching_le_cover`): each matched edge needs a distinct cover vertex, so `|M| ≤ |C|`. Hence a
**tight pair** — a matching and a cover of equal size — certifies that the matching is
**maximum** and the cover is **minimum** at once (`konig`). Only the CHECK is here; *finding*
the maximum matching (augmenting paths / Hopcroft–Karp) is the imported wall.

(Weak duality `|M| ≤ |C|` holds for *all* graphs; the tight pair exists for *bipartite*
graphs — König's theorem — which is exactly where *finding* it succeeds. This module checks a
supplied tight pair; the bipartite-existence search is the imported wall.)
-/
import Sundogcert.Certifies

namespace Sundog.MatchingCover

variable {V : Type*}

/-- A **matching** in `edges`: a sub-set of edges, pairwise vertex-disjoint (two matching
edges that share any endpoint are equal). -/
def IsMatching (edges : Finset (V × V)) (M : Finset (V × V)) : Prop :=
  M ⊆ edges ∧ ∀ e₁ ∈ M, ∀ e₂ ∈ M,
    (e₁.1 = e₂.1 ∨ e₁.1 = e₂.2 ∨ e₁.2 = e₂.1 ∨ e₁.2 = e₂.2) → e₁ = e₂

/-- A **vertex cover** of `edges`: a vertex set meeting every edge. -/
def IsCover (edges : Finset (V × V)) (C : Finset V) : Prop :=
  ∀ e ∈ edges, e.1 ∈ C ∨ e.2 ∈ C

/-- **Weak duality (the cheap dual bound).** Every matching is no larger than every vertex
cover: the map sending a matched edge to one of its endpoints in `C` is injective (distinct
matched edges share no vertex), so `|M| ≤ |C|`. A cover certifies an upper bound on the
maximum matching, checked by scanning the edges. -/
theorem matching_le_cover {edges : Finset (V × V)} {M : Finset (V × V)} {C : Finset V}
    (hM : IsMatching edges M) (hC : IsCover edges C) : M.card ≤ C.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun e => if e.1 ∈ C then e.1 else e.2) ?_ ?_
  · intro e he
    have hcov := hC e (hM.1 he)
    dsimp only
    split_ifs with hc
    · exact hc
    · exact hcov.resolve_left hc
  · intro e₁ he₁ e₂ he₂ heq
    refine hM.2 e₁ he₁ e₂ he₂ ?_
    dsimp only at heq
    split_ifs at heq
    · exact Or.inl heq
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (Or.inl heq))
    · exact Or.inr (Or.inr (Or.inr heq))

/-- **König (the certificate).** A tight matching/cover pair — a matching `M` and a cover `C`
with `|M| = |C|` — certifies *simultaneously* that `|M|` is the **maximum** matching size
(`IsGreatest`) and `|C|` is the **minimum** cover size (`IsLeast`). This is
`Certifies.weakDuality_tight` instantiated with `matching_le_cover`. -/
theorem konig {edges : Finset (V × V)} {M : Finset (V × V)} {C : Finset V}
    (hM : IsMatching edges M) (hC : IsCover edges C) (htight : M.card = C.card) :
    IsGreatest {k : ℕ | ∃ M', IsMatching edges M' ∧ M'.card = k} M.card ∧
      IsLeast {k : ℕ | ∃ C', IsCover edges C' ∧ C'.card = k} C.card := by
  apply Certifies.weakDuality_tight
  · rintro p ⟨M', hM', rfl⟩ d ⟨C', hC', rfl⟩
    exact matching_le_cover hM' hC'
  · exact ⟨M, hM, rfl⟩
  · exact ⟨C, hC, rfl⟩
  · exact htight

/-! ## The verification cost — and the find/check ledger instance -/

/-- A cover certificate's data: the edge set and the proposed cover. -/
structure CoverCert (V : Type*) where
  edges : Finset (V × V)
  C : Finset V

/-- Checking a cover scans every edge (one membership test per edge), plus the size compare. -/
def CoverCert.verifyCost (c : CoverCert V) : ℕ := c.edges.card + 1

/-- The cover certificate plugs into the shared find/check ledger. -/
instance coverCertifies : Certifies.Ledger (CoverCert V) where
  program c := StraightLineCost.StraightLineProgram.ofCost c.verifyCost

/-- **Checking is cheap (`O(|E|)`).** The min-cover bound is verified in `|edges| + 1`
operations — the cheap-CHECK half; *finding* the cover is the imported wall. -/
theorem covercert_cost_le (c : CoverCert V) :
    Certifies.checkCost c ≤ c.edges.card + 1 := le_refl _

end Sundog.MatchingCover
