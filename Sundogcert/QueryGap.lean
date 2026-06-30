/-
# A non-imported find/check gap: unstructured search in the query model (S3-3)

Every instance in the find/check ledger (`Certifies` + its seven cheap-CHECK theorems) shares one
honest caveat: the CHECK side is machine-checked cheap, but the FIND/hardness side is *imported*
(factoring for Pratt witnesses, max-flow algorithms, SCC construction, …). This module supplies
the ledger's **first instance where the gap itself is proved** — `check ≪ find` with *both* sides
in Lean, nothing imported — in the decision-tree (query) complexity model.

The toy is unstructured search over `x : Fin n → Bool`:

* **CHECK** a supplied witness `i` — "is position `i` marked?" — costs **one** query
  (`checkTree`, `checkTree_depth`).
* **FIND** — any decision tree that correctly decides `∃ i, x i = true` must make **`≥ n`**
  queries in the worst case (`search_needs_n_queries`), by the standard adversary argument: on the
  all-false input it must query *every* position, or an unqueried position could be flipped without
  changing the tree's answer.

So `check_lt_find`: for `n ≥ 2`, the witness-checker is strictly cheaper than any correct finder —
a machine-checked `check ≪ find`, the named falsifier `GAP_COLLAPSES_IN_MODEL` not firing. This is
not an unconditional P-vs-NP separation: it is an *unconditional lower bound in a restricted model*,
which is exactly what lets it be proved rather than imported.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Sundog.QueryGap

/-- A deterministic **decision tree** querying Boolean coordinates of an input `Fin n → Bool`.
`query i l r` reads position `i`; on `false` it descends into `l`, on `true` into `r`. -/
inductive DTree (n : ℕ) (α : Type*) where
  | leaf : α → DTree n α
  | query : Fin n → DTree n α → DTree n α → DTree n α

variable {n : ℕ} {α : Type*}

/-- The output of running the tree on an input. -/
def DTree.eval : DTree n α → (Fin n → Bool) → α
  | .leaf a, _ => a
  | .query i l r, x => if x i then r.eval x else l.eval x

/-- The worst-case query count (tree depth). -/
def DTree.depth : DTree n α → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max l.depth r.depth

/-- The set of positions queried along the path taken on input `x`. -/
def DTree.queriedOn : DTree n α → (Fin n → Bool) → Finset (Fin n)
  | .leaf _, _ => ∅
  | .query i l r, x => insert i (if x i then r.queriedOn x else l.queriedOn x)

/-- **Path determinacy.** If two inputs agree on every position queried along `x`'s path, the tree
returns the same output on both. (The path only branches on queried positions.) -/
theorem eval_eq_of_agree (t : DTree n α) :
    ∀ {x y : Fin n → Bool}, (∀ i ∈ t.queriedOn x, x i = y i) → t.eval x = t.eval y := by
  induction t with
  | leaf a => intro x y _; rfl
  | query i l r ihl ihr =>
    intro x y h
    simp only [DTree.queriedOn] at h
    have hxiy : x i = y i := h i (Finset.mem_insert_self _ _)
    simp only [DTree.eval]
    by_cases hxi : x i = true
    · rw [if_pos hxi, if_pos (hxiy ▸ hxi)]
      refine ihr (fun j hj => h j ?_)
      rw [if_pos hxi]; exact Finset.mem_insert_of_mem hj
    · rw [if_neg hxi, if_neg (hxiy ▸ hxi)]
      refine ihl (fun j hj => h j ?_)
      rw [if_neg hxi]; exact Finset.mem_insert_of_mem hj

/-- The queried set along any path has at most `depth`-many elements. -/
theorem card_queriedOn_le_depth (t : DTree n α) (x : Fin n → Bool) :
    (t.queriedOn x).card ≤ t.depth := by
  induction t with
  | leaf a => simp [DTree.queriedOn, DTree.depth]
  | query i l r ihl ihr =>
    simp only [DTree.queriedOn, DTree.depth]
    by_cases hxi : x i = true
    · rw [if_pos hxi]
      have := le_max_right l.depth r.depth
      calc (insert i (r.queriedOn x)).card
            ≤ (r.queriedOn x).card + 1 := Finset.card_insert_le _ _
        _ ≤ 1 + max l.depth r.depth := by omega
    · rw [if_neg hxi]
      have := le_max_left l.depth r.depth
      calc (insert i (l.queriedOn x)).card
            ≤ (l.queriedOn x).card + 1 := Finset.card_insert_le _ _
        _ ≤ 1 + max l.depth r.depth := by omega

/-- **The adversary.** A tree that correctly decides `∃ i, x i = true` must, on the all-false
input, query *every* position — otherwise flipping an unqueried position would change the answer
without changing the tree's path. -/
theorem queried_all_of_decides (t : DTree n Bool)
    (hcorrect : ∀ x, (t.eval x = true ↔ ∃ i, x i = true)) (i : Fin n) :
    i ∈ t.queriedOn (fun _ => false) := by
  by_contra hi
  set x0 : Fin n → Bool := fun _ => false with hx0
  set xi : Fin n → Bool := fun j => decide (j = i) with hxi
  have hagree : ∀ j ∈ t.queriedOn x0, x0 j = xi j := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hi hj
    simp only [hx0, hxi, decide_eq_false hji]
  have heval : t.eval x0 = t.eval xi := eval_eq_of_agree t hagree
  have hR : ∃ j, xi j = true := ⟨i, by rw [hxi]; simp⟩
  have hx0true : t.eval x0 = true := heval.trans ((hcorrect xi).mpr hR)
  obtain ⟨j, hj⟩ := (hcorrect x0).mp hx0true
  rw [hx0] at hj
  exact Bool.false_ne_true hj

/-- **FIND is hard (proved, not imported).** Any decision tree that correctly decides whether a
marked position exists makes at least `n` queries in the worst case. -/
theorem search_needs_n_queries (t : DTree n Bool)
    (hcorrect : ∀ x, (t.eval x = true ↔ ∃ i, x i = true)) : n ≤ t.depth := by
  have h2 : t.queriedOn (fun _ => false) = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (queried_all_of_decides t hcorrect)
  have h1 := card_queriedOn_le_depth t (fun _ => false)
  rwa [h2, Finset.card_univ, Fintype.card_fin] at h1

/-- The witness-checker for position `i`: read `x i` and report it. -/
def checkTree (i : Fin n) : DTree n Bool := .query i (.leaf false) (.leaf true)

/-- **CHECK is correct and costs one query.** -/
theorem checkTree_eval (i : Fin n) (x : Fin n → Bool) : (checkTree i).eval x = x i := by
  simp only [checkTree, DTree.eval]; cases x i <;> simp

theorem checkTree_depth (i : Fin n) : (checkTree i).depth = 1 := by
  simp [checkTree, DTree.depth]

/-- **The non-imported find/check gap.** For `n ≥ 2`: verifying a supplied witness costs one query,
while any correct existence-decider needs `≥ n` queries — so the checker is *strictly* cheaper than
any finder. Both bounds are machine-checked; nothing is imported. This is the find/check ledger's
first instance with a proved (not imported) `check ≪ find`. -/
theorem check_lt_find (hn : 2 ≤ n) (i : Fin n) (t : DTree n Bool)
    (hcorrect : ∀ x, (t.eval x = true ↔ ∃ i, x i = true)) :
    (checkTree i).depth < t.depth := by
  have := search_needs_n_queries t hcorrect
  rw [checkTree_depth]; omega

end Sundog.QueryGap
