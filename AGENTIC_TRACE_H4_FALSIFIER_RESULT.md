# H-IV FALSIFIER — the budget receipt bounds count-by-score, not the structural boundary

**Frozen:** 2026-06-28, repo HEAD `master`.
**Status:** **FALSIFIER FIRES → FIX LANDED (§7) → LEAN CORE LANDED (§8).** H-IV's own
pre-registered falsifier (both forms: the structural bound cuts off the only successful
branch, AND branch explosion despite every emitted trace satisfying the budget) is
satisfied by runnable, receipt-checkable counterexamples against the live
`scripts/branch_budget_receipt.py`; the re-specified line-free (cap-set) slot receipt in
§7 closes both legs; the §8 Lean module pins the trace-bound core, axiom-clean. A fired
falsifier is a banked SUCCESS: caught before any cap-set / structural claim, it localized
the exact re-spec — and the re-spec, and its deductive core, are done. **This brings H-IV
level with H-II/H-III (falsifier → fix → Lean core).**
**Lane:** sundogcert agentic-trace slate, Hypothesis IV (Trace-Bounded Search Trees). This
completes the four-hypothesis slate — every hypothesis now has a fired falsifier.

---

## §1 The instrument and its claim

`branch_budget_receipt.budget_search_branches` orders candidate branches by **score**
(desc) and admits the top `budget` into slots, refusing the overflow:

- `accept` — every candidate fits the budget (`branch-budget-satisfied`);
- `structural-zero` — overflow branches refused (`branch-budget-exhausted`);
- `quarantine` — malformed (duplicate branch ids).

H-IV's hook: *a recursive search tree should stop at a published **structural** boundary,
not an opaque token budget*, and this receipt is offered as that structural cap (the
runtime companion of `AgenticTrace`'s `branch_count_le_budget`).

## §2 The defect — a count-by-score cap is the opaque budget in structural clothing

The receipt bounds the **per-node admitted COUNT, ranked by score**. That is neither of
the two things the hook actually needs:

- it is not the **solution-bearing structural predicate** — score ranking is not solution
  membership, so the cap can prune the winner (Leg A);
- it is not the **total tree complexity** — a per-node breadth cap composes to
  `budget**depth` over depth, so per-node acceptance does not bound the search (Leg B).

A count cap is exactly the "opaque token budget" the hook warned against, relabelled
structural.

## §3 The two legs (both fire against the live receipt)

| leg | construction | receipt says | truth |
|---|---|---|---|
| **A — the bound cuts the only winner** (false negative) | 3 high-score distractors + 1 **low-score WINNER** (the only solution-bearing branch); `budget = 2` | **`structural-zero`** refusing overflow `{distractor2, WINNER}` | the **WINNER is pruned**; the smallest budget that keeps it is **4 = all branches** (no bound at all) |
| **B — explosion despite acceptance** (false positive) | each node emits exactly `budget = 3` branches; depth `8` | **`accept`** at **every** node (`branch-budget-satisfied`) | the tree has **9840 ≥ 3⁸ = 6561** nodes — the per-node cap does not bound the search |

**Control (detector not trivially broken):** 5 candidates with `budget = 2` →
**`structural-zero`** refusing 3 overflow. The receipt *does* bound per-node breadth — it
just bounds the wrong thing for the claimed purpose. `falsifier_fires = True ∧
control_holds = True`.

## §4 Why this is a mis-specification, not a tunable budget

No setting of `budget` recovers the missing structure. In Leg A the only budget that keeps
the winner is the one that admits everything, so the cap cannot simultaneously prune and
retain the solution — it is blind to *which* branch solves. In Leg B every budget `b ≥`
branching factor accepts at every node while the tree grows as `b**depth`; raising `budget`
makes the explosion *faster*, not bounded. The cap is a functional of the per-node count
ranked by score; the solution location and the total complexity are orthogonal to it.

## §5 The fix direction (the re-spec, not yet built)

Mirroring H-I (bind the decisive indices), H-II (re-spec around the fold count), and H-III
(key on the gradient/hierarchy component): a faithful trace bound must be a **structural
predicate aligned with solutions and composing over depth** — the slate's own
"coordinate-slot / line-free (cap-set) trace predicate," not a score-ranked count. Admit a
branch iff it occupies a *certified structural slot* (a polynomial-degree / cap-set
coordinate witness), and bound the *total* by the structural capacity, so (A) a
solution-bearing branch is never refused for lacking score and (B) the depth-composed
count is bounded by the structural invariant, not `budget**depth`. The Lean surface exists
(`branch_count_le_budget` for the finite-injection core); the cap-set version needs the
explicit `F₃ⁿ` projection and a line-free predicate (the named import). Promotion requires
that re-spec before any structural/cap-set claim.

## §6 Scope / honesty

- This is a **runtime** falsifier on the receipt's measurement (count-by-score vs
  structure), not a claim about cap-set combinatorics (Ellenberg–Gijswijt is correct) or
  about any real agent search (the branch→cap-set map remains the unbuilt imported wall —
  the falsifier shows the receipt mis-bounds even synthetic search, so the wall cannot yet
  be tested faithfully).
- The legs are deterministic, receipt-verifiable (`verify_branch_budget_receipt`), and
  frozen as a test (`scripts/test_h4_branch_budget_falsifier.py`, 4 cases). The control
  discriminates genuine breadth overflow, so the instrument is live.

Artifacts: `scripts/h4_branch_budget_falsifier.py`,
`scripts/test_h4_branch_budget_falsifier.py`.

## §7 FIX LANDED — the structural line-free (cap-set) slot receipt (2026-06-28)

`scripts/structural_slot_receipt.py` admits on a STRUCTURAL predicate instead of score.
Each branch carries a coordinate in `F₃ⁿ`; a branch is admitted iff its coordinate keeps
the admitted set **line-free** (a cap: no three distinct admitted points `a,b,c` with
`a+b+c ≡ 0 mod 3`, the collinearity condition in AG(n,3)). Admission **never** depends on
score, and the admitted set is bounded by the **cap-set capacity** of the space (the
Ellenberg–Gijswijt structural bound), independent of how many candidates are offered.

Outcomes: `accept` (every candidate occupies a certified line-free slot — the candidate set
is a cap), `structural-zero` (a branch is refused because admitting it would form a line —
the genuine published boundary), `quarantine` (coordinate not in `F₃ⁿ`, duplicate
coordinate, duplicate id). `verify_structural_receipt` re-checks the admitted set is a
genuine cap and the verdict matches the refusal set.

**It closes both falsifier legs** (`scripts/test_structural_slot_receipt.py`, each leg run
against the old count cap and the fix):

| leg | old `branch_budget_receipt` (count-by-score) | new `structural_slot_receipt` (line-free) |
|---|---|---|
| A — low-score WINNER, coord completes a cap | refused (overflow; pruned for low score) | **admitted** (`accept`) — kept on **structure**, not score |
| B — all 9 points of `F₃²`, budget 100 | `accept`s **all 9** (count cap bounds nothing) | **`structural-zero`**: admits a cap of **≤ 4** (`CAP_CAPACITY[2]`), refuses 5 — bounded by **capacity, not count** |

```
cap       verdict=accept           admitted=4 refused=0  is_cap=True   (a known 4-point cap)
overflow  verdict=structural-zero  admitted=4 refused=5  is_cap=True   (all 9 -> bounded to capacity)
```

The structural bound is **global and depth-independent**: feeding the tree's `budget**depth`
branches maps them into the shared coordinate space, of which only a cap (≤ capacity) is
admitted — so the explosion of Leg B cannot occur, and the low-score winner of Leg A is
never refused for its score.

**What it does not claim** (the named wall, unchanged): it is a faithful receipt over a
*declared* branch→coordinate map; it does **not** justify mapping real agent branches into
`F₃ⁿ` cap-set geometry, nor does it prove the Ellenberg–Gijswijt bound (it *uses* the cap
structure; the capacity table is cited). The deductive surface for a Lean quarantine
theorem is `AgenticTrace.branch_count_le_budget` (the finite-injection core) plus a
line-free predicate — the natural next step, mirroring H-II's `ContextDecay` and H-III's
`HierarchyHolonomy` cores. 16 tests pass (8 fix + 4 falsifier + 4 existing).

## §8 LEAN CORE — what the structural slot receipt licenses (2026-06-28)

`Sundogcert/StructuralSlot.lean` pins the deductive content of the fix, the way
`ContextDecay` (H-II) and `HierarchyHolonomy` (H-III) pinned theirs. A line (3-term AP) is
`IsLine a b c := a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c = 0` over an `AddCommGroup`; `LineFree S`
is a cap (no line); `FormsLine S c` is the refusal condition. Four theorems, enforced by
`#guard_msgs` in `AxiomAudit.lean`; full `lake build` green (3547 jobs).

| theorem | content | axioms | H-I/II/III analog |
|---|---|---|---|
| `refusal_earned` | a refused candidate exhibits a concrete line (two collinear admitted points) | `[propext, Quot.sound]` | `decay_earned` / `hijack_witness` |
| `admit_preserves_lineFree` | if `S` is a cap and `c` forms no line, `insert c S` is still a cap — the fix's core correctness | `[propext, Quot.sound]` | the rule-soundness lemmas |
| `lineFree_card_le_univ` | an admitted cap is bounded by the ambient space, **independent of how many candidates produced it** (depth-independent; EG capacity is the named sharpening) | `[propext, Quot.sound]` | — (Leg B) |
| `count_cannot_determine_structure` | **headline:** two sets of *equal cardinality*, one a cap and one a line — a count budget cannot tell line-free from line | triple | `no_word_function_determines_decisive` / `hierarchy_separates_what_loop_cannot` |

The headline is the formal blind spot: `count_cannot_determine_structure` exhibits concrete
witnesses in `F₃²` — `{(0,0),(1,0),(0,1)}` (a cap) and `{(0,0),(1,0),(2,0)}` (a line) — of
**equal cardinality**, so a cardinality/count budget is provably blind to line-freeness,
exactly as the falsifier's Leg A showed the count-by-score cap blind to which branch solves.
`refusal_earned`, `admit_preserves_lineFree`, and `lineFree_card_le_univ` are axiom-free of
`Classical.choice` (`[propext, Quot.sound]`); the decidable `F₃²` headline carries the full
triple. No `sorryAx`, no `native_decide`.

**What the Lean does not claim** (the named wall, unchanged): it formalizes what the
structural receipt licenses on a declared coordinate set; it does not justify mapping real
agent branches into `F₃ⁿ`, nor reprove the Ellenberg–Gijswijt cap-capacity bound. Those
remain imports by design.
