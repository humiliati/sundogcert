/-
# SurfaceBag — the order-blind bag determines depth but not the stack-top (H2/σ-bridge anchor)

The chat-v2 R2 intersection slate (`sundog/docs/chatv2/R2_INTERSECTION_HYPOTHESES.md`, H5 the
σ-bridge) asks for the small formal statement behind the H2 empirical crossover
(`sundog/scripts/chatv2_h2_stacktop_probe.py`, 2026-07-01): over bracket strings, the pure
order-blind surface statistic — the **bag** (symbol-count vector) — reads the nesting DEPTH
perfectly, yet collapses on the STACK-TOP exactly at count-ambiguous positions. This module
machine-checks the label-structure half of that crossover:

* `bagSufficient_depth` — the bag IS a sufficient statistic for the depth of a valid prefix
  (depth + #closers = #openers): the DETERMINED pole (H2's control row, counts→depth = 1.000).
* `not_bagSufficient_stackTop` — the bag is NOT sufficient for the stack-top: the two valid
  prefixes `([` and `[(` have the SAME bag but different stack-tops: the RESIST pole.
* `bag_determines_depth_not_stackTop` — the crossover as one statement: the same order-blind
  statistic determines one label of a prefix and resists the other; the split is exactly
  whether the label needs ORDER.

`BagSufficient` is the `IsSufficient` idiom of `ParityNoSufficientStat` with the statistic =
the count vector (the "order-blind window" surface probe of the slate) — another grounded
determine/resist axis for the Order-Relative Resolution Law's schema.

## Fences (what this does NOT prove)

* Nothing about GPT-2 or any model. "The model computes the stack-top" is the EMPIRICAL half
  (the H2 probe receipt); this module proves only that the label is invisible to the
  order-blind statistic — the toy/combinatorial half, exactly as `ParityNoSufficientStat`
  proves the toy half and names Sarnak/Chowla as the imported wall.
* Only the bag (order-blind) case. The graded window form ("undecodable at n-gram order w ⟺
  σ > w") was the open hook — CLOSED 2026-07-01 by `SurfaceBagGraded.lean`
  (`stackTop_resists_every_window`: σ_surface(stackTop) = ∞, every window order).
-/
import Mathlib

namespace Sundog.SurfaceBag

/-- Opener species: parenthesis or square bracket. Two species are exactly enough for the
count-ambiguous witness. -/
inductive Opener
  | par
  | sq
  deriving DecidableEq

/-- A bracket symbol: an opener or a closer of a species. -/
inductive Br
  | op (o : Opener)
  | cl (o : Opener)
  deriving DecidableEq

/-- One step of the bracket machine on the stack of currently-open species; `none` =
invalid (a closer with no matching opener). -/
def step : Option (List Opener) → Br → Option (List Opener)
  | none, _ => none
  | some st, .op o => some (o :: st)
  | some [], .cl _ => none
  | some (a :: st), .cl o => if a = o then some st else none

/-- Run the machine over a string from a starting stack. -/
def evalFrom (st : List Opener) (s : List Br) : Option (List Opener) :=
  s.foldl step (some st)

/-- Run the machine from the empty stack. -/
def eval (s : List Br) : Option (List Opener) :=
  evalFrom [] s

/-- A valid prefix: every closer matched. -/
def Valid (s : List Br) : Prop :=
  (eval s).isSome = true

/-- Nesting depth of a valid prefix (junk 0 on invalid). -/
def depth (s : List Br) : ℕ :=
  ((eval s).getD []).length

/-- The stack-top: which species must close next (`none` at depth 0 or invalid). -/
def stackTop (s : List Br) : Option Opener :=
  ((eval s).getD []).head?

/-- The **bag** — the order-blind surface statistic: the symbol-count vector. -/
def bag (s : List Br) (b : Br) : ℕ :=
  s.count b

/-- Opener count — a function of the bag. -/
def opens (s : List Br) : ℕ :=
  bag s (.op .par) + bag s (.op .sq)

/-- Closer count — a function of the bag. -/
def closes (s : List Br) : ℕ :=
  bag s (.cl .par) + bag s (.cl .sq)

/-- The bag is a **sufficient statistic** for a label `f` if equal bags of valid prefixes
force equal labels — `ParityNoSufficientStat.IsSufficient` with the statistic = the count
vector (the order-blind surface probe). -/
def BagSufficient {α : Type*} (f : List Br → α) : Prop :=
  ∀ s t : List Br, Valid s → Valid t → bag s = bag t → f s = f t

/-! ## Count bookkeeping -/

theorem opens_cons_op (o : Opener) (s : List Br) : opens (.op o :: s) = opens s + 1 := by
  simp only [opens, bag]
  cases o
  · rw [List.count_cons_self, List.count_cons_of_ne (by decide)]
    omega
  · rw [List.count_cons_of_ne (by decide), List.count_cons_self]
    omega

theorem opens_cons_cl (o : Opener) (s : List Br) : opens (.cl o :: s) = opens s := by
  simp only [opens, bag]
  cases o <;>
    rw [List.count_cons_of_ne (by decide), List.count_cons_of_ne (by decide)]

theorem closes_cons_op (o : Opener) (s : List Br) : closes (.op o :: s) = closes s := by
  simp only [closes, bag]
  cases o <;>
    rw [List.count_cons_of_ne (by decide), List.count_cons_of_ne (by decide)]

theorem closes_cons_cl (o : Opener) (s : List Br) : closes (.cl o :: s) = closes s + 1 := by
  simp only [closes, bag]
  cases o
  · rw [List.count_cons_self, List.count_cons_of_ne (by decide)]
    omega
  · rw [List.count_cons_of_ne (by decide), List.count_cons_self]
    omega

/-- The machine never recovers from an invalid state. -/
theorem foldl_step_none : ∀ s : List Br, s.foldl step none = none := by
  intro s
  induction s with
  | nil => rfl
  | cons b s ih =>
    rw [List.foldl_cons, show step none b = none from rfl]
    exact ih

/-- **The stack invariant.** A valid run's final stack size plus the closers consumed equals
the starting size plus the openers consumed: `|st'| + #closes = |st| + #opens`. -/
theorem evalFrom_length :
    ∀ (s : List Br) (st st' : List Opener),
      evalFrom st s = some st' → st'.length + closes s = st.length + opens s := by
  intro s
  induction s with
  | nil =>
    intro st st' h
    obtain rfl : st = st' := by simpa [evalFrom] using h
    simp [opens, closes, bag]
  | cons b s ih =>
    intro st st' h
    cases b with
    | op o =>
      have h' : evalFrom (o :: st) s = some st' := by
        simpa [evalFrom, List.foldl_cons, step] using h
      have hIH := ih (o :: st) st' h'
      rw [opens_cons_op, closes_cons_op]
      simp only [List.length_cons] at hIH
      omega
    | cl o =>
      cases st with
      | nil =>
        simp [evalFrom, List.foldl_cons, step, foldl_step_none] at h
      | cons a rest =>
        by_cases hao : a = o
        · subst hao
          have h' : evalFrom rest s = some st' := by
            simpa [evalFrom, List.foldl_cons, step] using h
          have hIH := ih rest st' h'
          rw [opens_cons_cl, closes_cons_cl]
          simp only [List.length_cons]
          omega
        · simp [evalFrom, List.foldl_cons, step, hao, foldl_step_none] at h

/-! ## The crossover -/

/-- **The bag DETERMINES depth.** For valid prefixes, `depth + #closers = #openers`, so
equal count vectors force equal depths: nesting depth is order-blind readable — the H2
control row (counts→depth = 1.000). The determined pole. -/
theorem bagSufficient_depth : BagSufficient depth := by
  intro s t hs ht hbag
  have hs' : (eval s).isSome = true := hs
  have ht' : (eval t).isSome = true := ht
  obtain ⟨sts, hsts⟩ := Option.isSome_iff_exists.mp hs'
  obtain ⟨stt, hstt⟩ := Option.isSome_iff_exists.mp ht'
  have h1 := evalFrom_length s [] sts hsts
  have h2 := evalFrom_length t [] stt hstt
  have ho : opens s = opens t := by simp only [opens, hbag]
  have hc : closes s = closes t := by simp only [closes, hbag]
  simp only [List.length_nil] at h1 h2
  simp only [depth, hsts, hstt, Option.getD_some]
  omega

/-- **The bag does NOT determine the stack-top.** The two valid prefixes `([` and `[(` have
the SAME bag (one opener of each species) but different stack-tops — the top is decided by
ORDER, which the bag erases. The resist pole; the count-ambiguous witness of the H2 probe. -/
theorem not_bagSufficient_stackTop : ¬ BagSufficient stackTop := by
  intro h
  have hb : bag [Br.op .par, Br.op .sq] = bag [Br.op .sq, Br.op .par] := by
    funext b
    cases b with
    | op o => cases o <;> decide
    | cl o => cases o <;> decide
  have hcontra :=
    h [Br.op .par, Br.op .sq] [Br.op .sq, Br.op .par]
      (by unfold Valid; decide) (by unfold Valid; decide) hb
  exact absurd hcontra (by decide)

/-- **The machine-checked crossover** — the H2 signature as one statement: the SAME
order-blind bag statistic determines the DEPTH of a valid prefix and fails to determine its
STACK-TOP. One string, one statistic, a determine/resist split decided exactly by whether
the label needs order — the label-structure half of "surface-undecodable ∧ model-computed =
a high-σ state". -/
theorem bag_determines_depth_not_stackTop :
    BagSufficient depth ∧ ¬ BagSufficient stackTop :=
  ⟨bagSufficient_depth, not_bagSufficient_stackTop⟩

end Sundog.SurfaceBag
