/-
# SurfaceBagGraded -- the stack-top resists EVERY window (OR-6)

Closes the hook `SurfaceBag.lean` and the sigma-slate addendum left open: the
graded window form.  `SurfaceBag` proved the bag (w = 1) cannot determine the
stack-top; this module proves **no window order w can**:

> `stackTop_resists_every_window : forall w, not (WindowSufficient w stackTop)`

`WindowSufficient w f` is the graded `BagSufficient`: equal counts of every
contiguous substring of length <= w (the w-gram count vector) on valid prefixes
force equal labels.  So sigma_surface(stackTop) = infinity: the conjectured
value, now machine-checked.

**The witness family.**  For each w, with `P` a balanced run of `w+1`
parenthesis pairs (length `L = 2w+2`):

    s_w = P ( P [ P        t_w = P [ P ( P

(as opener species: `x = op par`, `y = op sq`, swapped between the two).  Both
are valid; the stack-tops differ (`sq` vs `par`).  The two strings differ by
swapping two single symbols sitting in IDENTICAL length-`L` contexts, and the
gap between the swap positions (`L+1 > w`) exceeds every window, so no window
can see both.  The k-gram count vectors agree for every `k <= w`: the
involution `sigma` that shifts window positions across the two swap sites by
`L+1` matches windows of `s_w` to equal windows of `t_w` (`window_swap`), and
`Finset.card_bij'` transports the counts (`wcount_eq`).

Fences: same as `SurfaceBag` -- nothing about any model; this is the
label-structure half only.  The witness pair is one family; the claim is
existence of indistinguishable pairs at every order, i.e. non-sufficiency of
every finite window statistic -- exactly sigma_surface = infinity in the
addendum's sense.
-/
import Sundogcert.SurfaceBag

namespace Sundog.SurfaceBag.Graded

open Sundog.SurfaceBag

/-! ## Windows and the graded statistic -/

/-- The window of length `k` at position `i`. -/
def windowAt (l : List Br) (k i : ℕ) : List Br :=
  (l.drop i).take k

/-- Positions where `g` occurs as a contiguous substring. -/
def matchSet (l g : List Br) : Finset ℕ :=
  (Finset.range (l.length + 1)).filter (fun i => windowAt l g.length i = g)

/-- The `w`-gram count statistic: occurrences of `g` in `l`. -/
def wcount (l g : List Br) : ℕ :=
  (matchSet l g).card

/-- The graded sufficiency idiom: the length-≤-`w` substring count vector on
valid prefixes forces the label — `BagSufficient` at window order `w`. -/
def WindowSufficient (w : ℕ) {γ : Type*} (f : List Br → γ) : Prop :=
  ∀ s t : List Br, Valid s → Valid t →
    (∀ g : List Br, g.length ≤ w → wcount s g = wcount t g) → f s = f t

/-! ## The balanced context block -/

/-- `n` parenthesis pairs `()()...()`. -/
def pairsList : ℕ → List Br
  | 0 => []
  | n + 1 => .op .par :: .cl .par :: pairsList n

theorem length_pairsList (n : ℕ) : (pairsList n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairsList, ih]; omega

/-- The block's characters: alternating open/close parenthesis. -/
theorem pairsList_getElem (n i : ℕ) (h : i < (pairsList n).length) :
    (pairsList n)[i] = if i % 2 = 0 then Br.op .par else Br.cl .par := by
  induction n generalizing i with
  | zero => simp [pairsList] at h
  | succ n ih =>
    match i with
    | 0 => rfl
    | 1 => rfl
    | (j + 2) =>
      have hj : j < (pairsList n).length := by
        simp [pairsList] at h; omega
      have := ih j hj
      simp only [pairsList, List.getElem_cons_succ]
      rw [this]
      have : (j + 2) % 2 = j % 2 := by omega
      rw [this]

/-- The machine passes a balanced block leaving any stack unchanged. -/
theorem evalFrom_pairsList (n : ℕ) (st : List Opener) :
    evalFrom st (pairsList n) = some st := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    show (pairsList (n+1)).foldl step (some st) = some st
    simp only [pairsList, List.foldl_cons]
    have h1 : step (some st) (.op .par) = some (.par :: st) := rfl
    have h2 : step (some (.par :: st)) (.cl .par) = some st := by
      simp [step]
    rw [h1, h2]
    exact ih st

/-! ## The witness pair -/

variable (w : ℕ)

/-- The witness string with first swap symbol `x`, second `y`:
`P ++ x :: P ++ y :: P` with `P` = `w+1` pairs (`L = 2w+2`). -/
def wit (x y : Br) : List Br :=
  pairsList (w + 1) ++ x :: (pairsList (w + 1) ++ y :: pairsList (w + 1))

theorem length_wit (x y : Br) : (wit w x y).length = 6 * w + 8 := by
  simp [wit, length_pairsList]
  omega

/-- The character function the witness realizes. -/
def mkChar (x y : Br) (m : ℕ) : Br :=
  if m < 2 * w + 2 then (if m % 2 = 0 then Br.op .par else Br.cl .par)
  else if m = 2 * w + 2 then x
  else if m < 4 * w + 5 then (if (m - (2 * w + 3)) % 2 = 0 then Br.op .par else Br.cl .par)
  else if m = 4 * w + 5 then y
  else (if (m - (4 * w + 6)) % 2 = 0 then Br.op .par else Br.cl .par)

theorem pairsList_getElem? (n i : ℕ) (h : i < 2 * n) :
    (pairsList n)[i]? = some (if i % 2 = 0 then Br.op .par else Br.cl .par) := by
  have hl : i < (pairsList n).length := by rw [length_pairsList]; exact h
  rw [List.getElem?_eq_getElem hl, pairsList_getElem n i hl]

theorem wit_getElem? (x y : Br) (m : ℕ) (h : m < 6 * w + 8) :
    (wit w x y)[m]? = some (mkChar w x y m) := by
  have hP : (pairsList (w + 1)).length = 2 * w + 2 := by
    rw [length_pairsList]; omega
  unfold wit mkChar
  by_cases h1 : m < 2 * w + 2
  · rw [List.getElem?_append_left (by omega)]
    rw [pairsList_getElem? _ _ (by omega)]
    simp [h1]
  · rw [List.getElem?_append_right (by omega), hP]
    by_cases h2 : m = 2 * w + 2
    · rw [show m - (2 * w + 2) = 0 from by omega, List.getElem?_cons_zero]
      simp [h1, h2]
    · rw [show m - (2 * w + 2) = (m - (2 * w + 3)) + 1 from by omega,
        List.getElem?_cons_succ]
      by_cases h3 : m < 4 * w + 5
      · rw [List.getElem?_append_left (by omega)]
        rw [pairsList_getElem? _ _ (by omega)]
        simp [h1, h2, h3]
      · rw [List.getElem?_append_right (by omega), hP]
        by_cases h4 : m = 4 * w + 5
        · rw [show m - (2 * w + 3) - (2 * w + 2) = 0 from by omega,
            List.getElem?_cons_zero]
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
        · rw [show m - (2 * w + 3) - (2 * w + 2) = (m - (4 * w + 6)) + 1 from by omega,
            List.getElem?_cons_succ]
          rw [pairsList_getElem? _ _ (by omega)]
          simp [h1, h2, h3, h4]

theorem wit_getElem (x y : Br) (m : ℕ) (h : m < 6 * w + 8)
    (h' : m < (wit w x y).length) :
    (wit w x y)[m]'h' = mkChar w x y m := by
  have h1 := wit_getElem? w x y m h
  rw [List.getElem?_eq_getElem h'] at h1
  exact Option.some_inj.mp h1

/-- **The shift lemma (the heart).**  Below the second swap position, the
character at `m` in `wit x y` equals the character at `m + (L+1)` in
`wit y x`: the two swap sites sit in identical contexts one period apart. -/
theorem mkChar_shift (x y : Br) (m : ℕ) (hm : m < 4 * w + 5) :
    mkChar w x y m = mkChar w y x (m + (2 * w + 3)) := by
  unfold mkChar
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- Off the two swap positions the witnesses agree. -/
theorem mkChar_offdiag (x y : Br) (m : ℕ) (h1 : m ≠ 2 * w + 2) (h2 : m ≠ 4 * w + 5) :
    mkChar w x y m = mkChar w y x m := by
  unfold mkChar
  split_ifs <;> first | rfl | omega

/-! ## The position involution and the window swap -/

/-- The involution on window positions: windows touching one swap site map to
the corresponding windows at the other; everything else is fixed. -/
def sigma (k i : ℕ) : ℕ :=
  if i ≤ 2 * w + 2 ∧ 2 * w + 3 ≤ i + k then i + (2 * w + 3)
  else if i ≤ 4 * w + 5 ∧ 4 * w + 6 ≤ i + k then i - (2 * w + 3)
  else i

theorem sigma_invol (k i : ℕ) (hk : k ≤ w) : sigma w k (sigma w k i) = i := by
  simp only [sigma]
  split_ifs <;> omega

/-- Window characters transport across the involution. -/
theorem mkChar_sigma (x y : Br) (k i j : ℕ) (hk : k ≤ w) (hj : j < k) :
    mkChar w x y (i + j) = mkChar w y x (sigma w k i + j) := by
  unfold sigma
  split_ifs with h1 h2
  · rw [mkChar_shift w x y (i + j) (by omega)]
    congr 1
    omega
  · have h := mkChar_shift w y x (i - (2 * w + 3) + j) (by omega)
    rw [show i - (2 * w + 3) + j + (2 * w + 3) = i + j from by omega] at h
    exact h.symm
  · exact mkChar_offdiag w x y (i + j) (by omega) (by omega)

/-- **The window swap.**  Every window of `wit x y` equals the corresponding
window of `wit y x` at the involuted position. -/
theorem window_swap (x y : Br) (k i : ℕ) (hk : k ≤ w) :
    windowAt (wit w x y) k i = windowAt (wit w y x) k (sigma w k i) := by
  have hlen : ∀ (u v : Br) (i' : ℕ),
      (windowAt (wit w u v) k i').length = min k (6 * w + 8 - i') := by
    intro u v i'
    simp [windowAt, length_wit]
  apply List.ext_getElem
  · rw [hlen, hlen]
    simp only [sigma]
    split_ifs <;> omega
  · intro j hj1 hj2
    rw [hlen] at hj1
    have hjk : j < k := by omega
    have hin : i + j < 6 * w + 8 := by omega
    have hin' : sigma w k i + j < 6 * w + 8 := by
      simp only [sigma]; split_ifs <;> omega
    simp only [windowAt]
    rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
    rw [wit_getElem w x y (i + j) hin (by rw [length_wit]; exact hin),
      wit_getElem w y x (sigma w k i + j) hin' (by rw [length_wit]; exact hin')]
    exact mkChar_sigma w x y k i j hk hjk

/-- **Equal `k`-gram counts for every `k ≤ w`.**  The involution is a bijection
between the match sets, so every substring of length ≤ `w` occurs equally often
in the two witnesses. -/
theorem wcount_eq (x y : Br) (g : List Br) (hg : g.length ≤ w) :
    wcount (wit w x y) g = wcount (wit w y x) g := by
  have hmem : ∀ (u v : Br) (i : ℕ), i ∈ matchSet (wit w u v) g →
      sigma w g.length i ∈ matchSet (wit w v u) g := by
    intro u v i hi
    simp only [matchSet, Finset.mem_filter, Finset.mem_range, length_wit] at hi ⊢
    refine ⟨?_, ?_⟩
    · simp only [sigma]; split_ifs <;> omega
    · rw [← window_swap w u v g.length i hg]
      exact hi.2
  exact Finset.card_bij' (fun i _ => sigma w g.length i) (fun i _ => sigma w g.length i)
    (fun i hi => hmem x y i hi) (fun i hi => hmem y x i hi)
    (fun i _ => sigma_invol w g.length i hg) (fun i _ => sigma_invol w g.length i hg)

/-! ## Validity and the stack-tops -/

theorem eval_wit (ox oy : Opener) :
    eval (wit w (.op ox) (.op oy)) = some [oy, ox] := by
  show ((pairsList (w+1) ++ .op ox :: (pairsList (w+1) ++ .op oy :: pairsList (w+1))).foldl
    step (some [])) = some [oy, ox]
  rw [List.foldl_append]
  rw [show (pairsList (w+1)).foldl step (some []) = some [] from evalFrom_pairsList (w+1) []]
  rw [List.foldl_cons]
  rw [show step (some []) (.op ox) = some [ox] from rfl]
  rw [List.foldl_append]
  rw [show (pairsList (w+1)).foldl step (some [ox]) = some [ox] from
    evalFrom_pairsList (w+1) [ox]]
  rw [List.foldl_cons]
  rw [show step (some [ox]) (.op oy) = some [oy, ox] from rfl]
  exact evalFrom_pairsList (w+1) [oy, ox]

theorem valid_wit (ox oy : Opener) : Valid (wit w (.op ox) (.op oy)) := by
  unfold Valid
  rw [eval_wit]
  rfl

theorem stackTop_wit (ox oy : Opener) :
    stackTop (wit w (.op ox) (.op oy)) = some oy := by
  unfold stackTop
  rw [eval_wit]
  rfl

/-! ## The headline -/

/--
**The stack-top resists EVERY window: `σ_surface(stackTop) = ∞`.**  For every
window order `w` there are valid prefixes with identical substring-count
vectors up to length `w` and different stack-tops — no finite-window surface
statistic is sufficient for the stack-top.  The conjectured value of the
σ-slate addendum, machine-checked.
-/
theorem stackTop_resists_every_window (w : ℕ) :
    ¬ WindowSufficient w stackTop := by
  intro h
  have hcontra :=
    h (wit w (.op .par) (.op .sq)) (wit w (.op .sq) (.op .par))
      (valid_wit w .par .sq) (valid_wit w .sq .par)
      (fun g hg => wcount_eq w (.op .par) (.op .sq) g hg)
  rw [stackTop_wit, stackTop_wit] at hcontra
  exact absurd hcontra (by simp)

/-! ## Local axiom audit -/

/-- info: 'Sundog.SurfaceBag.Graded.window_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms window_swap

/-- info: 'Sundog.SurfaceBag.Graded.wcount_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wcount_eq

/-- info: 'Sundog.SurfaceBag.Graded.stackTop_resists_every_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stackTop_resists_every_window

end Sundog.SurfaceBag.Graded
