/-
# TS-QE, TS-2d-3 (the descent's engine): branch-constant annotation + the DM measure.

Three layers, the last technical inputs before the elimination recursion assembles:

**A. The reading layer** — the annotation values as functions of COLUMN ENTRIES (data
constant on a branch). With the derived family laid out `base ++ base.map (emod · P)`:
- `column_reads_sample_sign`: a `zero` at base-position `i` of a point column forces the
  entry at position `base.length + i` to BE `P`'s sign at that sample (the TS-2b
  transfer, positionally). Same column entries ⇒ same sign value, at every `g` in the
  branch — this is "`sP` is branch-constant" in its exact formal content.
- `column_reads_gap_sign`: the derivative's gap sign is entry `0` of the gap column.

**B. The plan reader** — `readPlan σ' sa sb`: the gap/ray plan as a function of the
derivative's gap entry and the two flank reads (sample reads for interior flanks,
`BotSign`/`TopSign` tags for the two ends — branch data via resolved lead sign and
degree parity). Four validity bridges (`readPlan_valid_gap/left/right/line`) discharge
`GapValid`/`RayValid` for the read plan through the DiagramAnnotate lemmas; the
degenerate `σ' = 0` arm collapses to the constant case, with the end tag pinned by
`botSign_const`/`topSign_const`.

**C. The measure** — `famDegrees_derived_lt`: replacing `P` by its derivative and the
remainders strictly drops the Dershowitz–Manna measure (one-element removal, every
added degree below the removed one); `famDegrees_induction`: the well-founded
induction principle the elimination recursion runs on.

**Honest fence.** The recursion itself — composing the reads over a concrete branch
diagram, refining branches by `truncChain` live-lead and end-sign `SADef` conditions,
the drop-a-member projection, and `DiagramPartition` for every family — is the
remaining assembly.
-/
import Sundogcert.DiagramAnnotate

namespace Sundog.TarskiQE

open Polynomial

variable {n : ℕ}

/-! ### A. The reading layer -/

theorem signVec_getElem? (F : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (g : Fin n → ℝ) (y : ℝ) (i : ℕ) :
    (signVec F g y)[i]? = F[i]?.map fun Q => SignType.sign ((spec g Q).eval y) := by
  rw [signVec, List.getElem?_map]

theorem zero_entry_root {g : Fin n → ℝ} {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    {x : ℝ} {i : ℕ} {q : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hq : F[i]? = some q) (hz : (signVec F g x)[i]? = some 0) :
    (spec g q).eval x = 0 := by
  rw [signVec_getElem?, hq] at hz
  exact sign_eq_zero_iff.mp (Option.some_injective _ hz)

theorem layout_remainder_getElem? (base : List (Polynomial (MvPolynomial (Fin n) ℝ)))
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) {i : ℕ}
    {q : Polynomial (MvPolynomial (Fin n) ℝ)} (hq : base[i]? = some q) :
    (base ++ base.map fun r => emod r P)[base.length + i]? = some (emod q P) := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map, hq]
  rfl

/-- **The positional transfer.** A `zero` at base-position `i` of a column of the
derived family (layout `base ++ remainders`) forces the entry at the remainder
position `base.length + i` to be `P`'s sign at the sample. -/
theorem column_reads_sample_sign (g : Fin n → ℝ)
    {base : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) {x : ℝ} {i : ℕ}
    {q : Polynomial (MvPolynomial (Fin n) ℝ)}
    (hlive : ∀ q' ∈ base, MvPolynomial.eval g q'.leadingCoeff ≠ 0)
    (hq : base[i]? = some q)
    (hz : (signVec (base ++ base.map fun r => emod r P) g x)[i]? = some 0) :
    (signVec (base ++ base.map fun r => emod r P) g x)[base.length + i]?
      = some (SignType.sign ((spec g P).eval x)) := by
  obtain ⟨hib, hget⟩ := List.getElem?_eq_some_iff.mp hq
  have hqF : (base ++ base.map fun r => emod r P)[i]? = some q := by
    rw [List.getElem?_append_left hib, hq]
  have hq0 : (spec g q).eval x = 0 := zero_entry_root hqF hz
  have hqmem : q ∈ base := hget ▸ List.getElem_mem hib
  rw [signVec_getElem?, layout_remainder_getElem? base P hq]
  exact congrArg some (sign_transfer_signType g q P (hlive q hqmem) hq0).symm

/-- The derivative's gap sign is entry `0` of the gap column. -/
theorem column_reads_gap_sign (g : Fin n → ℝ)
    {F : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    {Pd : Polynomial (MvPolynomial (Fin n) ℝ)} (hPd : F[0]? = some Pd)
    {c : List SignType} {σ' : SignType} (hc : c[0]? = some σ')
    {y : ℝ} (hcol : signVec F g y = c) :
    SignType.sign ((spec g Pd).eval y) = σ' := by
  have h : (signVec F g y)[0]? = c[0]? := by rw [hcol]
  rw [signVec_getElem?, hPd, hc] at h
  exact Option.some_injective _ h

/-! ### B. The plan reader -/

/-- The plan, read from the derivative's gap entry and the two flank reads. -/
def readPlan : SignType → SignType → SignType → GapPlan
  | SignType.zero, sa, _ => GapPlan.flow sa
  | SignType.neg, sa, sb => gapPlanAnti sa sb
  | SignType.pos, sa, sb => gapPlanMono sa sb

private theorem botSign_const {g : Fin n → ℝ}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)} {k : ℝ} {ε : SignType}
    (hbot : BotSign g P ε) (hC : spec g P = Polynomial.C k) : ε = SignType.sign k := by
  match ε, hbot with
  | SignType.zero, h0 =>
    rw [h0] at hC
    rw [Polynomial.C_eq_zero.mp hC.symm]
    exact sign_zero.symm
  | SignType.pos, ⟨M, hM⟩ =>
    have h := hM (M - 1) (by linarith)
    rw [hC, Polynomial.eval_C] at h
    exact (sign_pos h).symm
  | SignType.neg, ⟨M, hM⟩ =>
    have h := hM (M - 1) (by linarith)
    rw [hC, Polynomial.eval_C] at h
    exact (sign_neg h).symm

private theorem topSign_const {g : Fin n → ℝ}
    {P : Polynomial (MvPolynomial (Fin n) ℝ)} {k : ℝ} {ε : SignType}
    (htop : TopSign g P ε) (hC : spec g P = Polynomial.C k) : ε = SignType.sign k := by
  match ε, htop with
  | SignType.zero, h0 =>
    rw [h0] at hC
    rw [Polynomial.C_eq_zero.mp hC.symm]
    exact sign_zero.symm
  | SignType.pos, ⟨M, hM⟩ =>
    have h := hM (M + 1) (by linarith)
    rw [hC, Polynomial.eval_C] at h
    exact (sign_pos h).symm
  | SignType.neg, ⟨M, hM⟩ =>
    have h := hM (M + 1) (by linarith)
    rw [hC, Polynomial.eval_C] at h
    exact (sign_neg h).symm

/-- **Bounded gap**: the read plan is valid, flanks = the sample reads. -/
theorem readPlan_valid_gap (g : Fin n → ℝ)
    (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (hd : spec g Pd = derivative (spec g P)) {a x : ℝ} (hax : a < x) {σ' : SignType}
    (hσ : ∀ y ∈ Set.Ioo a x, SignType.sign ((spec g Pd).eval y) = σ') :
    GapValid g P (some a) x
      (readPlan σ' (SignType.sign ((spec g P).eval a))
        (SignType.sign ((spec g P).eval x))) := by
  match σ' with
  | SignType.zero =>
    have h0 : spec g Pd = 0 :=
      spec_eq_zero_of_gap_roots g Pd hax fun y hy => sign_eq_zero_iff.mp (hσ y hy)
    rw [hd] at h0
    have hC := Polynomial.eq_C_of_derivative_eq_zero h0
    have hk : (spec g P).eval a = (spec g P).coeff 0 := by
      conv_lhs => rw [hC]
      rw [Polynomial.eval_C]
    change GapValid g P (some a) x (GapPlan.flow (SignType.sign ((spec g P).eval a)))
    rw [hk]
    exact gapValid_const g P hC
  | SignType.pos =>
    have hmono := strictMonoOn_of_derivative_pos (spec g P) fun z hz => by
      rw [← hd]
      exact sign_eq_one_iff.mp (hσ z hz)
    exact gapValid_incr g P hax hmono
  | SignType.neg =>
    have hanti := strictAntiOn_of_derivative_neg (spec g P) fun z hz => by
      rw [← hd]
      exact sign_eq_neg_one_iff.mp (hσ z hz)
    exact gapValid_anti g P hax hanti

/-- **Left ray**: the read plan is valid, left flank = the `BotSign` tag. -/
theorem readPlan_valid_left (g : Fin n → ℝ)
    (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (hd : spec g Pd = derivative (spec g P)) {x : ℝ} {σ' εm : SignType}
    (hσ : ∀ y ∈ Set.Iio x, SignType.sign ((spec g Pd).eval y) = σ')
    (hbot : BotSign g P εm) :
    GapValid g P none x (readPlan σ' εm (SignType.sign ((spec g P).eval x))) := by
  match σ' with
  | SignType.zero =>
    have h0 : spec g Pd = 0 :=
      spec_eq_zero_of_gap_roots g Pd (show x - 1 < x by linarith)
        fun y hy => sign_eq_zero_iff.mp (hσ y hy.2)
    rw [hd] at h0
    have hC := Polynomial.eq_C_of_derivative_eq_zero h0
    change GapValid g P none x (GapPlan.flow εm)
    rw [botSign_const hbot hC]
    exact gapValid_const g P hC
  | SignType.pos =>
    have hmono := strictMonoOn_Iic_of_derivative_pos (spec g P) fun z hz => by
      rw [← hd]
      exact sign_eq_one_iff.mp (hσ z hz)
    exact gapValid_left_incr g P hmono hbot
  | SignType.neg =>
    have hanti := strictAntiOn_Iic_of_derivative_neg (spec g P) fun z hz => by
      rw [← hd]
      exact sign_eq_neg_one_iff.mp (hσ z hz)
    exact gapValid_left_anti g P hanti hbot

/-- **Terminal ray**: the read plan is valid, right flank = the `TopSign` tag. -/
theorem readPlan_valid_right (g : Fin n → ℝ)
    (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (hd : spec g Pd = derivative (spec g P)) {a : ℝ} {σ' εp : SignType}
    (hσ : ∀ y ∈ Set.Ioi a, SignType.sign ((spec g Pd).eval y) = σ')
    (htop : TopSign g P εp) :
    RayValid g P (some a) (readPlan σ' (SignType.sign ((spec g P).eval a)) εp) := by
  match σ' with
  | SignType.zero =>
    have h0 : spec g Pd = 0 :=
      spec_eq_zero_of_gap_roots g Pd (show a < a + 1 by linarith)
        fun y hy => sign_eq_zero_iff.mp (hσ y hy.1)
    rw [hd] at h0
    have hC := Polynomial.eq_C_of_derivative_eq_zero h0
    have hk : (spec g P).eval a = (spec g P).coeff 0 := by
      conv_lhs => rw [hC]
      rw [Polynomial.eval_C]
    change RayValid g P (some a) (GapPlan.flow (SignType.sign ((spec g P).eval a)))
    rw [hk]
    exact rayValid_const g P hC
  | SignType.pos =>
    have hmono := strictMonoOn_Ici_of_derivative_pos (spec g P) fun z hz => by
      rw [← hd]
      exact sign_eq_one_iff.mp (hσ z hz)
    exact rayValid_right_incr g P hmono htop
  | SignType.neg =>
    have hanti := strictAntiOn_Ici_of_derivative_neg (spec g P) fun z hz => by
      rw [← hd]
      exact sign_eq_neg_one_iff.mp (hσ z hz)
    exact rayValid_right_anti g P hanti htop

/-- **The whole line**: the read plan is valid, both flanks are end tags. -/
theorem readPlan_valid_line (g : Fin n → ℝ)
    (P Pd : Polynomial (MvPolynomial (Fin n) ℝ))
    (hd : spec g Pd = derivative (spec g P)) {σ' εm εp : SignType}
    (hσ : ∀ y : ℝ, SignType.sign ((spec g Pd).eval y) = σ')
    (hbot : BotSign g P εm) (htop : TopSign g P εp) :
    RayValid g P none (readPlan σ' εm εp) := by
  match σ' with
  | SignType.zero =>
    have h0 : spec g Pd = 0 :=
      spec_eq_zero_of_gap_roots g Pd (show (0 : ℝ) < 1 by norm_num)
        fun y _ => sign_eq_zero_iff.mp (hσ y)
    rw [hd] at h0
    have hC := Polynomial.eq_C_of_derivative_eq_zero h0
    change RayValid g P none (GapPlan.flow εm)
    rw [botSign_const hbot hC]
    exact rayValid_const g P hC
  | SignType.pos =>
    have hmono := strictMono_of_derivative_pos (spec g P) fun z => by
      rw [← hd]
      exact sign_eq_one_iff.mp (hσ z)
    exact rayValid_line_incr g P hmono hbot htop
  | SignType.neg =>
    have hanti := strictAnti_of_derivative_neg (spec g P) fun z => by
      rw [← hd]
      exact sign_eq_neg_one_iff.mp (hσ z)
    exact rayValid_line_anti g P hanti hbot htop

/-! ### C. The Dershowitz–Manna measure -/

theorem famDegrees_cons (Q : Polynomial (MvPolynomial (Fin n) ℝ))
    (F : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    famDegrees (Q :: F) = Q.natDegree ::ₘ famDegrees F := by
  rw [famDegrees, famDegrees, List.map_cons]
  rfl

theorem famDegrees_append (F₁ F₂ : List (Polynomial (MvPolynomial (Fin n) ℝ))) :
    famDegrees (F₁ ++ F₂) = famDegrees F₁ + famDegrees F₂ := by
  rw [famDegrees, famDegrees, famDegrees, List.map_append]
  rfl

/-- **The descent step drops the measure.** Replacing `P` by its derivative and the
remainders (all of strictly smaller degree) is a Dershowitz–Manna decrease: one
element removed, every added element below it. -/
theorem famDegrees_derived_lt {P Pd : Polynomial (MvPolynomial (Fin n) ℝ)}
    {rest rems : List (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hPd : Pd.natDegree < P.natDegree)
    (hrems : ∀ r ∈ rems, r.natDegree < P.natDegree) :
    Multiset.IsDershowitzMannaLT (famDegrees (Pd :: (rest ++ rems)))
      (famDegrees (P :: rest)) := by
  refine ⟨famDegrees rest, Pd.natDegree ::ₘ famDegrees rems, {P.natDegree},
    ?_, ?_, ?_, ?_⟩
  · simp
  · rw [famDegrees_cons, famDegrees_append, ← Multiset.singleton_add,
      ← Multiset.singleton_add, add_left_comm]
  · rw [famDegrees_cons, ← Multiset.singleton_add, add_comm]
  · intro y hy
    refine ⟨P.natDegree, Multiset.mem_singleton_self _, ?_⟩
    rcases Multiset.mem_cons.mp hy with rfl | hy'
    · exact hPd
    · rw [famDegrees] at hy'
      obtain ⟨r, hr, hry⟩ := List.mem_map.mp (Multiset.mem_coe.mp hy')
      exact hry ▸ hrems r hr

/-- **The induction principle** the elimination recursion runs on. -/
theorem famDegrees_induction (motive : List (Polynomial (MvPolynomial (Fin n) ℝ)) → Prop)
    (step : ∀ F, (∀ F', Multiset.IsDershowitzMannaLT (famDegrees F') (famDegrees F) →
      motive F') → motive F) :
    ∀ F, motive F := by
  have hwf : WellFounded fun F F' : List (Polynomial (MvPolynomial (Fin n) ℝ)) =>
      Multiset.IsDershowitzMannaLT (famDegrees F) (famDegrees F') :=
    InvImage.wf famDegrees Multiset.wellFounded_isDershowitzMannaLT
  exact fun F => hwf.induction F step

end Sundog.TarskiQE
