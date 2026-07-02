/-
# PercivalKeyedMargin -- the keyed-composition MARGIN law (OR-1)

Machine-checks the ORDERRELATIVE lane's OR-1 claim over the S3 multi-agent
aggregation skeleton (Percival S3, `S3_SHARED_COURT_UNREACHABLE_CAP_COMPOSES`):
guarantees compose according to the variable they are KEYED on.

**Behavior-keyed (the cap):** per-agent bounds on owned outgoing deviations.
* `cap_bound_additive` -- the composed bound is the SUM of per-agent bounds
  (soundness: |sum of deviations| <= sum of caps).
* `cap_bound_tight` -- the sum bound is achieved, so the composed bound is
  EXACTLY additive: each agent's marginal is exactly its own cap.
* `cap_marginal_profile_independent` -- one agent's marginal effect on the
  aggregate is x - y regardless of the co-agent profile: no interaction terms,
  the degradation is LINEAR.

**Outcome-keyed (the court):** the guarantee's value is a threshold readout of
the shared aggregate (honored iff total courting < M * cstar).
* `pivotal_threshold` / `coalition_flips` -- the division-free S3 pivotality
  algebra: one purifier is non-pivotal iff cγ <= M*(cγ - cstar) (S3.1's
  M* = ceil(cγ/(cγ-cstar))), and a coalition with k*cγ > M*(cγ - cstar) flips
  the court (S3.2's f* = 1 - cstar/cγ).
* `court_not_product` -- the 2-agent anchor: the satisfaction region is not a
  product of per-agent regions (bare non-composability, the near-definitional
  half).
* `court_value_not_additive` -- **the margin-recoding falsifier, refuted**: for
  NO per-agent recoding g : Q -> Q and affine offset beta is the court's value
  beta + Sum g(c_m) over profiles -- three profiles (all-courting, one
  purifier, all-pure) pigeonhole any candidate into 0 = 1.
* `keyed_margin_law` -- the packaged contrast at shared parameters: the cap
  bound is exactly additive AND the court value is additive in no recoding.

Readout-locus note (mark 3, feeds OR-2): the court's PRE-readout aggregate
(the sum) is itself additive -- `court_value_not_additive` shows the cliff
enters at the threshold READOUT, which is exactly where OR-2's idempotent
(Boolean/max) algebra takes over from the cancellative (Q, +) one.

Scope, honest: 1-D deviations/courting levels over Q; the threshold court in
sum form (mean * M); the aggregation SKELETON that S3.4/S3.5 measured
(caps linear 0/2583, court threshold f* ~ 0.286), not the court dynamics R(c);
margins-as-values, no training loop.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Sundogcert.Percival

/-! ## Behavior-keyed: the cap side -/

/--
**The composed cap bound is the sum of per-agent bounds (soundness).**  If every
agent's deviation is within its own cap, the aggregate deviation is within the
SUM of the caps -- at every co-agent profile.
-/
theorem cap_bound_additive : ∀ {ds ks : List ℚ},
    List.Forall₂ (fun d k => |d| ≤ k) ds ks → |ds.sum| ≤ ks.sum := by
  intro ds ks h
  induction h with
  | nil => simp
  | cons hdk _ ih =>
    simp only [List.sum_cons]
    have h1 := abs_le.mp hdk
    have h2 := abs_le.mp ih
    exact abs_le.mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

/--
**The sum bound is achieved (tightness).**  There is a profile (every agent at
its own cap) meeting every per-agent bound whose aggregate deviation equals the
sum of caps -- so the composed bound is EXACTLY additive: each agent's marginal
contribution to the composed guarantee is exactly its own cap.
-/
theorem cap_bound_tight (ks : List ℚ) (hk : ∀ k ∈ ks, 0 ≤ k) :
    ∃ ds : List ℚ, List.Forall₂ (fun d k => |d| ≤ k) ds ks ∧ |ds.sum| = ks.sum := by
  refine ⟨ks, List.forall₂_same.mpr (fun k hkm => le_of_eq (abs_of_nonneg (hk k hkm))), ?_⟩
  exact abs_of_nonneg (List.sum_nonneg hk)

/--
**Profile-independent marginal (linearity / no interaction).**  Replacing one
agent's deviation `y` by `x` moves the aggregate by exactly `x - y`, whatever
the co-agent profile is: the cap side's degradation is linear, with the same
slope at every profile.
-/
theorem cap_marginal_profile_independent (pre post : List ℚ) (x y : ℚ) :
    (pre ++ x :: post).sum - (pre ++ y :: post).sum = x - y := by
  simp only [List.sum_append, List.sum_cons]
  ring

/-! ## Outcome-keyed: the court side -/

/-- The court's value: honored (1) iff the aggregate courting level is below
the threshold, in sum form (`p.sum < M * cstar` is `mean < cstar`). -/
def courtValue (M : ℕ) (cstar : ℚ) (p : List ℚ) : ℚ :=
  if p.sum < M * cstar then 1 else 0

/--
**One purifier is non-pivotal (the S3.1 algebra, division-free).**  If
`cγ ≤ M * (cγ - cstar)` (i.e. `M ≥ cγ/(cγ - cstar)`, S3's `M*`), the court
stays disgraced when one agent purifies: `M * cstar ≤ (M - 1) * cγ`.
-/
theorem pivotal_threshold (M cγ cstar : ℚ) (h : cγ ≤ M * (cγ - cstar)) :
    M * cstar ≤ (M - 1) * cγ := by
  ring_nf at h ⊢
  linarith

/--
**A large enough coalition flips the court (the S3.2 algebra, division-free).**
If `k * cγ > M * (cγ - cstar)` (i.e. the purifying fraction exceeds
`f* = 1 - cstar/cγ`), the remaining courtiers cannot hold the aggregate at the
threshold: `(M - k) * cγ < M * cstar`.
-/
theorem coalition_flips (M k cγ cstar : ℚ) (h : M * (cγ - cstar) < k * cγ) :
    (M - k) * cγ < M * cstar := by
  ring_nf at h ⊢
  linarith

/--
**The 2-agent non-product anchor (bare non-composability).**  The court's
satisfaction region is not a product of per-agent regions: with threshold
`2 * (3/5)` and courting levels in `{0, 1}`, honored at `(0,1)` and `(1,0)`
but not `(1,1)` refutes any product form.  (Near-definitional -- the margin
law below is the real content.)
-/
theorem court_not_product :
    ¬ ∃ (PA PB : ℚ → Prop), ∀ x y : ℚ, (x + y < 2 * (3 / 5 : ℚ)) ↔ (PA x ∧ PB y) := by
  rintro ⟨PA, PB, h⟩
  have h01 := (h 0 1).mp (by norm_num)
  have h10 := (h 1 0).mp (by norm_num)
  have h11 := (h 1 1).mpr ⟨h10.1, h01.2⟩
  norm_num at h11

/--
**The margin-recoding degeneracy is refuted: the court's value is additive in
NO per-agent recoding, even up to an affine offset.**  For no recoding
`g : ℚ → ℚ` and constant `β` does `courtValue = β + (p.map g).sum` hold over
all `(m+1)`-agent profiles, whenever one purifier is non-pivotal
(`(m+1) * cstar ≤ m * cγ`).  Three profiles pigeonhole any candidate:
all-courting and one-purifier (both value 0) force `g cγ = g 0`; all-pure
(value 1) then demands `0 = 1`.
-/
theorem court_value_not_additive (m : ℕ) (cγ cstar : ℚ) (h0 : 0 < cstar)
    (hle : cstar ≤ cγ) (hpiv : ((m : ℚ) + 1) * cstar ≤ (m : ℚ) * cγ) :
    ¬ ∃ (g : ℚ → ℚ) (β : ℚ), ∀ p : List ℚ, p.length = m + 1 →
      courtValue (m + 1) cstar p = β + (p.map g).sum := by
  rintro ⟨g, β, hg⟩
  have hm : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
  have hM : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  -- all-courting: value 0, so (m+1) * g cγ = 0.
  have e1 := hg (List.replicate (m + 1) cγ) (List.length_replicate)
  rw [courtValue, if_neg (by
        rw [List.sum_replicate, nsmul_eq_mul, hM]
        nlinarith)] at e1
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul, hM] at e1
  -- one purifier: value 0 by non-pivotality, so g 0 + m * g cγ = 0.
  have e2 := hg (0 :: List.replicate m cγ) (by simp)
  rw [courtValue, if_neg (by
        rw [List.sum_cons, List.sum_replicate, nsmul_eq_mul, hM]
        nlinarith)] at e2
  rw [List.map_cons, List.sum_cons, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul] at e2
  -- all-pure: value 1, so (m+1) * g 0 = 1.
  have e3 := hg (List.replicate (m + 1) 0) (List.length_replicate)
  rw [courtValue, if_pos (by
        rw [List.sum_replicate, nsmul_eq_mul, hM]
        nlinarith)] at e3
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul, hM] at e3
  -- pigeonhole: e1 − e2 forces g cγ = g 0; then e1 against e3 forces 0 = 1.
  have key : g cγ = g 0 := by linarith
  rw [key] at e1
  linarith

/--
**The keyed-composition margin law, packaged.**  At shared parameters: the
behavior-keyed bound is exactly additive (achieved sum bound -- linear
degradation, marginal = own cap), while the outcome-keyed value is additive in
no per-agent recoding (flat-then-cliff).  Composition of a guarantee is decided
by what it is keyed on.
-/
theorem keyed_margin_law (m : ℕ) (κ cγ cstar : ℚ) (hκ : 0 ≤ κ) (h0 : 0 < cstar)
    (hle : cstar ≤ cγ) (hpiv : ((m : ℚ) + 1) * cstar ≤ (m : ℚ) * cγ) :
    (∃ ds : List ℚ, List.Forall₂ (fun d k => |d| ≤ k) ds (List.replicate (m + 1) κ) ∧
        |ds.sum| = (List.replicate (m + 1) κ).sum)
    ∧ ¬ ∃ (g : ℚ → ℚ) (β : ℚ), ∀ p : List ℚ, p.length = m + 1 →
        courtValue (m + 1) cstar p = β + (p.map g).sum := by
  refine ⟨cap_bound_tight _ (fun k hk => ?_), court_value_not_additive m cγ cstar h0 hle hpiv⟩
  rw [List.eq_of_mem_replicate hk]
  exact hκ

/-! ## Local axiom audit -/

/-- info: 'Sundogcert.Percival.cap_bound_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_bound_additive

/-- info: 'Sundogcert.Percival.cap_bound_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_bound_tight

/-- info: 'Sundogcert.Percival.cap_marginal_profile_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cap_marginal_profile_independent

/-- info: 'Sundogcert.Percival.pivotal_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pivotal_threshold

/-- info: 'Sundogcert.Percival.coalition_flips' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coalition_flips

/-- info: 'Sundogcert.Percival.court_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms court_not_product

/-- info: 'Sundogcert.Percival.court_value_not_additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms court_value_not_additive

/-- info: 'Sundogcert.Percival.keyed_margin_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keyed_margin_law

end Sundogcert.Percival
