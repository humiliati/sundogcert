/-
# TS-3: `semialgebraicStructure` — the second o-minimal structure, and the payoff.

The `SADef` classes assemble into an `OMinStructure`:

- booleans — the 2d-1 algebra;
- **substitution** — atoms transport along `MvPolynomial.rename` (`eval_rename`);
- **projection** — THE TS-2 PAYOFF: a `SADef` set is characterized by the sign vectors
  of a finite family (`sadef_sign_char`, by induction over the `allSignVecs`
  enumeration); the snoc-projection transports to the cons-based `finSuccEquiv` frame
  by the rotation `Fin.snoc Fin.succ 0`, and each sign-vector fiber is semialgebraic
  by `elim_signVector`;
- the `lt`/singleton atoms are linear polynomials;
- **tame_dim_one** — on the line, the sign vector is constant between the cuts of the
  family (TS-1 `family_sign_partition`), so the frontier of a `SADef 1` set lies in
  the finite cut set.

**`semialgebraicStructure : OMinStructure`** is the first genuinely nonlinear
machine-checked o-minimal structure here; through it the whiteboard theorems
instantiate at the real field: `semialgebraic_s1_eq_tame` (dim-1 semialgebraic =
tame), `semialgebraic_uniform_finiteness`, `semialgebraic_cell_decomposition`.
-/
import Sundogcert.DiagramAssembly
import Sundogcert.OMinimalCellDecomp

namespace Sundog.TarskiQE

open Polynomial Sundog.OMinimalOne Sundog.OMinimalAbstract

variable {n : ℕ}

/-! ### The sign characterization of SADef sets -/

/-- Every `SADef` set is a sign-vector condition on a finite family. -/
theorem sadef_sign_char {m : ℕ} {A : Set (Fin m → ℝ)} (hA : SADef m A) :
    ∃ (F : List (MvPolynomial (Fin m) ℝ)) (sigs : List (List SignType)),
      ∀ h : Fin m → ℝ,
        h ∈ A ↔ F.map (fun q => SignType.sign (MvPolynomial.eval h q)) ∈ sigs := by
  induction hA with
  | pos q =>
    refine ⟨[q], [[SignType.pos]], fun h => ?_⟩
    simp only [Set.mem_setOf_eq, List.map_cons, List.map_nil, List.mem_singleton,
      List.cons.injEq, and_true]
    exact ⟨fun hp => sign_pos hp, fun hs => sign_eq_one_iff.mp hs⟩
  | compl hA ih =>
    obtain ⟨F, sigs, hch⟩ := ih
    refine ⟨F, (allSignVecs F.length).filter (fun τ => τ ∉ sigs), fun h => ?_⟩
    constructor
    · intro hc
      rw [List.mem_filter]
      refine ⟨mem_allSignVecs (by simp), ?_⟩
      simp only [decide_eq_true_eq]
      exact fun hmem => hc ((hch h).mpr hmem)
    · intro hmem hA'
      rw [List.mem_filter] at hmem
      have h2 := hmem.2
      simp only [decide_eq_true_eq] at h2
      exact h2 ((hch h).mp hA')
  | union hA hB ihA ihB =>
    obtain ⟨FA, sigsA, hchA⟩ := ihA
    obtain ⟨FB, sigsB, hchB⟩ := ihB
    refine ⟨FA ++ FB, (allSignVecs (FA ++ FB).length).filter
      (fun τ => τ.take FA.length ∈ sigsA ∨ τ.drop FA.length ∈ sigsB), fun h => ?_⟩
    have hsplit : (FA ++ FB).map (fun q => SignType.sign (MvPolynomial.eval h q))
        = (FA.map fun q => SignType.sign (MvPolynomial.eval h q))
          ++ (FB.map fun q => SignType.sign (MvPolynomial.eval h q)) := by
      rw [List.map_append]
    have htake : ((FA ++ FB).map
        (fun q => SignType.sign (MvPolynomial.eval h q))).take FA.length
        = FA.map fun q => SignType.sign (MvPolynomial.eval h q) := by
      rw [hsplit]
      exact List.take_left' (by rw [List.length_map])
    have hdrop : ((FA ++ FB).map
        (fun q => SignType.sign (MvPolynomial.eval h q))).drop FA.length
        = FB.map fun q => SignType.sign (MvPolynomial.eval h q) := by
      rw [hsplit]
      exact List.drop_left' (by rw [List.length_map])
    constructor
    · intro hmem
      rw [List.mem_filter]
      refine ⟨mem_allSignVecs (by simp), ?_⟩
      simp only [decide_eq_true_eq]
      rcases hmem with hA' | hB'
      · exact Or.inl (by rw [htake]; exact (hchA h).mp hA')
      · exact Or.inr (by rw [hdrop]; exact (hchB h).mp hB')
    · intro hmem
      rw [List.mem_filter] at hmem
      have h2 := hmem.2
      simp only [decide_eq_true_eq] at h2
      rcases h2 with hA' | hB'
      · exact Or.inl ((hchA h).mpr (by rw [htake] at hA'; exact hA'))
      · exact Or.inr ((hchB h).mpr (by rw [hdrop] at hB'; exact hB'))

/-! ### Substitution -/

theorem sadef_subst {m k : ℕ} (σ : Fin m → Fin k) {A : Set (Fin m → ℝ)}
    (hA : SADef m A) : SADef k {f : Fin k → ℝ | f ∘ σ ∈ A} := by
  induction hA with
  | pos q =>
    have e : {f : Fin k → ℝ | f ∘ σ ∈ {g | 0 < MvPolynomial.eval g q}}
        = {f | 0 < MvPolynomial.eval f (MvPolynomial.rename σ q)} := by
      ext f
      simp [MvPolynomial.eval_rename]
    rw [e]
    exact SADef.pos _
  | @compl s _ ih =>
    have e : {f : Fin k → ℝ | f ∘ σ ∈ sᶜ} = {f : Fin k → ℝ | f ∘ σ ∈ s}ᶜ := rfl
    rw [e]
    exact ih.compl
  | @union s t _ _ ihs iht =>
    have e : {f : Fin k → ℝ | f ∘ σ ∈ s ∪ t}
        = {f : Fin k → ℝ | f ∘ σ ∈ s} ∪ {f : Fin k → ℝ | f ∘ σ ∈ t} := rfl
    rw [e]
    exact ihs.union iht

/-! ### Projection: the TS-2 payoff -/

theorem sadef_proj {A : Set (Fin (n + 1) → ℝ)} (hA : SADef (n + 1) A) :
    SADef n {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A} := by
  obtain ⟨F, sigs, hch⟩ := sadef_sign_char hA
  have hcomp : ∀ (g : Fin n → ℝ) (y : ℝ),
      (Fin.cons y g : Fin (n + 1) → ℝ) ∘ (Fin.snoc Fin.succ 0) = Fin.snoc g y := by
    intro g y
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp
  set F' : List (Polynomial (MvPolynomial (Fin n) ℝ)) := F.map fun q =>
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.rename (Fin.snoc Fin.succ 0) q)
    with hF'
  have hvec : ∀ (g : Fin n → ℝ) (y : ℝ),
      F.map (fun q => SignType.sign (MvPolynomial.eval (Fin.snoc g y) q))
        = signVec F' g y := by
    intro g y
    rw [signVec, hF', List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply]
    rw [← spec_eval_cons, MvPolynomial.eval_rename, hcomp g y]
  have hset : {g : Fin n → ℝ | ∃ y : ℝ, Fin.snoc g y ∈ A}
      = ⋃ σ ∈ sigs, {g : Fin n → ℝ | ∃ y : ℝ, signVec F' g y = σ} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, hy⟩
      have hv := (hch (Fin.snoc g y)).mp hy
      rw [hvec g y] at hv
      exact ⟨_, hv, y, rfl⟩
    · rintro ⟨σ, hσ, y, hy⟩
      refine ⟨y, (hch (Fin.snoc g y)).mpr ?_⟩
      rw [hvec g y, hy]
      exact hσ
  rw [hset]
  exact SADef.list_biUnion fun σ _ => elim_signVector F' σ

/-! ### The atoms -/

theorem sadef_lt : SADef 2 {f : Fin 2 → ℝ | f 0 < f 1} := by
  have e : {f : Fin 2 → ℝ | f 0 < f 1}
      = {f | 0 < MvPolynomial.eval f (MvPolynomial.X 1 - MvPolynomial.X 0)} := by
    ext f
    simp [sub_pos]
  rw [e]
  exact SADef.pos _

theorem sadef_singleton (r : ℝ) : SADef 1 {f : Fin 1 → ℝ | f 0 = r} := by
  have e : {f : Fin 1 → ℝ | f 0 = r}
      = {f | MvPolynomial.eval f (MvPolynomial.X 0 - MvPolynomial.C r) = 0} := by
    ext f
    simp [sub_eq_zero]
  rw [e]
  exact SADef.zero _

/-! ### Dimension one is tame -/

private theorem avoid_around (C : Finset ℝ) :
    ∀ x : ℝ, x ∉ C → ∃ a b : ℝ, a < x ∧ x < b ∧ ∀ s ∈ C, s ∉ Set.Ioo a b := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    intro x _
    exact ⟨x - 1, x + 1, by linarith, by linarith, by simp⟩
  | @insert c s _ ih =>
    intro x hx
    rw [Finset.mem_insert] at hx
    push Not at hx
    obtain ⟨a, b, hax, hxb, havoid⟩ := ih x hx.2
    rcases lt_trichotomy c x with hcx | rfl | hxc
    · refine ⟨max a c, b, max_lt hax hcx, hxb, ?_⟩
      intro s' hs' hmem
      rcases Finset.mem_insert.mp hs' with heq | hs'
      · rw [heq] at hmem
        exact absurd hmem.1 (not_lt.mpr (le_max_right a c))
      · exact havoid s' hs' ⟨lt_of_le_of_lt (le_max_left a c) hmem.1, hmem.2⟩
    · exact absurd rfl hx.1
    · refine ⟨a, min b c, hax, lt_min hxb hxc, ?_⟩
      intro s' hs' hmem
      rcases Finset.mem_insert.mp hs' with heq | hs'
      · rw [heq] at hmem
        exact absurd hmem.2 (not_lt.mpr (min_le_right b c))
      · exact havoid s' hs' ⟨hmem.1, lt_of_lt_of_le hmem.2 (min_le_left b c)⟩

theorem sadef_tame_dim_one {A : Set (Fin 1 → ℝ)} (hA : SADef 1 A) :
    Tame {x : ℝ | (fun _ => x) ∈ A} := by
  classical
  obtain ⟨F, sigs, hch⟩ := sadef_sign_char hA
  set g₀ : Fin 0 → ℝ := fun i => i.elim0 with hg₀
  set pF : List ℝ[X] :=
    F.map fun q => spec g₀ (MvPolynomial.finSuccEquiv ℝ 0 q) with hpF
  have hvec : ∀ x : ℝ,
      F.map (fun q => SignType.sign (MvPolynomial.eval (fun _ => x) q))
        = pF.map fun p => SignType.sign (p.eval x) := by
    intro x
    rw [hpF, List.map_map]
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply]
    have hconst : (fun _ : Fin 1 => x) = Fin.cons x g₀ := by
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [hconst, spec_eval_cons]
  have hT : {x : ℝ | (fun _ : Fin 1 => x) ∈ A}
      = {x : ℝ | (pF.map fun p => SignType.sign (p.eval x)) ∈ sigs} := by
    ext x
    rw [Set.mem_setOf_eq, hch (fun _ => x), hvec x]
    rfl
  rw [hT]
  obtain ⟨C, hC⟩ := family_sign_partition (pF.filter fun p => p ≠ 0)
    (fun p hp => by simpa using (List.mem_filter.mp hp).2)
  refine Set.Finite.subset C.finite_toSet ?_
  intro x hx
  by_contra hxC
  obtain ⟨a, b, hax, hxb, havoid⟩ := avoid_around C x (by simpa using hxC)
  have hconstv : ∀ x' ∈ Set.Ioo a b,
      (pF.map fun p => SignType.sign (p.eval x'))
        = pF.map fun p => SignType.sign (p.eval x) := by
    intro x' hx'
    refine List.map_congr_left fun p hp => ?_
    by_cases hp0 : p = 0
    · rw [hp0]
      simp
    · have hpF' : p ∈ pF.filter (fun p => p ≠ 0) :=
        List.mem_filter.mpr ⟨hp, by simpa⟩
      rcases hC a b (lt_trans hax hxb) havoid p hpF' with hpos | hneg
      · rw [sign_pos (hpos x' hx'), sign_pos (hpos x ⟨hax, hxb⟩)]
      · rw [sign_neg (hneg x' hx'), sign_neg (hneg x ⟨hax, hxb⟩)]
  by_cases hxT : (pF.map fun p => SignType.sign (p.eval x)) ∈ sigs
  · have hsub : Set.Ioo a b
        ⊆ {x : ℝ | (pF.map fun p => SignType.sign (p.eval x)) ∈ sigs} := by
      intro x' hx'
      rw [Set.mem_setOf_eq, hconstv x' hx']
      exact hxT
    have hint : x ∈ interior
        {x : ℝ | (pF.map fun p => SignType.sign (p.eval x)) ∈ sigs} :=
      mem_interior.mpr ⟨Set.Ioo a b, hsub, isOpen_Ioo, ⟨hax, hxb⟩⟩
    exact hx.2 hint
  · have hncl : x ∉ closure
        {x : ℝ | (pF.map fun p => SignType.sign (p.eval x)) ∈ sigs} := by
      intro hcl
      obtain ⟨z, hz1, hz2⟩ := (mem_closure_iff.mp hcl) (Set.Ioo a b)
        isOpen_Ioo ⟨hax, hxb⟩
      rw [Set.mem_setOf_eq, hconstv z hz1] at hz2
      exact hxT hz2
    exact hncl hx.1

/-! ### The structure -/

/-- **The semialgebraic o-minimal structure** — the second witness, and the first
genuinely nonlinear one. Projection is Tarski–Seidenberg (`elim_signVector`). -/
def semialgebraicStructure : OMinStructure where
  Definable := fun {m} A => SADef m A
  definable_empty := SADef.empty
  definable_compl := SADef.compl
  definable_union := SADef.union
  definable_subst := by
    intro m k σ A hA
    exact sadef_subst σ hA
  definable_proj := by
    intro m A hA
    exact sadef_proj hA
  definable_lt := sadef_lt
  definable_singleton := sadef_singleton
  tame_dim_one := by
    intro A hA
    exact sadef_tame_dim_one hA

/-! ### The whiteboard at the real field -/

/-- Dimension-one semialgebraic sets are EXACTLY the tame sets. -/
theorem semialgebraic_s1_eq_tame (T : Set ℝ) : SADef 1 (toOne T) ↔ Tame T :=
  s1_eq_tame semialgebraicStructure T

/-- **Uniform Finiteness at the real field.** -/
theorem semialgebraic_uniform_finiteness {A : Set (Fin 2 → ℝ)} (hA : SADef 2 A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    ∃ N : ℕ, ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.ncard ≤ N :=
  uniform_finiteness (S := semialgebraicStructure) hA hfib

/-- **Cell decomposition for ℝ² at the real field.** -/
theorem semialgebraic_cell_decomposition {A : Set (Fin 2 → ℝ)} (hA : SADef 2 A) :
    ∃ cells : List Cell₂, IsCellDecomp cells A :=
  cell_decomposition (S := semialgebraicStructure) hA

end Sundog.TarskiQE
