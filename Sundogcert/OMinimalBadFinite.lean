/-
# O-min lane R4-D4c: the tube kill — the bad sets are finite.

The heart of the classical Finiteness Lemma, machine-checked. Under the UF hypotheses
(`A` definable, every fiber finite), all three bad sets are FINITE:

- **`notNormalTop_finite` / `notNormalBot_finite` — the ray kills.** If top-ray normality
  failed on an interval, shrink to where the (definable, D4b) fiber-max function is
  continuous: at any point, a constant `d` above the local max caps a whole window — a ray
  box, so the point was top-normal after all. The offending A-point itself witnesses the
  fiber-max spec, so no domain bookkeeping is needed.
- **`badFin_finite` — THE TUBE.** If some height were non-normal over an interval: dodge
  the finitely many `¬NormalBot` points (so `β` = least non-normal height exists), split
  the interval by the three tame flags (fiber-points-below-β, fiber-points-above-β, and
  β-on-the-graph), shrink to where `β`, `β⁻`, `β⁺` are all continuous, and pick constants
  `c < β < d` squeezing between the fiber neighbors. **The tube `(c,d)` is then A-free
  except exactly for the β-graph** — every would-be invader in a nearby column is trapped
  at-or-beyond its own fiber neighbors. So the box around `(a*, β a*)` is either a thin
  continuous graph box or an empty box: `(a*, β a*)` is *normal*, contradicting β's
  definition as the least non-normal height.

With `abnormal_finite` (the union), D4d gets: away from finitely many parameters, every
point and both ray-ends are normal — the count-constancy input.

**Honest fence.** D4c only: no count constancy, no UF statement (D4d).
-/
import Sundogcert.OMinimalBeta

namespace Sundog.OMinimalAbstract

open Sundog.OMinimalOne Sundog.OMinimalAbstract.Fml Topology

variable {S : OMinStructure} {A : Set (Fin 2 → ℝ)}

/-! ### Local helpers -/

private theorem tcompPair {n : ℕ} (h : Fin n → ℝ) (i j : Fin n) :
    h ∘ ![i, j] = pairFn (h i) (h j) := by
  funext k
  fin_cases k <;> simp [pairFn, Function.comp]

private theorem snocPairL (g : Fin 1 → ℝ) (t : ℝ) :
    (Fin.snoc g t : Fin 2 → ℝ) = pairFn (g 0) t := by
  funext k
  fin_cases k <;> simp [pairFn, Fin.snoc]

private theorem ts2_0 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem tsL2 (h : Fin 1 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 2 → ℝ) 1 = z := by simp [Fin.snoc]

private theorem ts3_0 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 0 = h 0 := by simp [Fin.snoc]

private theorem ts3_1 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 1 = h 1 := by simp [Fin.snoc]

private theorem tsL3 (h : Fin 2 → ℝ) (z : ℝ) :
    (Fin.snoc h z : Fin 3 → ℝ) 2 = z := by simp [Fin.snoc]

attribute [local simp] ts2_0 tsL2 ts3_0 ts3_1 tsL3

private theorem tame_Ioo {a b : ℝ} (hab : a < b) : Tame (Set.Ioo a b) := by
  unfold Tame
  rw [frontier_Ioo hab]
  exact (Set.finite_singleton b).insert a

/-- One tame split step, disjunction packed inside the existential so case analysis can be
deferred: every interval has a subinterval lying entirely inside `T` or entirely outside. -/
private theorem split_interval {T : Set ℝ} (hT : Tame T) {a b : ℝ} (hab : a < b) :
    ∃ c d : ℝ, c < d ∧ Set.Ioo c d ⊆ Set.Ioo a b ∧
      ((∀ x ∈ Set.Ioo c d, x ∈ T) ∨ (∀ x ∈ Set.Ioo c d, x ∉ T)) := by
  by_cases hinf : (Set.Ioo a b ∩ T).Infinite
  · obtain ⟨c, d, hcd, hsub⟩ :=
      tame_infinite_contains_Ioo (tame_inter (tame_Ioo hab) hT) hinf
    exact ⟨c, d, hcd, fun x hx => (hsub hx).1, Or.inl (fun x hx => (hsub hx).2)⟩
  · rw [Set.not_infinite] at hinf
    have hinf' : (Set.Ioo a b ∩ Tᶜ).Infinite := by
      have hd : Set.Ioo a b ∩ Tᶜ = Set.Ioo a b \ (Set.Ioo a b ∩ T) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]
        tauto
      rw [hd]
      exact (Set.Ioo_infinite hab).diff hinf
    obtain ⟨c, d, hcd, hsub⟩ :=
      tame_infinite_contains_Ioo (tame_inter (tame_Ioo hab) (tame_compl hT)) hinf'
    exact ⟨c, d, hcd, fun x hx => (hsub hx).1, Or.inr (fun x hx => (hsub hx).2)⟩

/-! ### The three tame flags -/

private theorem tame_blo (hA : S.Definable A) :
    Tame {x : ℝ | ∃ y, pairFn x y ∈ A ∧ y < betaFn A x} := by
  have hG := definableFun_betaFn hA
  have h := Fml.tame_one (S := S) (Fml.ex (Fml.ex ((Fml.atom ![0, 2] hG).and
    ((Fml.atom ![0, 1] hA).and (ltAt 1 2)))))
  have e : {x : ℝ | ∃ y, pairFn x y ∈ A ∧ y < betaFn A x}
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.ex (Fml.ex ((Fml.atom ![0, 2] hG).and
        ((Fml.atom ![0, 1] hA).and (ltAt 1 2))))) (fun _ => x)} := by
    ext a
    simp [Fml.eval, tcompPair, exists_eq_left']
  rw [e]
  exact h

private theorem tame_bhi (hA : S.Definable A) :
    Tame {x : ℝ | ∃ y, pairFn x y ∈ A ∧ betaFn A x < y} := by
  have hG := definableFun_betaFn hA
  have h := Fml.tame_one (S := S) (Fml.ex (Fml.ex ((Fml.atom ![0, 2] hG).and
    ((Fml.atom ![0, 1] hA).and (ltAt 2 1)))))
  have e : {x : ℝ | ∃ y, pairFn x y ∈ A ∧ betaFn A x < y}
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.ex (Fml.ex ((Fml.atom ![0, 2] hG).and
        ((Fml.atom ![0, 1] hA).and (ltAt 2 1))))) (fun _ => x)} := by
    ext a
    simp [Fml.eval, tcompPair, exists_eq_left']
  rw [e]
  exact h

private theorem tame_gset (hA : S.Definable A) :
    Tame {x : ℝ | pairFn x (betaFn A x) ∈ A} := by
  have hG := definableFun_betaFn hA
  have h := Fml.tame_one (S := S) (Fml.ex ((Fml.atom id hG).and (Fml.atom id hA)))
  have e : {x : ℝ | pairFn x (betaFn A x) ∈ A}
      = {x : ℝ | Fml.eval (S := S) (n := 1) (Fml.ex ((Fml.atom id hG).and
          (Fml.atom id hA))) (fun _ => x)} := by
    ext a
    simp [Fml.eval, snocPairL, exists_eq_left']
  rw [e]
  exact h

/-! ### The ray kills -/

/-- **Top-ray normality fails only finitely often.** -/
theorem notNormalTop_finite (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    {a : ℝ | ¬ NormalTop A a}.Finite := by
  by_contra hinf
  obtain ⟨a₀, b₀, h₀, hsub₀⟩ :=
    tame_infinite_contains_Ioo (tame_notNormalTop hA) hinf
  obtain ⟨F, hF⟩ := monotonicity_theorem_continuous (definableFun_maxFn hA)
  obtain ⟨a₂, b₂, h₂, hsub₂, havoid₂⟩ := avoid_finset F a₀ b₀ h₀
  have hcont : ContinuousOn (maxFn A) (Set.Ioo a₂ b₂) := (hF a₂ b₂ h₂ havoid₂).2
  obtain ⟨astar, hastar⟩ := exists_between h₂
  apply hsub₀ (hsub₂ hastar)
  obtain ⟨d, hd⟩ := exists_gt (maxFn A astar)
  have hca : ContinuousAt (maxFn A) astar :=
    hcont.continuousAt (Ioo_mem_nhds hastar.1 hastar.2)
  have hpre : maxFn A ⁻¹' Set.Iio d ∈ 𝓝 astar :=
    hca.preimage_mem_nhds (Iio_mem_nhds hd)
  obtain ⟨u, w, hauw, hsubw⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
  refine ⟨u, w, d, ⟨hauw.1, hauw.2⟩, ?_⟩
  intro x hx y hy hyA
  have hxd : maxFn A x < d := hsubw ⟨hx.1, hx.2⟩
  have hmax := maxFn_mem (hfib x) ⟨y, hyA⟩
  rw [mem_fiberMaxSet] at hmax
  exact hmax.2 y hyA (lt_trans hxd hy)

/-- **Bottom-ray normality fails only finitely often.** -/
theorem notNormalBot_finite (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    {a : ℝ | ¬ NormalBot A a}.Finite := by
  by_contra hinf
  obtain ⟨a₀, b₀, h₀, hsub₀⟩ :=
    tame_infinite_contains_Ioo (tame_notNormalBot hA) hinf
  obtain ⟨F, hF⟩ := monotonicity_theorem_continuous (definableFun_minFn hA)
  obtain ⟨a₂, b₂, h₂, hsub₂, havoid₂⟩ := avoid_finset F a₀ b₀ h₀
  have hcont : ContinuousOn (minFn A) (Set.Ioo a₂ b₂) := (hF a₂ b₂ h₂ havoid₂).2
  obtain ⟨astar, hastar⟩ := exists_between h₂
  apply hsub₀ (hsub₂ hastar)
  obtain ⟨p, hp⟩ := exists_lt (minFn A astar)
  have hca : ContinuousAt (minFn A) astar :=
    hcont.continuousAt (Ioo_mem_nhds hastar.1 hastar.2)
  have hpre : minFn A ⁻¹' Set.Ioi p ∈ 𝓝 astar :=
    hca.preimage_mem_nhds (Ioi_mem_nhds hp)
  obtain ⟨u, w, hauw, hsubw⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
  refine ⟨u, w, p, ⟨hauw.1, hauw.2⟩, ?_⟩
  intro x hx y hy hyA
  have hxp : p < minFn A x := hsubw ⟨hx.1, hx.2⟩
  have hmin := minFn_mem (hfib x) ⟨y, hyA⟩
  rw [mem_fiberMinSet] at hmin
  exact hmin.2 y hyA (lt_trans hy hxp)

/-! ### The tube kill -/

/-- **The finite-height bad set is finite** — the tube argument. -/
theorem badFin_finite (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    {a : ℝ | ∃ b, ¬ Normal A a b}.Finite := by
  classical
  by_contra hinf
  -- 1. an interval of bad parameters
  obtain ⟨a₀, b₀, h₀, hsub₀⟩ := tame_infinite_contains_Ioo (tame_badFin hA) hinf
  -- 2. dodge the finitely many ¬NormalBot points, so β exists
  obtain ⟨a₁, b₁, h₁, hsub₁, havoid₁⟩ :=
    avoid_finset (notNormalBot_finite hA hfib).toFinset a₀ b₀ h₀
  have hbot : ∀ x ∈ Set.Ioo a₁ b₁, NormalBot A x := by
    intro x hx
    by_contra hnb
    exact havoid₁ x ((notNormalBot_finite hA hfib).mem_toFinset.mpr hnb) hx
  -- 3. split by the three tame flags
  obtain ⟨cA, dA, hcdA, hsubA, hlo⟩ := split_interval (tame_blo hA) h₁
  obtain ⟨cB, dB, hcdB, hsubB, hhi⟩ := split_interval (tame_bhi hA) hcdA
  obtain ⟨cC, dC, hcdC, hsubC, hg⟩ := split_interval (tame_gset hA) hcdB
  -- 4. continuity shrink for β, β⁻, β⁺ at once
  obtain ⟨Fb, hFb⟩ := monotonicity_theorem_continuous (definableFun_betaFn hA)
  obtain ⟨Fm, hFm⟩ := monotonicity_theorem_continuous (definableFun_betaMinusFn hA)
  obtain ⟨Fp, hFp⟩ := monotonicity_theorem_continuous (definableFun_betaPlusFn hA)
  obtain ⟨c₄, d₄, hcd₄, hsub₄, havoid₄⟩ := avoid_finset (Fb ∪ Fm ∪ Fp) cC dC hcdC
  have hcontβ : ContinuousOn (betaFn A) (Set.Ioo c₄ d₄) :=
    (hFb c₄ d₄ hcd₄ (fun s hs =>
      havoid₄ s (Finset.mem_union_left _ (Finset.mem_union_left _ hs)))).2
  have hcontm : ContinuousOn (betaMinusFn A) (Set.Ioo c₄ d₄) :=
    (hFm c₄ d₄ hcd₄ (fun s hs =>
      havoid₄ s (Finset.mem_union_left _ (Finset.mem_union_right _ hs)))).2
  have hcontp : ContinuousOn (betaPlusFn A) (Set.Ioo c₄ d₄) :=
    (hFp c₄ d₄ hcd₄ (fun s hs => havoid₄ s (Finset.mem_union_right _ hs))).2
  -- membership chains
  have hinC : ∀ x ∈ Set.Ioo c₄ d₄, x ∈ Set.Ioo cC dC := fun x hx => hsub₄ hx
  have hinB : ∀ x ∈ Set.Ioo c₄ d₄, x ∈ Set.Ioo cB dB := fun x hx => hsubC (hinC x hx)
  have hinA : ∀ x ∈ Set.Ioo c₄ d₄, x ∈ Set.Ioo cA dA := fun x hx => hsubB (hinB x hx)
  have hin1 : ∀ x ∈ Set.Ioo c₄ d₄, x ∈ Set.Ioo a₁ b₁ := fun x hx => hsubA (hinA x hx)
  -- β's spec on the final interval
  have hβspec : ∀ x ∈ Set.Ioo c₄ d₄,
      ¬ Normal A x (betaFn A x) ∧ ∀ z' : ℝ, z' < betaFn A x → Normal A x z' := by
    intro x hx
    exact mem_leastBadSet.mp
      (betaFn_mem (hbot x (hin1 x hx)) (hsub₀ (hsub₁ (hin1 x hx))))
  -- 5. the point of contradiction
  obtain ⟨astar, hastar⟩ := exists_between hcd₄
  apply (hβspec astar hastar).1
  -- 6. the lower tube edge
  have hedge_lo : ∃ c : ℝ, c < betaFn A astar ∧ ∃ N ∈ 𝓝 astar,
      ∀ x ∈ N, x ∈ Set.Ioo c₄ d₄ →
        ∀ y : ℝ, pairFn x y ∈ A → c < y → betaFn A x ≤ y := by
    rcases hlo with hyes | hno
    · have hbm := betaMinusFn_mem (hfib astar) (hyes astar (hinA astar hastar))
      rw [mem_maxBelowSet] at hbm
      obtain ⟨c, hc1, hc2⟩ := exists_between hbm.2.1
      have hcam : ContinuousAt (betaMinusFn A) astar :=
        hcontm.continuousAt (Ioo_mem_nhds hastar.1 hastar.2)
      refine ⟨c, hc2, _, hcam.preimage_mem_nhds (Iio_mem_nhds hc1), ?_⟩
      intro x hxN hx₄ y hyA hcy
      by_contra hlt
      rw [not_le] at hlt
      have hbmx := betaMinusFn_mem (hfib x) ⟨y, hyA, hlt⟩
      rw [mem_maxBelowSet] at hbmx
      have hyle := hbmx.2.2 y ⟨hyA, hlt⟩
      rw [not_lt] at hyle
      have hxc : betaMinusFn A x < c := hxN
      exact absurd hcy (not_lt.mpr (le_trans hyle hxc.le))
    · obtain ⟨c, hc⟩ := exists_lt (betaFn A astar)
      refine ⟨c, hc, Set.Ioo cA dA, Ioo_mem_nhds (hinA astar hastar).1
        (hinA astar hastar).2, ?_⟩
      intro x hxN _ y hyA _
      by_contra hlt
      rw [not_le] at hlt
      exact hno x hxN ⟨y, hyA, hlt⟩
  -- 7. the upper tube edge (mirror)
  have hedge_hi : ∃ d : ℝ, betaFn A astar < d ∧ ∃ N ∈ 𝓝 astar,
      ∀ x ∈ N, x ∈ Set.Ioo c₄ d₄ →
        ∀ y : ℝ, pairFn x y ∈ A → y < d → y ≤ betaFn A x := by
    rcases hhi with hyes | hno
    · have hbp := betaPlusFn_mem (hfib astar) (hyes astar (hinB astar hastar))
      rw [mem_minAboveSet] at hbp
      obtain ⟨d, hd1, hd2⟩ := exists_between hbp.2.1
      have hcap : ContinuousAt (betaPlusFn A) astar :=
        hcontp.continuousAt (Ioo_mem_nhds hastar.1 hastar.2)
      refine ⟨d, hd1, _, hcap.preimage_mem_nhds (Ioi_mem_nhds hd2), ?_⟩
      intro x hxN hx₄ y hyA hyd
      by_contra hlt
      rw [not_le] at hlt
      have hbpx := betaPlusFn_mem (hfib x) ⟨y, hyA, hlt⟩
      rw [mem_minAboveSet] at hbpx
      have hyge := hbpx.2.2 y ⟨hyA, hlt⟩
      rw [not_lt] at hyge
      have hxd : d < betaPlusFn A x := hxN
      exact absurd hyd (not_lt.mpr (le_trans hxd.le hyge))
    · obtain ⟨d, hd⟩ := exists_gt (betaFn A astar)
      refine ⟨d, hd, Set.Ioo cB dB, Ioo_mem_nhds (hinB astar hastar).1
        (hinB astar hastar).2, ?_⟩
      intro x hxN _ y hyA _
      by_contra hlt
      rw [not_le] at hlt
      exact hno x hxN ⟨y, hyA, hlt⟩
  obtain ⟨c, hc, Nlo, hNlo, hlo'⟩ := hedge_lo
  obtain ⟨d, hd, Nhi, hNhi, hhi'⟩ := hedge_hi
  -- 8. the common window
  have hcaβ : ContinuousAt (betaFn A) astar :=
    hcontβ.continuousAt (Ioo_mem_nhds hastar.1 hastar.2)
  have hbig : (Set.Ioo c₄ d₄ ∩ Nlo ∩ Nhi ∩ betaFn A ⁻¹' Set.Ioi c ∩
      betaFn A ⁻¹' Set.Iio d) ∈ 𝓝 astar :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (Ioo_mem_nhds hastar.1 hastar.2) hNlo) hNhi)
      (hcaβ.preimage_mem_nhds (Ioi_mem_nhds hc)))
      (hcaβ.preimage_mem_nhds (Iio_mem_nhds hd))
  obtain ⟨u, w, hauw, hsubw⟩ := mem_nhds_iff_exists_Ioo_subset.mp hbig
  have hW : ∀ x ∈ Set.Ioo u w, x ∈ Set.Ioo c₄ d₄ ∧
      (∀ y : ℝ, pairFn x y ∈ A → c < y → betaFn A x ≤ y) ∧
      (∀ y : ℝ, pairFn x y ∈ A → y < d → y ≤ betaFn A x) ∧
      c < betaFn A x ∧ betaFn A x < d := by
    intro x hx
    obtain ⟨⟨⟨⟨hx4, hxlo⟩, hxhi⟩, hxc⟩, hxd⟩ := hsubw hx
    exact ⟨hx4, hlo' x hxlo hx4, hhi' x hxhi hx4, hxc, hxd⟩
  -- the tube: inside the box, A-points ARE the β-graph
  have htube : ∀ x ∈ Set.Ioo u w, ∀ y : ℝ,
      ((c < y ∧ y < d) ∧ pairFn x y ∈ A) → y = betaFn A x := by
    intro x hx y hy
    obtain ⟨-, hLO, hHI, -, -⟩ := hW x hx
    exact le_antisymm (hHI y hy.2 hy.1.2) (hLO y hy.2 hy.1.1)
  obtain ⟨-, -, -, hcβs, hβds⟩ := hW astar hauw
  -- 9. normal after all: graph box or empty box
  rcases hg with hgin | hgout
  · refine ⟨u, w, c, d, ⟨⟨hauw.1, hauw.2⟩, hcβs, hβds⟩,
      Or.inr ⟨hgin astar (hinC astar hastar), ?_, ?_⟩⟩
    · -- thin
      intro x hx
      obtain ⟨hx4, -, -, hcβ, hβd⟩ := hW x ⟨hx.1, hx.2⟩
      exact ⟨betaFn A x, ⟨hcβ, hβd⟩, hgin x (hinC x hx4),
        fun y' hy' => htube x ⟨hx.1, hx.2⟩ y' hy'⟩
    · -- selection continuity: the selection IS β
      intro x hx y hy c' d' hbr
      have hyeq : y = betaFn A x := htube x ⟨hx.1, hx.2⟩ y ⟨hy.1, hy.2⟩
      subst hyeq
      obtain ⟨hx4, -, -, -, -⟩ := hW x ⟨hx.1, hx.2⟩
      have hcax : ContinuousAt (betaFn A) x :=
        hcontβ.continuousAt (Ioo_mem_nhds hx4.1 hx4.2)
      have hpre : betaFn A ⁻¹' Set.Ioo c' d' ∈ 𝓝 x :=
        hcax.preimage_mem_nhds (Ioo_mem_nhds hbr.1 hbr.2)
      obtain ⟨u', w', hxu'w', hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp hpre
      refine ⟨u', w', ⟨hxu'w'.1, hxu'w'.2⟩, ?_⟩
      intro x' hx' y' hy'
      have hy'eq : y' = betaFn A x' :=
        htube x' ⟨hx'.2.1, hx'.2.2⟩ y' ⟨hy'.1, hy'.2⟩
      rw [hy'eq]
      exact hsub' ⟨hx'.1.1, hx'.1.2⟩
  · refine ⟨u, w, c, d, ⟨⟨hauw.1, hauw.2⟩, hcβs, hβds⟩, Or.inl ?_⟩
    intro x y hxy hyA
    have hyeq : y = betaFn A x := htube x ⟨hxy.1.1, hxy.1.2⟩ y ⟨hxy.2, hyA⟩
    obtain ⟨hx4, -, -, -, -⟩ := hW x ⟨hxy.1.1, hxy.1.2⟩
    have hyA' : pairFn x (betaFn A x) ∈ A := by
      rw [← hyeq]
      exact hyA
    exact hgout x (hinC x hx4) hyA'

/-! ### The master bad set -/

/-- **The full bad set is finite**: away from finitely many parameters, every height and
both ray-ends are normal — D4d's input. -/
theorem abnormal_finite (hA : S.Definable A)
    (hfib : ∀ x : ℝ, {y : ℝ | pairFn x y ∈ A}.Finite) :
    {a : ℝ | (∃ b, ¬ Normal A a b) ∨ ¬ NormalTop A a ∨ ¬ NormalBot A a}.Finite := by
  have h := ((badFin_finite hA hfib).union
    ((notNormalTop_finite hA hfib).union (notNormalBot_finite hA hfib)))
  refine h.subset ?_
  intro a ha
  rcases ha with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

end Sundog.OMinimalAbstract
