/-
# Bounded piece certificate — N-1 positive half, quantitative (C-D1 / FoldCancellation follow-on)

The `FoldCancellation` module proved the *qualitative* positive half of N-1 (a monotone
circuit never folds, at any level). This module supplies the **quantitative** half — the
`O(d·k)` region bound — via the "safer Lean target": a bounded **piece certificate**
`HasPieceCover f k` instead of the exact chamber-count object.

`HasPieceCover f k` says `f` is affine on every interval whose interior avoids a finite cut
set of size `≤ k - 1`, i.e. `f` is covered by at most `k` affine pieces. This bounds the
linear-region count from above without committing to the exact tropical-hypersurface chamber
count (the literature's bounds-only object, deliberately deferred in `RegionCount`).

The load-bearing lemma is **`hasPieceCover_comp_mono`**: composing a **monotone** inner map
*adds* pieces,
  `HasPieceCover h n → HasPieceCover g m → Monotone h → HasPieceCover (g ∘ h) (n + m)`.
Monotonicity is essential — each cut value of the outer `g` is reached by `h` on a single
upward ray (so cuts cannot multiply). Iterating gives the headline contrast to
`DepthSeparation`'s tent:

  **`hasPieceCover_iterate`** — a monotone map with `k` pieces, composed with itself `d`
  times, has at most `d·k + 1` pieces: **linear in depth**.

The (non-monotone) tent `T` has `2^d` pieces under the same iteration (`DepthSeparation`),
so monotone depth is region-polynomial while cancellation depth is region-exponential — the
quantitative form of N-1 on the 1-D depth axis. The remaining wiring to a fully general
`isMono_regions_poly` over arbitrary `IsMono` circuits is the per-gate (`+`, `max`, `scale`)
piece lemmas over `Trop`; the composition/iteration core is here.
-/
import Mathlib.Order.Iterate
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Sundog.PieceCover

/-- `f` agrees with a single affine function `x ↦ p·x + q` on the closed interval `[a,b]`. -/
def LineOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ p q : ℝ, ∀ x ∈ Set.Icc a b, f x = p * x + q

/-- `f` is affine on every interval whose **interior** avoids the finite cut set `S`. -/
def AffineAway (f : ℝ → ℝ) (S : Finset ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → (∀ s ∈ S, s ∉ Set.Ioo a b) → LineOn f a b

/-- **Bounded piece certificate.** `f` is covered by at most `k` affine pieces: there is a
cut set of cardinality `≤ k - 1` off whose interior `f` is affine. An upper bound on the
linear-region count, with no exact chamber-count object. -/
def HasPieceCover (f : ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ S : Finset ℝ, S.card + 1 ≤ k ∧ AffineAway f S

/-- A piece certificate weakens to any larger bound. -/
theorem hasPieceCover_mono_le {f : ℝ → ℝ} {n n' : ℕ}
    (h : HasPieceCover f n) (hle : n ≤ n') : HasPieceCover f n' := by
  obtain ⟨S, hcard, haff⟩ := h
  exact ⟨S, le_trans hcard hle, haff⟩

/-- A constant function is a single affine piece. -/
theorem hasPieceCover_const (c : ℝ) : HasPieceCover (fun _ => c) 1 :=
  ⟨∅, by simp, fun _ _ _ _ => ⟨0, c, by intro x _; simp⟩⟩

/-- The identity is a single affine piece. -/
theorem hasPieceCover_id : HasPieceCover (id : ℝ → ℝ) 1 :=
  ⟨∅, by simp, fun _ _ _ _ => ⟨1, 0, by intro x _; simp⟩⟩

/-- The global "first crossing" of level `β` by `h`: the infimum of where `h` reaches `β`.
For a monotone `h`, the super-level set `{x | β ≤ h x}` is an upward ray, so this is the
single point at which `h` crosses `β`. -/
noncomputable def crossing (h : ℝ → ℝ) (β : ℝ) : ℝ := sInf {x : ℝ | β ≤ h x}

/-- **Monotone composition bound (the load-bearing lemma).** Composing a monotone inner
map `h` with `g` *adds* pieces: the cuts of `g ∘ h` are the cuts of `h` together with one
crossing per cut of `g`. Monotonicity is what makes this additive rather than multiplicative
— each cut value of `g` is reached by `h` on a single upward ray, so crossings cannot
multiply (the folding that would multiply them is exactly non-monotonicity). -/
theorem hasPieceCover_comp_mono {g h : ℝ → ℝ} {n m : ℕ}
    (hh : HasPieceCover h n) (hg : HasPieceCover g m) (hmono : Monotone h) :
    HasPieceCover (g ∘ h) (n + m) := by
  obtain ⟨Sh, hSh_card, hSh⟩ := hh
  obtain ⟨Sg, hSg_card, hSg⟩ := hg
  refine ⟨Sh ∪ Sg.image (crossing h), ?_, ?_⟩
  · -- cardinality: |Sh ∪ image| ≤ |Sh| + |Sg|, so the cover stays `≤ n + m`
    have h1 : (Sh ∪ Sg.image (crossing h)).card ≤ Sh.card + (Sg.image (crossing h)).card :=
      Finset.card_union_le _ _
    have h2 : (Sg.image (crossing h)).card ≤ Sg.card := Finset.card_image_le
    omega
  · -- affine away from the combined cut set
    intro a b hab hmiss
    rcases eq_or_lt_of_le hab with rfl | hab'
    · -- degenerate interval [a,a]: a single point is trivially affine
      exact ⟨0, (g ∘ h) a, by
        intro x hx; simp only [Set.mem_Icc] at hx
        have hxa : x = a := le_antisymm hx.2 hx.1; subst hxa; simp⟩
    · -- a < b
      -- the interval misses Sh ⇒ h is a single line on [a,b]
      have hmissSh : ∀ s ∈ Sh, s ∉ Set.Ioo a b := fun s hs =>
        hmiss s (Finset.mem_union_left _ hs)
      obtain ⟨p, q, hline⟩ := hSh a b hab hmissSh
      have hha : h a = p * a + q := hline a ⟨le_refl a, le_of_lt hab'⟩
      have hhb : h b = p * b + q := hline b ⟨le_of_lt hab', le_refl b⟩
      have hab_h : h a ≤ h b := hmono (le_of_lt hab')
      -- KEY: the image interval (h a, h b) misses Sg
      have hmissSg : ∀ β ∈ Sg, β ∉ Set.Ioo (h a) (h b) := by
        intro β hβ hβmem
        rw [Set.mem_Ioo] at hβmem
        obtain ⟨hβ1, hβ2⟩ := hβmem
        -- a strict gap forces the line to rise: p > 0
        have hlt_hab : h a < h b := lt_trans hβ1 hβ2
        have hpos : 0 < p := by
          have hpapb : p * a < p * b := by linarith [hha, hhb, hlt_hab]
          by_contra hp; push_neg at hp
          have hle : p * b ≤ p * a := mul_le_mul_of_nonpos_left (le_of_lt hab') hp
          linarith
        have hpne : p ≠ 0 := ne_of_gt hpos
        set c := (β - q) / p with hc
        have hcval : p * c + q = β := by rw [hc]; field_simp
        -- the crossing point c lies strictly inside (a,b)
        have hca : a < c := by
          have : p * a < p * c := by linarith [hha, hβ1, hcval]
          exact (mul_lt_mul_left hpos).mp this
        have hcb : c < b := by
          have : p * c < p * b := by linarith [hhb, hβ2, hcval]
          exact (mul_lt_mul_left hpos).mp this
        -- monotonicity pins the super-level set to the ray [c, ∞)
        have hset : {x : ℝ | β ≤ h x} = Set.Ici c := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_Ici]
          constructor
          · intro hx
            by_contra hlt; push_neg at hlt
            have hxlt : h x < β := by
              rcases le_or_lt x a with hxa | hax
              · linarith [hβ1, hmono hxa]
              · have hxb : x ≤ b := le_of_lt (lt_trans hlt hcb)
                have hxline : h x = p * x + q := hline x ⟨le_of_lt hax, hxb⟩
                have hmul : p * x < p * c := (mul_lt_mul_left hpos).mpr hlt
                linarith [hxline, hmul, hcval]
            linarith [hx, hxlt]
          · intro hx
            rcases le_or_lt x b with hxb | hbx
            · have hax : a ≤ x := le_of_lt (lt_of_lt_of_le hca hx)
              have hxline : h x = p * x + q := hline x ⟨hax, hxb⟩
              have hmul : p * c ≤ p * x := (mul_le_mul_left hpos).mpr hx
              linarith [hxline, hmul, hcval]
            · linarith [hβ2, hmono (le_of_lt hbx)]
        -- so crossing h β = c, and c is a cut in (a,b) — contradicting hmiss
        have hcross : crossing h β = c := by unfold crossing; rw [hset]; exact csInf_Ici
        have hmem_c : c ∈ Set.Ioo a b := ⟨hca, hcb⟩
        have hT : crossing h β ∈ Sg.image (crossing h) := Finset.mem_image_of_mem _ hβ
        have hnotin : crossing h β ∉ Set.Ioo a b :=
          hmiss (crossing h β) (Finset.mem_union_right _ hT)
        rw [hcross] at hnotin
        exact hnotin hmem_c
      -- (h a, h b) misses Sg ⇒ g is a single line there ⇒ g ∘ h is a single line on [a,b]
      obtain ⟨p', q', gline⟩ := hSg (h a) (h b) hab_h hmissSg
      refine ⟨p' * p, p' * q + q', ?_⟩
      intro x hx
      simp only [Set.mem_Icc] at hx
      have hxline : h x = p * x + q := hline x ⟨hx.1, hx.2⟩
      have hxrange : h x ∈ Set.Icc (h a) (h b) := ⟨hmono hx.1, hmono hx.2⟩
      have hgx : g (h x) = p' * h x + q' := gline (h x) hxrange
      simp only [Function.comp_apply]
      rw [hgx, hxline]; ring

/-- **Headline: monotone depth is region-polynomial.** A monotone map with `k` affine pieces,
composed with itself `d` times, has at most `d·k + 1` affine pieces — **linear in depth**.
Contrast `DepthSeparation`: the (non-monotone) tent has `2^d` pieces under the same iteration.
So folding's exponential expressivity requires cancellation, quantitatively. -/
theorem hasPieceCover_iterate {f : ℝ → ℝ} {k : ℕ}
    (hf : Monotone f) (hk : HasPieceCover f k) :
    ∀ d : ℕ, HasPieceCover (f^[d]) (d * k + 1) := by
  intro d
  induction d with
  | zero => simpa using hasPieceCover_id
  | succ d ih =>
    have hcomp := hasPieceCover_comp_mono ih hk (hf.iterate d)
    rw [Function.iterate_succ' f d]
    have hk_eq : (d + 1) * k + 1 = (d * k + 1) + k := by ring
    rw [hk_eq]
    exact hcomp

end Sundog.PieceCover
