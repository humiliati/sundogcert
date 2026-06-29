/-
# Polynomial region bound for cancellation-free circuits (N-1, circuit-level, TIGHT)

`PieceCover` gave the depth-axis quantitative N-1 (monotone composition is piece-additive,
`d` iterations ⇒ linear). This module lifts that to **arbitrary `IsMono` (cancellation-free)
circuits** with a *tight* (polynomial) region bound, using convexity.

The pipeline:

* **`isMono_realize1_convexOn`** — the bridge: every `IsMono` circuit's 1-D realization is
  **convex** (`var`/`const`/`add`/nonneg-`scale`/`max` all preserve `ConvexOn`). This is the
  fact that makes `max` *piece-additive* rather than piece-doubling.
* **`hasPieceCover_add` / `hasPieceCover_smul`** — the cut-based gates (no convexity needed):
  `+` is piece-additive (`n + m`), scaling preserves the cut set (`n`).
* **`hasPieceCover_max`** (the crux, convexity) — `max` of two convex functions is
  piece-additive (`n + m`): a convex function with `n` pieces is the max of its `n` piece
  lines, and the upper envelope of `N` lines has `≤ N` pieces (adding a line to a convex
  envelope replaces a single interval). Without convexity `max` would double.
* **`isMono_hasPieceCover`** — the payoff: `IsMono e → HasPieceCover (realize1 e) (leafCount e)`,
  i.e. the region count is **linear in circuit size**. Polynomial, where the (cancellation-using)
  tent is `2^d` for circuit size `O(d)` along the composition axis.
-/
import Sundogcert.PieceCover
import Sundogcert.RegionCount
import Sundogcert.CancellationFree
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Slope

namespace Sundog.RegionPoly

open Sundog.CircuitNet Sundog.RegionCount Sundog.CancellationFree Sundog.PieceCover

/-! ### `realize1` unfolds per constructor -/

@[simp] theorem realize1_var (i : Fin 1) : realize1 (Trop.var i) = id := by
  funext t; simp [realize1]

@[simp] theorem realize1_const (c : ℝ) : realize1 (Trop.const c : Trop 1) = fun _ => c := by
  funext t; simp [realize1]

@[simp] theorem realize1_add (a b : Trop 1) :
    realize1 (Trop.add a b) = fun t => realize1 a t + realize1 b t := by
  funext t; simp [realize1]

@[simp] theorem realize1_scale (c : ℝ) (a : Trop 1) :
    realize1 (Trop.scale c a) = fun t => c * realize1 a t := by
  funext t; simp [realize1]

@[simp] theorem realize1_max (a b : Trop 1) :
    realize1 (Trop.max a b) = fun t => max (realize1 a t) (realize1 b t) := by
  funext t; simp [realize1]

/-! ### The convexity bridge -/

/-- **Every cancellation-free circuit realizes a convex function.** The reason `max` is
piece-additive (not piece-doubling) downstream. -/
theorem isMono_realize1_convexOn {e : Trop 1} (h : IsMono e) :
    ConvexOn ℝ Set.univ (realize1 e) := by
  induction e with
  | var i => rw [realize1_var]; exact convexOn_id convex_univ
  | const c => rw [realize1_const]; exact convexOn_const _ convex_univ
  | add a b iha ihb => rw [realize1_add]; exact (iha h.1).add (ihb h.2)
  | scale c a ih =>
    rw [realize1_scale]
    simpa [smul_eq_mul] using (ih h.2).smul h.1
  | max a b iha ihb =>
    rw [realize1_max]
    exact (iha h.1).sup (ihb h.2)

/-! ### The cut-based gates (no convexity) -/

/-- `+` is piece-additive: cuts of `f + g` are the union of the cuts. -/
theorem hasPieceCover_add {f g : ℝ → ℝ} {n m : ℕ}
    (hf : HasPieceCover f n) (hg : HasPieceCover g m) :
    HasPieceCover (fun x => f x + g x) (n + m) := by
  obtain ⟨Sf, hcf, haf⟩ := hf
  obtain ⟨Sg, hcg, hag⟩ := hg
  refine ⟨Sf ∪ Sg, ?_, ?_⟩
  · have := Finset.card_union_le Sf Sg; omega
  · intro a b hab hmiss
    have hmf : ∀ s ∈ Sf, s ∉ Set.Ioo a b := fun s hs => hmiss s (Finset.mem_union_left _ hs)
    have hmg : ∀ s ∈ Sg, s ∉ Set.Ioo a b := fun s hs => hmiss s (Finset.mem_union_right _ hs)
    obtain ⟨pf, qf, hlf⟩ := haf a b hab hmf
    obtain ⟨pg, qg, hlg⟩ := hag a b hab hmg
    exact ⟨pf + pg, qf + qg, by
      intro x hx; change f x + g x = (pf + pg) * x + (qf + qg)
      rw [hlf x hx, hlg x hx]; ring⟩

/-- Scaling preserves the cut set (and hence the piece count). -/
theorem hasPieceCover_smul {f : ℝ → ℝ} {n : ℕ} (c : ℝ) (hf : HasPieceCover f n) :
    HasPieceCover (fun x => c * f x) n := by
  obtain ⟨S, hc, ha⟩ := hf
  refine ⟨S, hc, ?_⟩
  intro a b hab hmiss
  obtain ⟨p, q, hl⟩ := ha a b hab hmiss
  exact ⟨c * p, c * q, by
    intro x hx; change c * f x = c * p * x + c * q
    rw [hl x hx]; ring⟩

/-! ### The crux: `max` is piece-additive for convex functions (via the convex merge) -/

/-- **(B) Adding one line to a convex function adds at most one piece.** `{x | h x ≤ ℓ x}`
is an interval (sublevel set of the convex `h − ℓ`), so the line wins on a single stretch;
the `+1` (not `+2`) in the bounded case is the convex-merge absorption — a convex `h` that
dips below `ℓ` and returns must change slope inside, i.e. carry a breakpoint there. -/
theorem hasPieceCover_max_line {h : ℝ → ℝ} {k : ℕ} (p q : ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hpc : HasPieceCover h k) :
    HasPieceCover (fun x => max (p * x + q) (h x)) (k + 1) := by
  obtain ⟨S, hScard, hAff⟩ := hpc
  by_cases hGne : ∃ x, h x ≤ p * x + q
  · -- agreement region nonempty
    obtain ⟨x0, hx0⟩ := hGne
    have hcont : Continuous h := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
    -- the agreement region G = {x | h x ≤ ℓ x} is order-connected (h convex, ℓ affine)
    have hGconn : Set.OrdConnected {x : ℝ | h x ≤ p * x + q} := by
      constructor
      intro x hx y hy z hz
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      obtain ⟨hxz, hzy⟩ := hz
      rcases eq_or_lt_of_le hxz with rfl | hxz'
      · exact hx
      · rcases eq_or_lt_of_le hzy with rfl | hzy'
        · exact hy
        · have hxy : (0 : ℝ) < y - x := by linarith
          have hne : y - x ≠ 0 := ne_of_gt hxy
          set a := (y - z) / (y - x) with ha
          set b := (z - x) / (y - x) with hb
          have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg <;> linarith
          have hb0 : 0 ≤ b := by rw [hb]; apply div_nonneg <;> linarith
          have hab : a + b = 1 := by
            rw [ha, hb, ← add_div, div_eq_one_iff_eq hne]; ring
          have hcombo : a * x + b * y = z := by rw [ha, hb]; field_simp; ring
          have hjensen := hconv.2 (Set.mem_univ x) (Set.mem_univ y) ha0 hb0 hab
          simp only [smul_eq_mul] at hjensen
          rw [hcombo] at hjensen
          have hub : a * h x + b * h y ≤ a * (p * x + q) + b * (p * y + q) :=
            add_le_add (mul_le_mul_of_nonneg_left hx ha0) (mul_le_mul_of_nonneg_left hy hb0)
          have heq : a * (p * x + q) + b * (p * y + q) = p * z + q := by
            linear_combination p * hcombo + q * hab
          linarith [hjensen, hub, heq]
    have hGcl : IsClosed {x : ℝ | h x ≤ p * x + q} := isClosed_le hcont (by fun_prop)
    have hGne' : {x : ℝ | h x ≤ p * x + q}.Nonempty := ⟨x0, hx0⟩
    by_cases hbb : BddBelow {x : ℝ | h x ≤ p * x + q}
    · by_cases hba : BddAbove {x : ℝ | h x ≤ p * x + q}
      · -- bounded interval [α, β]: the convex-merge absorption case
        classical
        set α := sInf {x : ℝ | h x ≤ p * x + q} with hαdef
        set β := sSup {x : ℝ | h x ≤ p * x + q} with hβdef
        have hαG : h α ≤ p * α + q := hGcl.csInf_mem hGne' hbb
        have hβG : h β ≤ p * β + q := hGcl.csSup_mem hGne' hba
        have hαlb : ∀ g, h g ≤ p * g + q → α ≤ g := fun g hg => csInf_le hbb hg
        have hβub : ∀ g, h g ≤ p * g + q → g ≤ β := fun g hg => le_csSup hba hg
        have hαβ : α ≤ β := le_trans (hαlb x0 hx0) (hβub x0 hx0)
        have hleftstrict : ∀ x, x < α → p * x + q < h x := by
          intro x hxα; by_contra hc; rw [not_lt] at hc
          exact absurd (hαlb x hc) (not_le.mpr hxα)
        have hrightstrict : ∀ x, β < x → p * x + q < h x := by
          intro x hxβ; by_contra hc; rw [not_lt] at hc
          exact absurd (hβub x hc) (not_le.mpr hxβ)
        have hbdryα : p * α + q ≤ h α := by
          have hsub : Set.Iio α ⊆ {x : ℝ | p * x + q ≤ h x} :=
            fun x hx => le_of_lt (hleftstrict x hx)
          have hcl2 : IsClosed {x : ℝ | p * x + q ≤ h x} := isClosed_le (by fun_prop) hcont
          have hαcl : α ∈ closure (Set.Iio α) := by rw [closure_Iio]; exact le_refl α
          have hmono := closure_mono hsub; rw [hcl2.closure_eq] at hmono; exact hmono hαcl
        have hbdryβ : p * β + q ≤ h β := by
          have hsub : Set.Ioi β ⊆ {x : ℝ | p * x + q ≤ h x} :=
            fun x hx => le_of_lt (hrightstrict x hx)
          have hcl2 : IsClosed {x : ℝ | p * x + q ≤ h x} := isClosed_le (by fun_prop) hcont
          have hβcl : β ∈ closure (Set.Ioi β) := by rw [closure_Ioi]; exact le_refl β
          have hmono := closure_mono hsub; rw [hcl2.closure_eq] at hmono; exact hmono hβcl
        have hmid : ∀ x, α ≤ x → x ≤ β → h x ≤ p * x + q := fun x hxα hxβ =>
          hGconn.out hαG hβG ⟨hxα, hxβ⟩
        have hleft : ∀ x, x ≤ α → p * x + q ≤ h x := by
          intro x hxα; rcases eq_or_lt_of_le hxα with rfl | hlt
          · exact hbdryα
          · exact le_of_lt (hleftstrict x hlt)
        have hright : ∀ x, β ≤ x → p * x + q ≤ h x := by
          intro x hxβ; rcases eq_or_lt_of_le hxβ with rfl | hlt
          · exact hbdryβ
          · exact le_of_lt (hrightstrict x hlt)
        by_cases hSin : (S.filter (fun s => α < s ∧ s < β)).Nonempty
        · -- absorption: there is an h-breakpoint inside (α,β)
          refine ⟨insert α (insert β (S.filter (fun s => ¬(α < s ∧ s < β)))), ?_, ?_⟩
          · have hpart := Finset.card_filter_add_card_filter_not (s := S)
              (p := fun s => α < s ∧ s < β)
            have hinpos := hSin.card_pos
            have hc1 := Finset.card_insert_le α (insert β (S.filter (fun s => ¬(α < s ∧ s < β))))
            have hc2 := Finset.card_insert_le β (S.filter (fun s => ¬(α < s ∧ s < β)))
            omega
          · intro a b hab hmiss
            have hαnotin : α ∉ Set.Ioo a b := hmiss α (Finset.mem_insert_self _ _)
            have hβnotin : β ∉ Set.Ioo a b :=
              hmiss β (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            have hToutmiss : ∀ s ∈ S, ¬(α < s ∧ s < β) → s ∉ Set.Ioo a b := fun s hs hout =>
              hmiss s (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_filter.mpr ⟨hs, hout⟩)))
            by_cases hbα : b ≤ α
            · have hSmiss : ∀ s ∈ S, s ∉ Set.Ioo a b := by
                intro s hs
                by_cases hsout : α < s ∧ s < β
                · intro hsin
                  exact absurd (lt_of_le_of_lt hbα hsout.1) (not_lt.mpr (le_of_lt hsin.2))
                · exact hToutmiss s hs hsout
              obtain ⟨ph, qh, hhl⟩ := hAff a b hab hSmiss
              refine ⟨ph, qh, fun x hx => ?_⟩
              have hxα : x ≤ α := le_trans hx.2 hbα
              change max (p * x + q) (h x) = ph * x + qh
              rw [max_eq_right (hleft x hxα), hhl x hx]
            · have hαb : α < b := not_le.mp hbα
              have hαa : α ≤ a := by by_contra hc; rw [not_le] at hc; exact hαnotin ⟨hc, hαb⟩
              by_cases hbβ : b ≤ β
              · refine ⟨p, q, fun x hx => ?_⟩
                have hxα : α ≤ x := le_trans hαa hx.1
                have hxβ : x ≤ β := le_trans hx.2 hbβ
                change max (p * x + q) (h x) = p * x + q
                exact max_eq_left (hmid x hxα hxβ)
              · have hβb : β < b := not_le.mp hbβ
                have hβa : β ≤ a := by by_contra hc; rw [not_le] at hc; exact hβnotin ⟨hc, hβb⟩
                have hSmiss : ∀ s ∈ S, s ∉ Set.Ioo a b := by
                  intro s hs
                  by_cases hsout : α < s ∧ s < β
                  · intro hsin
                    exact absurd (lt_of_lt_of_le hsout.2 hβa) (not_lt.mpr (le_of_lt hsin.1))
                  · exact hToutmiss s hs hsout
                obtain ⟨ph, qh, hhl⟩ := hAff a b hab hSmiss
                refine ⟨ph, qh, fun x hx => ?_⟩
                have hxβ : β ≤ x := le_trans hβa hx.1
                change max (p * x + q) (h x) = ph * x + qh
                rw [max_eq_right (hright x hxβ), hhl x hx]
        · -- no inside breakpoint: h = ℓ on [α,β], so max = h everywhere
          have hmidS : ∀ s ∈ S, s ∉ Set.Ioo α β := by
            intro s hs hsin
            exact hSin ⟨s, Finset.mem_filter.mpr ⟨hs, hsin.1, hsin.2⟩⟩
          obtain ⟨ph, qh, hhl⟩ := hAff α β hαβ hmidS
          have heqαβ : ∀ x, α ≤ x → x ≤ β → p * x + q ≤ h x := by
            intro x hxα hxβ
            rcases eq_or_lt_of_le hαβ with hαβe | hαβlt
            · have hxeq : x = α := le_antisymm (hαβe ▸ hxβ) hxα
              subst hxeq; exact hleft α (le_refl α)
            · have hhα : h α = ph * α + qh := hhl α ⟨le_refl α, hαβ⟩
              have hhβ : h β = ph * β + qh := hhl β ⟨hαβ, le_refl β⟩
              have heα : ph * α + qh = p * α + q := by rw [← hhα]; linarith [hbdryα, hαG]
              have heβ : ph * β + qh = p * β + q := by rw [← hhβ]; linarith [hbdryβ, hβG]
              have hph : ph = p := by
                have hz : (ph - p) * (β - α) = 0 := by linear_combination heβ - heα
                rcases mul_eq_zero.mp hz with h1 | h2
                · linarith
                · exfalso; linarith
              have hqh : qh = q := by have h3 := heα; rw [hph] at h3; linarith
              rw [hhl x ⟨hxα, hxβ⟩, hph, hqh]
          refine ⟨S, by omega, fun a b hab hSm => ?_⟩
          obtain ⟨ph2, qh2, hhl2⟩ := hAff a b hab hSm
          refine ⟨ph2, qh2, fun x hx => ?_⟩
          change max (p * x + q) (h x) = ph2 * x + qh2
          have hle : p * x + q ≤ h x := by
            by_cases hxα : x ≤ α
            · exact hleft x hxα
            · by_cases hxβ : β ≤ x
              · exact hright x hxβ
              · exact heqαβ x (le_of_lt (not_le.mp hxα)) (le_of_lt (not_le.mp hxβ))
          rw [max_eq_right hle, hhl2 x hx]
      · -- ray [α, ∞): max = h left of α, ℓ right of α
        set α := sInf {x : ℝ | h x ≤ p * x + q} with hαdef
        have hαG : h α ≤ p * α + q := hGcl.csInf_mem hGne' hbb
        have hαlb : ∀ g, h g ≤ p * g + q → α ≤ g := fun g hg => csInf_le hbb hg
        have hleftstrict : ∀ x, x < α → p * x + q < h x := by
          intro x hxα
          by_contra hc
          rw [not_lt] at hc
          exact absurd (hαlb x hc) (not_le.mpr hxα)
        have hbdry : p * α + q ≤ h α := by
          have hsub : Set.Iio α ⊆ {x : ℝ | p * x + q ≤ h x} :=
            fun x hx => le_of_lt (hleftstrict x hx)
          have hcl2 : IsClosed {x : ℝ | p * x + q ≤ h x} := isClosed_le (by fun_prop) hcont
          have hαcl : α ∈ closure (Set.Iio α) := by rw [closure_Iio]; exact le_refl α
          have hmono := closure_mono hsub
          rw [hcl2.closure_eq] at hmono
          exact hmono hαcl
        have hright : ∀ x, α ≤ x → h x ≤ p * x + q := by
          intro x hxα
          obtain ⟨y, hy, hxy⟩ := (not_bddAbove_iff).mp hba x
          exact hGconn.out hαG hy ⟨hxα, le_of_lt hxy⟩
        have hleft : ∀ x, x ≤ α → p * x + q ≤ h x := by
          intro x hxα
          rcases eq_or_lt_of_le hxα with rfl | hlt
          · exact hbdry
          · exact le_of_lt (hleftstrict x hlt)
        refine ⟨insert α S, ?_, ?_⟩
        · have := Finset.card_insert_le α S; omega
        · intro a b hab hmiss
          have hαnotin : α ∉ Set.Ioo a b := hmiss α (Finset.mem_insert_self α S)
          have hSmiss : ∀ s ∈ S, s ∉ Set.Ioo a b := fun s hs =>
            hmiss s (Finset.mem_insert_of_mem hs)
          by_cases hbα : b ≤ α
          · obtain ⟨ph, qh, hhl⟩ := hAff a b hab hSmiss
            refine ⟨ph, qh, fun x hx => ?_⟩
            have hxα : x ≤ α := le_trans hx.2 hbα
            change max (p * x + q) (h x) = ph * x + qh
            rw [max_eq_right (hleft x hxα), hhl x hx]
          · have hαb : α < b := not_le.mp hbα
            have hαa : α ≤ a := by
              by_contra hc
              rw [not_le] at hc
              exact hαnotin ⟨hc, hαb⟩
            refine ⟨p, q, fun x hx => ?_⟩
            have hαx : α ≤ x := le_trans hαa hx.1
            change max (p * x + q) (h x) = p * x + q
            exact max_eq_left (hright x hαx)
    · by_cases hba : BddAbove {x : ℝ | h x ≤ p * x + q}
      · -- ray (-∞, β]: max = ℓ left of β, h right of β
        set β := sSup {x : ℝ | h x ≤ p * x + q} with hβdef
        have hβG : h β ≤ p * β + q := hGcl.csSup_mem hGne' hba
        have hβub : ∀ g, h g ≤ p * g + q → g ≤ β := fun g hg => le_csSup hba hg
        have hrightstrict : ∀ x, β < x → p * x + q < h x := by
          intro x hxβ
          by_contra hc
          rw [not_lt] at hc
          exact absurd (hβub x hc) (not_le.mpr hxβ)
        have hbdry : p * β + q ≤ h β := by
          have hsub : Set.Ioi β ⊆ {x : ℝ | p * x + q ≤ h x} :=
            fun x hx => le_of_lt (hrightstrict x hx)
          have hcl2 : IsClosed {x : ℝ | p * x + q ≤ h x} := isClosed_le (by fun_prop) hcont
          have hβcl : β ∈ closure (Set.Ioi β) := by rw [closure_Ioi]; exact le_refl β
          have hmono := closure_mono hsub
          rw [hcl2.closure_eq] at hmono
          exact hmono hβcl
        have hleftG : ∀ x, x ≤ β → h x ≤ p * x + q := by
          intro x hxβ
          obtain ⟨y, hy, hyx⟩ := (not_bddBelow_iff).mp hbb x
          exact hGconn.out hy hβG ⟨le_of_lt hyx, hxβ⟩
        have hrightge : ∀ x, β ≤ x → p * x + q ≤ h x := by
          intro x hxβ
          rcases eq_or_lt_of_le hxβ with rfl | hlt
          · exact hbdry
          · exact le_of_lt (hrightstrict x hlt)
        refine ⟨insert β S, ?_, ?_⟩
        · have := Finset.card_insert_le β S; omega
        · intro a b hab hmiss
          have hβnotin : β ∉ Set.Ioo a b := hmiss β (Finset.mem_insert_self β S)
          have hSmiss : ∀ s ∈ S, s ∉ Set.Ioo a b := fun s hs =>
            hmiss s (Finset.mem_insert_of_mem hs)
          by_cases hbβ : b ≤ β
          · refine ⟨p, q, fun x hx => ?_⟩
            have hxβ : x ≤ β := le_trans hx.2 hbβ
            change max (p * x + q) (h x) = p * x + q
            exact max_eq_left (hleftG x hxβ)
          · have hβb : β < b := not_le.mp hbβ
            have hβa : β ≤ a := by
              by_contra hc
              rw [not_le] at hc
              exact hβnotin ⟨hc, hβb⟩
            obtain ⟨ph, qh, hhl⟩ := hAff a b hab hSmiss
            refine ⟨ph, qh, fun x hx => ?_⟩
            have hβx : β ≤ x := le_trans hβa hx.1
            change max (p * x + q) (h x) = ph * x + qh
            rw [max_eq_right (hrightge x hβx), hhl x hx]
      · -- G = univ: max = ℓ everywhere
        have hGu : ∀ z : ℝ, h z ≤ p * z + q := by
          intro z
          obtain ⟨x1, hx1, hx1z⟩ := (not_bddBelow_iff).mp hbb z
          obtain ⟨y1, hy1, hzy1⟩ := (not_bddAbove_iff).mp hba z
          have : z ∈ {x : ℝ | h x ≤ p * x + q} :=
            hGconn.out hx1 hy1 ⟨le_of_lt hx1z, le_of_lt hzy1⟩
          exact this
        refine ⟨∅, by rw [Finset.card_empty]; omega, fun a b hab _ => ⟨p, q, fun x _ => ?_⟩⟩
        change max (p * x + q) (h x) = p * x + q
        exact max_eq_left (hGu x)
  · -- line never reaches h: max = h everywhere
    simp only [not_exists, not_le] at hGne
    refine ⟨S, by omega, fun a b hab hmiss => ?_⟩
    obtain ⟨pp, qq, hl⟩ := hAff a b hab hmiss
    exact ⟨pp, qq, fun x hx => by
      change max (p * x + q) (h x) = pp * x + qq
      rw [max_eq_right (le_of_lt (hGne x)), hl x hx]⟩

/-- **Supporting line.** A convex function lies above any line it equals on a (nondegenerate)
interval `[s,t]` — the line of a piece is a global lower bound. (Convexity via slope
monotonicity.) This is what lets a convex function be written as the `max` of its piece-lines. -/
theorem lineBelow {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {s t p q : ℝ}
    (hst : s < t) (hline : ∀ x ∈ Set.Icc s t, f x = p * x + q) (w : ℝ) :
    p * w + q ≤ f w := by
  have hfs : f s = p * s + q := hline s ⟨le_refl s, le_of_lt hst⟩
  have hft : f t = p * t + q := hline t ⟨le_of_lt hst, le_refl t⟩
  have hts : (0 : ℝ) < t - s := by linarith
  have hp : (f t - f s) / (t - s) = p := by
    rw [hfs, hft, show p * t + q - (p * s + q) = p * (t - s) by ring,
      mul_div_assoc, div_self hts.ne', mul_one]
  rcases lt_trichotomy w s with hws | hws | hws
  · have hsl := ConvexOn.slope_mono_adjacent hf (Set.mem_univ w) (Set.mem_univ t) hws hst
    rw [hp] at hsl
    have hsw : (0 : ℝ) < s - w := by linarith
    rw [div_le_iff₀ hsw, hfs] at hsl
    nlinarith [hsl]
  · subst hws; rw [hfs]
  · by_cases hwt : w ≤ t
    · rw [hline w ⟨le_of_lt hws, hwt⟩]
    · have hwt' : t < w := not_le.mp hwt
      have hsl := ConvexOn.slope_mono_adjacent hf (Set.mem_univ s) (Set.mem_univ w) hst hwt'
      rw [hp] at hsl
      have htw : (0 : ℝ) < w - t := by linarith
      rw [le_div_iff₀ htw, hft] at hsl
      nlinarith [hsl]

/-- **(A) A convex `HasPieceCover`-`n` function is the max of `≤ n` lines.** Stated via the
two halves of "`f = sup L`": every line in `L` is `≤ f` (supporting, `lineBelow`), and every
point achieves some line of `L` (its piece line). The line set is the secants on the cut-set
pieces. -/
theorem convex_eq_sup_lines {f : ℝ → ℝ} {n : ℕ} (hf : ConvexOn ℝ Set.univ f)
    (hpc : HasPieceCover f n) :
    ∃ L : Finset (ℝ × ℝ), L.card ≤ n ∧
      (∀ pr ∈ L, ∀ x, pr.1 * x + pr.2 ≤ f x) ∧
      (∀ x, ∃ pr ∈ L, f x = pr.1 * x + pr.2) := by
  classical
  obtain ⟨S, hScard, hAff⟩ := hpc
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · -- no cuts: `f` is a single global line
    subst hSe
    have hg : ∀ x, f x = (f 1 - f 0) * x + f 0 := by
      intro x
      have hle : min x 0 ≤ max x 1 := le_trans (min_le_left x 0) (le_max_left x 1)
      obtain ⟨p, q, hpq⟩ := hAff (min x 0) (max x 1) hle (by simp)
      have h0 : f 0 = p * 0 + q :=
        hpq 0 ⟨min_le_right x 0, le_trans (by norm_num) (le_max_right x 1)⟩
      have h1 : f 1 = p * 1 + q :=
        hpq 1 ⟨le_trans (min_le_right x 0) (by norm_num), le_max_right x 1⟩
      have hx : f x = p * x + q := hpq x ⟨min_le_left x 0, le_max_left x 1⟩
      rw [hx, h0, h1]; ring
    refine ⟨{(f 1 - f 0, f 0)}, ?_, ?_, ?_⟩
    · rw [Finset.card_singleton]
      simp only [Finset.card_empty] at hScard; omega
    · intro pr hpr y
      rw [Finset.mem_singleton] at hpr; subst hpr
      exact le_of_eq (hg y).symm
    · intro x; exact ⟨_, Finset.mem_singleton_self _, hg x⟩
  · -- smallest cut strictly above `a`, else `a + 1`
    set nextCut : ℝ → ℝ :=
      fun a => if h : (S.filter (a < ·)).Nonempty then (S.filter (a < ·)).min' h else a + 1
      with hnc
    -- secant of `f` on the piece `[a, nextCut a]`
    set lineOf : ℝ → ℝ × ℝ :=
      fun a => ((f (nextCut a) - f a) / (nextCut a - a),
        f a - (f (nextCut a) - f a) / (nextCut a - a) * a) with hlo
    -- `nextCut a` is strictly above `a`
    have hlt : ∀ a, a < nextCut a := by
      intro a; simp only [hnc]
      by_cases h : (S.filter (a < ·)).Nonempty
      · rw [dif_pos h]; exact (Finset.mem_filter.mp ((S.filter (a < ·)).min'_mem h)).2
      · rw [dif_neg h]; linarith
    -- no cut lies strictly inside the piece `(a, nextCut a)`
    have hmissAt : ∀ a, ∀ s ∈ S, s ∉ Set.Ioo a (nextCut a) := by
      intro a s hs hsin; simp only [hnc] at hsin
      by_cases h : (S.filter (a < ·)).Nonempty
      · rw [dif_pos h] at hsin
        have hle := Finset.min'_le (S.filter (a < ·)) s (Finset.mem_filter.mpr ⟨hs, hsin.1⟩)
        linarith [hsin.2, hle]
      · exact h ⟨s, Finset.mem_filter.mpr ⟨hs, hsin.1⟩⟩
    -- `f` equals its secant `lineOf a` on the piece `[a, nextCut a]`
    have hpiece : ∀ a, ∀ y ∈ Set.Icc a (nextCut a),
        f y = (lineOf a).1 * y + (lineOf a).2 := by
      intro a y hy
      obtain ⟨p, q, hpq⟩ := hAff a (nextCut a) (le_of_lt (hlt a)) (hmissAt a)
      have hfa : f a = p * a + q := hpq a ⟨le_refl a, le_of_lt (hlt a)⟩
      have hfn : f (nextCut a) = p * nextCut a + q := hpq (nextCut a) ⟨le_of_lt (hlt a), le_refl _⟩
      have hfy : f y = p * y + q := hpq y hy
      have hslope : (f (nextCut a) - f a) / (nextCut a - a) = p := by
        rw [hfa, hfn, show p * nextCut a + q - (p * a + q) = p * (nextCut a - a) by ring,
          mul_div_assoc, div_self (sub_ne_zero.mpr (ne_of_lt (hlt a)).symm), mul_one]
      simp only [hlo]
      rw [hslope, hfa, hfy]; ring
    -- on the unbounded LEFT piece, `f` equals the secant `lineOf (min - 1)`
    have hncm : nextCut (S.min' hSne - 1) = S.min' hSne := by
      simp only [hnc]
      have hne2 : (S.filter (S.min' hSne - 1 < ·)).Nonempty :=
        ⟨S.min' hSne, Finset.mem_filter.mpr ⟨S.min'_mem hSne, by linarith⟩⟩
      rw [dif_pos hne2]
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨S.min'_mem hSne, by linarith⟩)
      · exact Finset.le_min' _ _ _ fun y hy => Finset.min'_le S y (Finset.mem_of_mem_filter y hy)
    have hleftmost : ∀ x, x ≤ S.min' hSne →
        f x = (lineOf (S.min' hSne - 1)).1 * x + (lineOf (S.min' hSne - 1)).2 := by
      intro x hxm
      have hlo_le : min x (S.min' hSne - 1) ≤ S.min' hSne :=
        le_trans (min_le_right _ _) (by linarith)
      have hmiss2 : ∀ s ∈ S, s ∉ Set.Ioo (min x (S.min' hSne - 1)) (S.min' hSne) :=
        fun s hs hsin => by linarith [Finset.min'_le S s hs, hsin.2]
      obtain ⟨p, q, hpq⟩ := hAff (min x (S.min' hSne - 1)) (S.min' hSne) hlo_le hmiss2
      have hfm1 : f (S.min' hSne - 1) = p * (S.min' hSne - 1) + q :=
        hpq _ ⟨min_le_right _ _, by linarith⟩
      have hfm : f (S.min' hSne) = p * S.min' hSne + q := hpq _ ⟨hlo_le, le_refl _⟩
      have hfx : f x = p * x + q := hpq x ⟨min_le_left _ _, hxm⟩
      simp only [hlo, hncm]
      rw [hfm1, hfm, hfx, show S.min' hSne - (S.min' hSne - 1) = 1 by ring]
      simp only [div_one]; ring
    -- on the unbounded RIGHT piece, `f` equals the secant `lineOf (max)`
    have hncM : nextCut (S.max' hSne) = S.max' hSne + 1 := by
      simp only [hnc]
      rw [dif_neg]
      rintro ⟨s, hs⟩
      rw [Finset.mem_filter] at hs
      linarith [Finset.le_max' S s hs.1, hs.2]
    have hrightmost : ∀ x, S.max' hSne ≤ x →
        f x = (lineOf (S.max' hSne)).1 * x + (lineOf (S.max' hSne)).2 := by
      intro x hxM
      have hM_le : S.max' hSne ≤ max x (S.max' hSne + 1) :=
        le_trans (by linarith) (le_max_right _ _)
      have hmiss2 : ∀ s ∈ S, s ∉ Set.Ioo (S.max' hSne) (max x (S.max' hSne + 1)) :=
        fun s hs hsin => by linarith [Finset.le_max' S s hs, hsin.1]
      obtain ⟨p, q, hpq⟩ := hAff (S.max' hSne) (max x (S.max' hSne + 1)) hM_le hmiss2
      have hfM : f (S.max' hSne) = p * S.max' hSne + q := hpq _ ⟨le_refl _, hM_le⟩
      have hfM1 : f (S.max' hSne + 1) = p * (S.max' hSne + 1) + q :=
        hpq _ ⟨by linarith, le_max_right _ _⟩
      have hfx : f x = p * x + q := hpq x ⟨hxM, le_max_left _ _⟩
      simp only [hlo, hncM]
      rw [hfM, hfM1, hfx, show S.max' hSne + 1 - S.max' hSne = 1 by ring]
      simp only [div_one]; ring
    refine ⟨(insert (S.min' hSne - 1) S).image lineOf, ?_, ?_, ?_⟩
    · calc ((insert (S.min' hSne - 1) S).image lineOf).card
            ≤ (insert (S.min' hSne - 1) S).card := Finset.card_image_le
        _ ≤ S.card + 1 := Finset.card_insert_le _ _
        _ ≤ n := by omega
    · intro pr hpr x
      rw [Finset.mem_image] at hpr
      obtain ⟨a, _, rfl⟩ := hpr
      exact lineBelow hf (hlt a) (hpiece a) x
    · intro x
      by_cases hxm : x ≤ S.min' hSne
      · exact ⟨lineOf (S.min' hSne - 1),
          Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _), hleftmost x hxm⟩
      · have hmx : S.min' hSne < x := not_le.mp hxm
        by_cases hxM : S.max' hSne ≤ x
        · exact ⟨lineOf (S.max' hSne),
            Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (S.max'_mem hSne)),
            hrightmost x hxM⟩
        · have hMx : x < S.max' hSne := not_le.mp hxM
          have hfne : (S.filter (· ≤ x)).Nonempty :=
            ⟨S.min' hSne, Finset.mem_filter.mpr ⟨S.min'_mem hSne, le_of_lt hmx⟩⟩
          set a := (S.filter (· ≤ x)).max' hfne with ha
          have ha_mem : a ∈ S := Finset.mem_of_mem_filter a (Finset.max'_mem _ hfne)
          have ha_le : a ≤ x := (Finset.mem_filter.mp (Finset.max'_mem _ hfne)).2
          have hcut_gt : ∀ c ∈ S, a < c → x < c := by
            intro c hc hac
            by_contra hcx; rw [not_lt] at hcx
            exact absurd (Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hc, hcx⟩)) (not_le.mpr hac)
          have hx_lt : x < nextCut a := by
            simp only [hnc]
            by_cases h : (S.filter (a < ·)).Nonempty
            · rw [dif_pos h]
              have hmem := Finset.min'_mem (S.filter (a < ·)) h
              rw [Finset.mem_filter] at hmem
              exact hcut_gt _ hmem.1 hmem.2
            · rw [dif_neg h]
              have hMa : S.max' hSne ≤ a := by
                by_contra hc; rw [not_le] at hc
                exact h ⟨S.max' hSne, Finset.mem_filter.mpr ⟨S.max'_mem hSne, hc⟩⟩
              linarith [hMx, hMa]
          exact ⟨lineOf a, Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem ha_mem),
            hpiece a x ⟨ha_le, le_of_lt hx_lt⟩⟩

/-- Every affine function is convex (used to keep the running envelope convex). -/
theorem affineConvex (c d : ℝ) : ConvexOn ℝ Set.univ (fun x => c * x + d) := by
  refine ⟨convex_univ, fun x _ y _ s t _ _ hst => ?_⟩
  simp only [smul_eq_mul]
  have heq : c * (s * x + t * y) + d = s * (c * x + d) + t * (c * y + d) := by
    linear_combination (-d) * hst
  linarith [heq]

/-- **Convex-convex `max` is piece-additive.** Decompose `a` into its `≤ na` piece-lines (`A`),
then fold the line-add linchpin into `b`: each line adds one piece, so `max a b` has `≤ na + nb`
pieces. This is the gate that needed convexity (cut-based `max` would double). -/
theorem hasPieceCover_max {a b : ℝ → ℝ} {na nb : ℕ}
    (hca : ConvexOn ℝ Set.univ a) (hcb : ConvexOn ℝ Set.univ b)
    (hpa : HasPieceCover a na) (hpb : HasPieceCover b nb) :
    HasPieceCover (fun x => max (a x) (b x)) (na + nb) := by
  classical
  obtain ⟨La, hLcard, hLle, hLach⟩ := convex_eq_sup_lines hca hpa
  -- folding `La` into `b`: `HasPieceCover` and convexity together
  have key : ∀ L : Finset (ℝ × ℝ),
      HasPieceCover (fun x => L.fold max (b x) (fun pr => pr.1 * x + pr.2)) (L.card + nb) ∧
      ConvexOn ℝ Set.univ (fun x => L.fold max (b x) (fun pr => pr.1 * x + pr.2)) := by
    intro L
    induction L using Finset.induction with
    | empty => exact ⟨by simpa using hpb, by simpa using hcb⟩
    | @insert ℓ L hnotin ih =>
      have hfold : (fun x => (insert ℓ L).fold max (b x) (fun pr => pr.1 * x + pr.2))
          = fun x => max (ℓ.1 * x + ℓ.2) (L.fold max (b x) (fun pr => pr.1 * x + pr.2)) := by
        funext x; rw [Finset.fold_insert hnotin]
      rw [hfold, Finset.card_insert_of_notMem hnotin]
      refine ⟨?_, (affineConvex ℓ.1 ℓ.2).sup ih.2⟩
      exact hasPieceCover_mono_le (hasPieceCover_max_line ℓ.1 ℓ.2 ih.2 ih.1) (by omega)
  -- `max a b` equals that fold (`a` is the sup of `La`)
  have heq : (fun x => max (a x) (b x))
      = fun x => La.fold max (b x) (fun pr => pr.1 * x + pr.2) := by
    funext x
    have hbase : ∀ (L : Finset (ℝ × ℝ)), b x ≤ L.fold max (b x) (fun pr => pr.1 * x + pr.2) := by
      intro L
      induction L using Finset.induction with
      | empty => simp
      | @insert ℓ L hnotin ih => rw [Finset.fold_insert hnotin]; exact le_max_of_le_right ih
    have hmem : ∀ (L : Finset (ℝ × ℝ)), ∀ ℓ ∈ L,
        ℓ.1 * x + ℓ.2 ≤ L.fold max (b x) (fun pr => pr.1 * x + pr.2) := by
      intro L
      induction L using Finset.induction with
      | empty => simp
      | @insert ℓ' L hnotin ih =>
        intro ℓ hℓ
        rw [Finset.fold_insert hnotin]
        rw [Finset.mem_insert] at hℓ
        rcases hℓ with rfl | hℓ
        · exact le_max_left _ _
        · exact le_max_of_le_right (ih ℓ hℓ)
    have hub : ∀ (L : Finset (ℝ × ℝ)), (∀ ℓ ∈ L, ℓ.1 * x + ℓ.2 ≤ max (a x) (b x)) →
        L.fold max (b x) (fun pr => pr.1 * x + pr.2) ≤ max (a x) (b x) := by
      intro L
      induction L using Finset.induction with
      | empty => intro _; simp only [Finset.fold_empty]; exact le_max_right _ _
      | @insert ℓ L hnotin ih =>
        intro hall
        rw [Finset.fold_insert hnotin]
        refine max_le (hall ℓ (Finset.mem_insert_self _ _)) (ih ?_)
        exact fun p hp => hall p (Finset.mem_insert_of_mem hp)
    apply le_antisymm
    · refine max_le ?_ (hbase La)
      obtain ⟨ℓ, hℓmem, hℓeq⟩ := hLach x
      rw [hℓeq]; exact hmem La ℓ hℓmem
    · exact hub La (fun ℓ hℓ => le_max_of_le_left (hLle ℓ hℓ x))
  rw [heq]
  exact hasPieceCover_mono_le (key La).1 (by omega)

/-- Number of leaves (`var`/`const` nodes) of a tropical circuit — a proxy for circuit size. -/
def leafCount {n : ℕ} : Trop n → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add a b => leafCount a + leafCount b
  | .scale _ a => leafCount a
  | .max a b => leafCount a + leafCount b

/-- **The payoff (N-1, circuit-level, TIGHT).** Every cancellation-free circuit's 1-D realization
has a linear-region count **linear in the number of leaves** — polynomial in circuit size. The
`max` gate is `n + m` (convex-merge, `hasPieceCover_max`), `add`/`scale` are `n + m` / `n`. Contrast
`DepthSeparation`: the (cancellation-using) tent reaches `2^d` regions. So monotone depth is
region-polynomial; cancellation depth is region-exponential — the complete N-1 dichotomy. -/
theorem isMono_hasPieceCover :
    ∀ {e : Trop 1}, IsMono e → HasPieceCover (realize1 e) (leafCount e) := by
  intro e
  induction e with
  | var i => intro _; rw [realize1_var]; exact hasPieceCover_id
  | const c => intro _; rw [realize1_const]; exact hasPieceCover_const c
  | add a b iha ihb => intro h; rw [realize1_add]; exact hasPieceCover_add (iha h.1) (ihb h.2)
  | scale c a ih => intro h; rw [realize1_scale]; exact hasPieceCover_smul c (ih h.2)
  | max a b iha ihb =>
    intro h; rw [realize1_max]
    exact hasPieceCover_max (isMono_realize1_convexOn h.1) (isMono_realize1_convexOn h.2)
      (iha h.1) (ihb h.2)

end Sundog.RegionPoly
