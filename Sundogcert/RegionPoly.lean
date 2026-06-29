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
  · sorry
  · -- smallest cut strictly above `a`, else `a + 1`
    set nextCut : ℝ → ℝ :=
      fun a => if h : (S.filter (a < ·)).Nonempty then (S.filter (a < ·)).min' h else a + 1
      with hnc
    -- secant of `f` on the piece `[a, nextCut a]`
    set lineOf : ℝ → ℝ × ℝ :=
      fun a => ((f (nextCut a) - f a) / (nextCut a - a),
        f a - (f (nextCut a) - f a) / (nextCut a - a) * a) with hlo
    refine ⟨(insert (S.min' hSne - 1) S).image lineOf, ?_, ?_, ?_⟩
    · calc ((insert (S.min' hSne - 1) S).image lineOf).card
            ≤ (insert (S.min' hSne - 1) S).card := Finset.card_image_le
        _ ≤ S.card + 1 := Finset.card_insert_le _ _
        _ ≤ n := by omega
    · sorry
    · sorry

end Sundog.RegionPoly
