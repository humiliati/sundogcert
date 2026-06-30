/-
# Exact representability — every convex continuous-PL function is a finite ReLU net (S3-1)

Slate-3 hook **S3-1**: the *characterization of universal approximation* at ε = 0. A 1-D
function is exactly representable by a finite ReLU network iff it is continuous piecewise-linear
with finitely many pieces. `HasPieceCover f k` is exactly that predicate (`f` is affine off a
finite cut set, hence continuous PL with `≤ k` pieces — `LineOn` is exact equality, and includes
the endpoints, so adjacent pieces agree).

This module lands the **convex case of the converse** (CPL ⟹ ReLU): a convex `HasPieceCover`
function is the realization of an explicit ReLU net. The construction is canonical — a convex PL
function is the upper envelope of its piece-lines (`convex_eq_sup_lines`), the upper envelope is a
tropical `max`-circuit (`linesTrop`), and a tropical circuit compiles exactly to a ReLU net
(`compile`/`realize1_compile`). The general (non-convex) converse — `f` as a difference of two
convex envelopes — and the forward direction (ReLU ⟹ CPL) are the staged extensions.
-/
import Sundogcert.RegionPoly

namespace Sundog.ExactRepr

open Sundog.CircuitNet Sundog.RegionCount Sundog.PieceCover Sundog.RegionPoly

/-! ### `max` over a list, at the value level (bounds) -/

theorem foldlMax_le {α : Type*} (g : α → ℝ) (l : List α) (base c : ℝ)
    (hb : base ≤ c) (hmem : ∀ a ∈ l, g a ≤ c) :
    l.foldl (fun acc a => max acc (g a)) base ≤ c := by
  induction l generalizing base with
  | nil => simpa using hb
  | cons hd tl ih =>
    rw [List.foldl_cons]
    exact ih (max base (g hd)) (max_le hb (hmem hd List.mem_cons_self))
      (fun a ha => hmem a (List.mem_cons_of_mem hd ha))

theorem le_foldlMax_base {α : Type*} (g : α → ℝ) (l : List α) (base : ℝ) :
    base ≤ l.foldl (fun acc a => max acc (g a)) base := by
  induction l generalizing base with
  | nil => simp
  | cons hd tl ih => rw [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih (max base (g hd)))

theorem le_foldlMax_mem {α : Type*} (g : α → ℝ) {a : α} :
    ∀ (l : List α) (base : ℝ), a ∈ l → g a ≤ l.foldl (fun acc a => max acc (g a)) base := by
  intro l
  induction l with
  | nil => intro base ha; simp at ha
  | cons hd tl ih =>
    intro base ha
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | htl
    · exact le_trans (le_max_right _ _) (le_foldlMax_base g tl _)
    · exact ih (max base (g hd)) htl

/-! ### `max` over a list of lines, as a tropical circuit -/

/-- A nonempty list of lines `(slope, intercept)` as a tropical `max`-circuit. -/
def linesTrop : List (ℝ × ℝ) → Trop 1
  | [] => Trop.const 0
  | pr :: rest => rest.foldl (fun acc q => Trop.max acc (affineCirc q.1 q.2)) (affineCirc pr.1 pr.2)

/-- The realization of a `foldl` of `max`-with-affine-gates is the value-level `foldl` of `max`. -/
theorem realize1_foldl (rest : List (ℝ × ℝ)) (init : Trop 1) (x : ℝ) :
    realize1 (rest.foldl (fun acc q => Trop.max acc (affineCirc q.1 q.2)) init) x
      = rest.foldl (fun acc q => max acc (q.1 * x + q.2)) (realize1 init x) := by
  induction rest generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (Trop.max init (affineCirc hd.1 hd.2))]
    have hbase : realize1 (Trop.max init (affineCirc hd.1 hd.2)) x
        = max (realize1 init x) (hd.1 * x + hd.2) := by
      simp [realize1_max, affineCirc_realize]
    rw [hbase]

/-! ### The converse, convex case -/

/-- **Convex continuous-PL ⟹ ReLU (exact).** Every convex function with a finite piece cover is
the exact realization of a finite ReLU network — built as the upper envelope of its piece-lines,
compiled through the tropical→ReLU compiler. The first ε = 0 representability direction. -/
theorem convexCPL_realizable {f : ℝ → ℝ} {n : ℕ}
    (hconv : ConvexOn ℝ Set.univ f) (hpc : HasPieceCover f n) :
    ∃ g : Net 1, realize1N g = f := by
  obtain ⟨L, _, hle, hach⟩ := convex_eq_sup_lines hconv hpc
  have hne : L.toList ≠ [] := by
    obtain ⟨pr, hpr, _⟩ := hach 0
    intro h
    rw [List.eq_nil_iff_forall_not_mem] at h
    exact h pr (Finset.mem_toList.mpr hpr)
  obtain ⟨hd, tl, hLa⟩ := List.exists_cons_of_ne_nil hne
  have hhdL : hd ∈ L := Finset.mem_toList.mp (by rw [hLa]; exact List.mem_cons_self)
  have htlL : ∀ a ∈ tl, a ∈ L :=
    fun a ha => Finset.mem_toList.mp (by rw [hLa]; exact List.mem_cons_of_mem hd ha)
  refine ⟨compile (linesTrop L.toList), ?_⟩
  rw [realize1_compile]
  funext x
  rw [hLa]
  simp only [linesTrop]
  rw [realize1_foldl, affineCirc_realize]
  apply le_antisymm
  · exact foldlMax_le (fun q => q.1 * x + q.2) tl (hd.1 * x + hd.2) (f x)
      (hle hd hhdL x) (fun a ha => hle a (htlL a ha) x)
  · obtain ⟨pr, hpr, hprx⟩ := hach x
    rw [hprx]
    have hprLa : pr ∈ hd :: tl := by rw [← hLa]; exact Finset.mem_toList.mpr hpr
    rcases List.mem_cons.mp hprLa with rfl | hprtl
    · exact le_foldlMax_base (fun q => q.1 * x + q.2) tl (pr.1 * x + pr.2)
    · exact le_foldlMax_mem (fun q => q.1 * x + q.2) tl (hd.1 * x + hd.2) hprtl

/-! ### The general (non-convex) converse

The convex case routed through the upper envelope. The *general* converse needs no convexity:
peel the cut set one breakpoint at a time. At the largest breakpoint `b`, subtract a single ReLU
correction `Δ · relu(· − b)` whose coefficient `Δ` is the slope jump of `f` across `b`; the
remainder `f₀ = f − Δ·relu(· − b)` has the kink at `b` ironed out, so it is affine away from the
*smaller* cut set `S.erase b`. Induction supplies a net for `f₀`, and `f = f₀ + Δ·relu(· − b)`. -/

/-- A net for the affine map `x ↦ p·x + q`. -/
def affNet (p q : ℝ) : Net 1 := Net.add (Net.scale p (Net.var 0)) (Net.const q)

@[simp] theorem realize1N_affNet (p q : ℝ) : realize1N (affNet p q) = fun x => p * x + q := by
  funext x; simp [realize1N, affNet]

/-- A net for the shifted ReLU `x ↦ max (x − b) 0`. -/
def reluAtNet (b : ℝ) : Net 1 := Net.relu (Net.add (Net.var 0) (Net.const (-b)))

@[simp] theorem realize1N_reluAt (b : ℝ) : realize1N (reluAtNet b) = fun x => max (x - b) 0 := by
  funext x; simp [realize1N, reluAtNet, sub_eq_add_neg]

@[simp] theorem realize1N_add (a b : Net 1) :
    realize1N (Net.add a b) = fun x => realize1N a x + realize1N b x := by
  funext x; simp [realize1N]

@[simp] theorem realize1N_scale (c : ℝ) (a : Net 1) :
    realize1N (Net.scale c a) = fun x => c * realize1N a x := by
  funext x; simp [realize1N]

/-- **Canonical affine formula on a clean interval.** If `f` is affine away from `S` and the open
interval `(c,d)` avoids `S`, then on `[c,d]` the function `f` is the line through `(c, f c)` and
`(d, f d)` — given explicitly, so slopes can be compared without `Classical.choose`. -/
theorem clean_affine {f : ℝ → ℝ} {S : Finset ℝ} (hAff : AffineAway f S)
    {c d : ℝ} (hcd : c < d) (hclean : ∀ s ∈ S, s ∉ Set.Ioo c d) :
    ∀ x ∈ Set.Icc c d, f x = f c + (f d - f c) / (d - c) * (x - c) := by
  obtain ⟨p, q, hpq⟩ := hAff c d hcd.le hclean
  have hfc : f c = p * c + q := hpq c ⟨le_refl c, hcd.le⟩
  have hfd : f d = p * d + q := hpq d ⟨hcd.le, le_refl d⟩
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcd)
  have hslope : (f d - f c) / (d - c) = p := by rw [hfc, hfd, div_eq_iff hdc]; ring
  intro x hx
  rw [hpq x hx, hslope, hfc]; ring

/-- A function affine away from the empty cut set is globally a single line. -/
theorem affineAway_empty {f : ℝ → ℝ} (hAff : AffineAway f ∅) :
    ∃ p q : ℝ, ∀ x, f x = p * x + q := by
  obtain ⟨p, q, hpq⟩ := hAff 0 1 (by norm_num) (by simp)
  refine ⟨p, q, fun x => ?_⟩
  have hclean : ∀ s ∈ (∅ : Finset ℝ), s ∉ Set.Ioo (min x 0) (max x 1) := by simp
  have hc0 : min x (0:ℝ) ≤ 0 := min_le_right _ _
  have h1d : (1:ℝ) ≤ max x 1 := le_max_right _ _
  have hcd : min x (0:ℝ) ≤ max x 1 := le_trans hc0 (le_trans (by norm_num) h1d)
  obtain ⟨p', q', hpq'⟩ := hAff (min x 0) (max x 1) hcd hclean
  have e0 : f 0 = p' * 0 + q' := hpq' 0 ⟨hc0, le_trans (by norm_num) h1d⟩
  have e1 : f 1 = p' * 1 + q' := hpq' 1 ⟨le_trans hc0 (by norm_num), h1d⟩
  have ex : f x = p' * x + q' := hpq' x ⟨min_le_left _ _, le_max_left _ _⟩
  have hq0 : f 0 = p * 0 + q := hpq 0 ⟨by norm_num, by norm_num⟩
  have hp1 : f 1 = p * 1 + q := hpq 1 ⟨by norm_num, by norm_num⟩
  have hqq : q = q' := by have := hq0.symm.trans e0; simpa using this
  have hpp : p = p' := by
    have h := hp1.symm.trans e1; rw [hqq] at h; simp at h; linarith [h]
  rw [ex, hpp, hqq]

/-- **The peeling core.** Any function affine away from a finite cut set `S` is the exact
realization of a finite ReLU net, by induction on `S`: peel the largest breakpoint `b`, subtract
the single ReLU correction `Δ·relu(· − b)` (with `Δ` the slope jump across `b`), and recurse on
`S.erase b`. -/
theorem reluRepr_aux (S : Finset ℝ) :
    ∀ f : ℝ → ℝ, AffineAway f S → ∃ g : Net 1, realize1N g = f := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro f hAff
    rcases S.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨p, q, hpq⟩ := affineAway_empty hAff
      exact ⟨affNet p q, by funext x; simp only [realize1N_affNet]; exact (hpq x).symm⟩
    · -- peel the maximum breakpoint `b`
      set b := S.max' hne with hbdef
      have hbS : b ∈ S := S.max'_mem hne
      have hble : ∀ s ∈ S, s ≤ b := fun s hs => S.le_max' s hs
      set T := S.erase b with hTdef
      set a : ℝ := if hT' : T.Nonempty then T.max' hT' else b - 1 with hadef
      have ha_max : ∀ s ∈ T, s ≤ a := by
        intro s hs
        have hT' : T.Nonempty := ⟨s, hs⟩
        have hae : a = T.max' hT' := by rw [hadef]; exact dif_pos hT'
        rw [hae]; exact T.le_max' s hs
      have ha_lt : a < b := by
        rcases T.eq_empty_or_nonempty with hTe | hT'
        · rw [hadef, dif_neg (by rw [hTe]; exact Finset.not_nonempty_empty)]; linarith
        · have hae : a = T.max' hT' := by rw [hadef]; exact dif_pos hT'
          rw [hae]
          exact lt_of_le_of_ne (hble _ (Finset.mem_of_mem_erase (T.max'_mem hT')))
            (Finset.ne_of_mem_erase (T.max'_mem hT'))
      set sL : ℝ := (f b - f a) / (b - a) with hsLdef
      set sR : ℝ := f (b + 1) - f b with hsRdef
      set Δ : ℝ := sR - sL with hΔdef
      set f₀ : ℝ → ℝ := fun x => f x - Δ * max (x - b) 0 with hf0def
      have haff0 : AffineAway f₀ T := by
        intro u v huv hmissT
        rcases eq_or_lt_of_le huv with heq | huv'
        · exact ⟨0, f₀ v, fun x hx => by
            simp only [Set.mem_Icc] at hx
            have hxv : x = v := le_antisymm hx.2 (heq ▸ hx.1)
            rw [hxv]; simp⟩
        · by_cases hvb : v ≤ b
          · -- interval lies left of `b`: the ReLU is flat, `f₀ = f`
            have hSclean : ∀ s ∈ S, s ∉ Set.Ioo u v := by
              intro s hs hmem
              rcases eq_or_ne s b with rfl | hsb
              · rw [Set.mem_Ioo] at hmem; linarith [hmem.2, hvb]
              · exact hmissT s (Finset.mem_erase.mpr ⟨hsb, hs⟩) hmem
            obtain ⟨p, q, hpq⟩ := hAff u v huv hSclean
            refine ⟨p, q, fun x hx => ?_⟩
            simp only [Set.mem_Icc] at hx
            simp only [hf0def]
            rw [max_eq_right (by have := le_trans hx.2 hvb; linarith), hpq x ⟨hx.1, hx.2⟩]; ring
          · rw [not_le] at hvb
            by_cases hub : b ≤ u
            · -- interval lies right of `b`: the ReLU is `x - b`
              have hSclean : ∀ s ∈ S, s ∉ Set.Ioo u v := by
                intro s hs hmem
                rcases eq_or_ne s b with rfl | hsb
                · rw [Set.mem_Ioo] at hmem; linarith [hmem.1, hub]
                · exact hmissT s (Finset.mem_erase.mpr ⟨hsb, hs⟩) hmem
              obtain ⟨p, q, hpq⟩ := hAff u v huv hSclean
              refine ⟨p - Δ, q + Δ * b, fun x hx => ?_⟩
              simp only [Set.mem_Icc] at hx
              simp only [hf0def]
              rw [max_eq_left (by have := le_trans hub hx.1; linarith), hpq x ⟨hx.1, hx.2⟩]; ring
            · -- straddle: `u < b < v`
              rw [not_le] at hub
              have hleft_clean : ∀ s ∈ S, s ∉ Set.Ioo (min a u) b := by
                intro s hs hmem
                rw [Set.mem_Ioo] at hmem
                obtain ⟨h1, h2⟩ := hmem
                have hsT : s ∈ T := Finset.mem_erase.mpr ⟨ne_of_lt h2, hs⟩
                have hmin_lt_a : min a u < a := lt_of_lt_of_le h1 (ha_max s hsT)
                have hua : u < a := by
                  by_contra hcon; rw [not_lt] at hcon
                  rw [min_eq_left hcon] at hmin_lt_a; exact lt_irrefl a hmin_lt_a
                have hTne : T.Nonempty := ⟨s, hsT⟩
                have haT : a ∈ T := by
                  have hae : a = T.max' hTne := by rw [hadef]; exact dif_pos hTne
                  rw [hae]; exact T.max'_mem hTne
                exact hmissT a haT ⟨hua, lt_trans ha_lt hvb⟩
              have hright_clean : ∀ s ∈ S, s ∉ Set.Ioo b (max v (b + 1)) := by
                intro s hs hmem; rw [Set.mem_Ioo] at hmem
                exact absurd (hble s hs) (not_le.mpr hmem.1)
              have hmab : min a u < b := lt_of_le_of_lt (min_le_left _ _) ha_lt
              have hbM : b < max v (b + 1) := lt_of_lt_of_le hvb (le_max_left _ _)
              have hca_left := clean_affine hAff hmab hleft_clean
              have hca_right := clean_affine hAff hbM hright_clean
              set sCl : ℝ := (f b - f (min a u)) / (b - min a u) with hsCldef
              set sCr : ℝ := (f (max v (b + 1)) - f b) / (max v (b + 1) - b) with hsCrdef
              have hmu_le_a : min a u ≤ a := min_le_left _ _
              have hmu_le_u : min a u ≤ u := min_le_right _ _
              have hfa : f a = f (min a u) + sCl * (a - min a u) := by
                rw [hsCldef]; exact hca_left a ⟨hmu_le_a, ha_lt.le⟩
              have hfb_l : f b = f (min a u) + sCl * (b - min a u) := by
                rw [hsCldef]; exact hca_left b ⟨hmab.le, le_refl b⟩
              have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha_lt)
              have hsL_eq : sL = sCl := by
                rw [hsLdef, hfa, hfb_l, div_eq_iff hba]; ring
              have hfb1 : f (b + 1) = f b + sCr * ((b + 1) - b) := by
                rw [hsCrdef]; exact hca_right (b + 1) ⟨by linarith, le_max_right _ _⟩
              have hsR_eq : sR = sCr := by rw [hsRdef, hfb1]; ring
              refine ⟨sL, f b - sL * b, fun x hx => ?_⟩
              simp only [Set.mem_Icc] at hx
              simp only [hf0def]
              by_cases hxb : x ≤ b
              · have hfx : f x = f b + sCl * (x - b) := by
                  have h1 : f x = f (min a u) + sCl * (x - min a u) := by
                    rw [hsCldef]; exact hca_left x ⟨le_trans hmu_le_u hx.1, hxb⟩
                  rw [h1, hfb_l]; ring
                rw [max_eq_right (by linarith : x - b ≤ 0), hfx, hsL_eq]; ring
              · rw [not_le] at hxb
                have hfx : f x = f b + sCr * (x - b) := by
                  rw [hsCrdef]
                  exact hca_right x ⟨hxb.le, le_trans hx.2 (le_max_left _ _)⟩
                rw [max_eq_left (by linarith : (0:ℝ) ≤ x - b), hfx, hΔdef, hsR_eq]; ring
      obtain ⟨g₀, hg₀⟩ := ih T (Finset.erase_ssubset hbS) f₀ haff0
      refine ⟨Net.add g₀ (Net.scale Δ (reluAtNet b)), ?_⟩
      funext x
      simp only [realize1N_add, realize1N_scale, realize1N_reluAt, hg₀, hf0def]
      ring

/-- **General continuous-PL ⟹ ReLU (exact), no convexity.** Every function with a finite piece
cover — i.e. every continuous piecewise-linear function with finitely many pieces — is the exact
realization of a finite ReLU network. With the convex case (`convexCPL_realizable`) this is the
full converse of the ε = 0 characterization: continuous-PL ⟹ finite ReLU, dropping convexity. -/
theorem cpl_realizable {f : ℝ → ℝ} {n : ℕ} (h : HasPieceCover f n) :
    ∃ g : Net 1, realize1N g = f := by
  obtain ⟨S, _, hAff⟩ := h
  exact reluRepr_aux S f hAff

/-! ### The forward direction: ReLU ⟹ continuous-PL

Every ReLU net's 1-D realization has a finite piece cover. By induction on the net: `var`/`const`
are single pieces, `add`/`scale` reuse `hasPieceCover_add`/`hasPieceCover_smul`, and the only real
content is `relu`, which at most *doubles* the piece count — `max(f, 0)` kinks only at `f`'s own
breakpoints and at the (≤ one-per-piece) zero-crossings of `f`. -/

@[simp] theorem realize1N_relu (a : Net 1) :
    realize1N (Net.relu a) = fun x => max (realize1N a x) 0 := by
  funext x; simp [realize1N]

/-- **The ReLU piece bound (general, non-convex).** Applying `relu` at most doubles the piece
count: the cut set of `max(f, 0)` is `f`'s cut set together with one zero-crossing per piece.
This is the doubling-via-crossings bound deferred in N-1. -/
theorem hasPieceCover_relu {f : ℝ → ℝ} {k : ℕ} (hf : HasPieceCover f k) :
    HasPieceCover (fun x => max (f x) 0) (2 * k) := by
  classical
  obtain ⟨S, hScard, hAff⟩ := hf
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 S.card) hScard
  -- a single clean piece-line `sl·+ic` whose zero is outside `(u,v)` gives a ReLU that is affine
  have key : ∀ (u v : ℝ) (sl ic : ℝ), (-ic / sl ∉ Set.Ioo u v) →
      (∀ x ∈ Set.Icc u v, f x = sl * x + ic) →
      ∃ p q, ∀ x ∈ Set.Icc u v, max (f x) 0 = p * x + q := by
    intro u v sl ic hzero hfeq
    by_cases hsl : sl = 0
    · exact ⟨0, max ic 0, fun x hx => by rw [hfeq x hx, hsl]; simp⟩
    · have hgz : ∀ x, sl * x + ic = sl * (x - (-ic / sl)) := fun x => by field_simp; ring
      have hz' : (-ic / sl) ≤ u ∨ v ≤ (-ic / sl) := by
        by_contra h; rw [not_or, not_le, not_le] at h; exact hzero ⟨h.1, h.2⟩
      have hsign : (∀ x ∈ Set.Icc u v, 0 ≤ sl * x + ic) ∨
          (∀ x ∈ Set.Icc u v, sl * x + ic ≤ 0) := by
        rcases hz' with hzu | hzv <;> rcases lt_or_gt_of_ne hsl with hsgn | hsgn
        · right; intro x hx; rw [Set.mem_Icc] at hx
          have hxz : 0 ≤ x - (-ic / sl) := by linarith [hx.1]
          nlinarith [hgz x, hxz, hsgn]
        · left; intro x hx; rw [Set.mem_Icc] at hx
          have hxz : 0 ≤ x - (-ic / sl) := by linarith [hx.1]
          nlinarith [hgz x, hxz, hsgn]
        · left; intro x hx; rw [Set.mem_Icc] at hx
          have hxz : x - (-ic / sl) ≤ 0 := by linarith [hx.2]
          nlinarith [hgz x, hxz, hsgn]
        · right; intro x hx; rw [Set.mem_Icc] at hx
          have hxz : x - (-ic / sl) ≤ 0 := by linarith [hx.2]
          nlinarith [hgz x, hxz, hsgn]
      rcases hsign with hpos | hneg
      · exact ⟨sl, ic, fun x hx => by rw [hfeq x hx, max_eq_left (hpos x hx)]⟩
      · exact ⟨0, 0, fun x hx => by rw [hfeq x hx, max_eq_right (hneg x hx)]; ring⟩
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · -- `f` is a single global line; ≤ 1 crossing
    obtain ⟨p, q, hpq⟩ := affineAway_empty hAff
    refine ⟨{-q / p}, by simp only [Finset.card_singleton]; omega, fun u v _ hmiss => ?_⟩
    have hz0 : -q / p ∉ Set.Ioo u v := by simpa using hmiss (-q / p) (Finset.mem_singleton_self _)
    exact key u v p q hz0 (fun x _ => hpq x)
  · -- the cut-enumeration scaffold (convexity-free)
    set nextCut : ℝ → ℝ :=
      fun a => if h : (S.filter (a < ·)).Nonempty then (S.filter (a < ·)).min' h else a + 1
      with hnc
    set lineOf : ℝ → ℝ × ℝ :=
      fun a => ((f (nextCut a) - f a) / (nextCut a - a),
        f a - (f (nextCut a) - f a) / (nextCut a - a) * a) with hlo
    set zeroAt : ℝ → ℝ := fun a => -(lineOf a).2 / (lineOf a).1 with hza
    have hlt : ∀ a, a < nextCut a := by
      intro a; simp only [hnc]
      by_cases h : (S.filter (a < ·)).Nonempty
      · rw [dif_pos h]; exact (Finset.mem_filter.mp ((S.filter (a < ·)).min'_mem h)).2
      · rw [dif_neg h]; linarith
    have hmissAt : ∀ a, ∀ s ∈ S, s ∉ Set.Ioo a (nextCut a) := by
      intro a s hs hsin; simp only [hnc] at hsin
      by_cases h : (S.filter (a < ·)).Nonempty
      · rw [dif_pos h] at hsin
        exact absurd (Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, hsin.1⟩)) (not_le.mpr hsin.2)
      · rw [dif_neg h] at hsin
        exact h ⟨s, Finset.mem_filter.mpr ⟨hs, hsin.1⟩⟩
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
    -- the cut set: `S` together with one crossing per piece
    set A := insert (S.min' hSne - 1) S with hA
    refine ⟨S ∪ A.image zeroAt, ?_, ?_⟩
    · have h1 : (S ∪ A.image zeroAt).card ≤ S.card + (A.image zeroAt).card :=
        Finset.card_union_le _ _
      have h2 : (A.image zeroAt).card ≤ A.card := Finset.card_image_le
      have h3 : A.card ≤ S.card + 1 := Finset.card_insert_le _ _
      omega
    · intro u v huv hmiss
      rcases eq_or_lt_of_le huv with heq | huv'
      · exact ⟨0, max (f v) 0, fun x hx => by
          simp only [Set.mem_Icc] at hx
          obtain rfl : x = v := le_antisymm hx.2 (heq ▸ hx.1); simp⟩
      · have hSclean : ∀ s ∈ S, s ∉ Set.Ioo u v := fun s hs =>
          hmiss s (Finset.mem_union_left _ hs)
        obtain ⟨a, haA, hfline⟩ :
            ∃ a ∈ A, ∀ x ∈ Set.Icc u v, f x = (lineOf a).1 * x + (lineOf a).2 := by
          by_cases hvm : v ≤ S.min' hSne
          · exact ⟨S.min' hSne - 1, Finset.mem_insert_self _ _,
              fun x hx => hleftmost x (le_trans hx.2 hvm)⟩
          · rw [not_le] at hvm
            by_cases hMu : S.max' hSne ≤ u
            · exact ⟨S.max' hSne, Finset.mem_insert_of_mem (S.max'_mem hSne),
                fun x hx => hrightmost x (le_trans hMu hx.1)⟩
            · rw [not_le] at hMu
              have huge : S.min' hSne ≤ u := by
                by_contra hc; rw [not_le] at hc
                exact hSclean (S.min' hSne) (S.min'_mem hSne) ⟨hc, hvm⟩
              have hfne : (S.filter (· ≤ u)).Nonempty :=
                ⟨S.min' hSne, Finset.mem_filter.mpr ⟨S.min'_mem hSne, huge⟩⟩
              set a := (S.filter (· ≤ u)).max' hfne with ha
              have ha_mem : a ∈ S := Finset.mem_of_mem_filter a (Finset.max'_mem _ hfne)
              have ha_le : a ≤ u := (Finset.mem_filter.mp (Finset.max'_mem _ hfne)).2
              refine ⟨a, Finset.mem_insert_of_mem ha_mem, fun x hx => ?_⟩
              have hxnc : v ≤ nextCut a := by
                simp only [hnc]
                by_cases h : (S.filter (a < ·)).Nonempty
                · rw [dif_pos h]
                  have hmem := Finset.min'_mem (S.filter (a < ·)) h
                  rw [Finset.mem_filter] at hmem
                  by_contra hlt2; rw [not_le] at hlt2
                  have hcu : u < (S.filter (a < ·)).min' h := by
                    by_contra hcu'; rw [not_lt] at hcu'
                    exact absurd (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hmem.1, hcu'⟩))
                      (not_le.mpr hmem.2)
                  exact hSclean _ hmem.1 ⟨hcu, hlt2⟩
                · rw [dif_neg h]
                  have hMa : S.max' hSne ≤ a := by
                    by_contra hc; rw [not_le] at hc
                    exact h ⟨S.max' hSne, Finset.mem_filter.mpr ⟨S.max'_mem hSne, hc⟩⟩
                  linarith [hMu, hMa, ha_le]
              exact hpiece a x ⟨le_trans ha_le hx.1, le_trans hx.2 hxnc⟩
        have hzero : zeroAt a ∉ Set.Ioo u v :=
          hmiss (zeroAt a) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ haA))
        exact key u v (lineOf a).1 (lineOf a).2 hzero hfline

/-- **The forward direction.** Every ReLU net's 1-D realization is continuous piecewise-linear
(has a finite piece cover). By induction on the net; the `relu` step is `hasPieceCover_relu`. -/
theorem net_hasPieceCover : ∀ g : Net 1, ∃ k, HasPieceCover (realize1N g) k := by
  intro g
  induction g with
  | var i =>
    refine ⟨1, ?_⟩
    have h : realize1N (Net.var i) = (id : ℝ → ℝ) := by funext t; simp [realize1N]
    rw [h]; exact hasPieceCover_id
  | const c =>
    refine ⟨1, ?_⟩
    have h : realize1N (Net.const c) = (fun _ => c) := by funext t; simp [realize1N]
    rw [h]; exact hasPieceCover_const c
  | add a b iha ihb =>
    obtain ⟨ka, hka⟩ := iha; obtain ⟨kb, hkb⟩ := ihb
    exact ⟨ka + kb, by rw [realize1N_add]; exact hasPieceCover_add hka hkb⟩
  | scale c a ih =>
    obtain ⟨ka, hka⟩ := ih
    exact ⟨ka, by rw [realize1N_scale]; exact hasPieceCover_smul c hka⟩
  | relu a ih =>
    obtain ⟨ka, hka⟩ := ih
    exact ⟨2 * ka, by rw [realize1N_relu]; exact hasPieceCover_relu hka⟩

/-- **Exact representability characterization (S3-1), ε = 0.** A 1-D function is the exact
realization of a finite ReLU network **iff** it is continuous piecewise-linear with finitely many
pieces (`HasPieceCover`). The forward direction is `net_hasPieceCover`; the converse is
`cpl_realizable`. This closes the ε = 0 case of arXiv:2606.26705's characterization of universal
approximation, in both directions. -/
theorem cpl_iff_reluNet (f : ℝ → ℝ) :
    (∃ k, HasPieceCover f k) ↔ (∃ g : Net 1, realize1N g = f) := by
  constructor
  · rintro ⟨k, hk⟩; exact cpl_realizable hk
  · rintro ⟨g, rfl⟩; exact net_hasPieceCover g

end Sundog.ExactRepr
