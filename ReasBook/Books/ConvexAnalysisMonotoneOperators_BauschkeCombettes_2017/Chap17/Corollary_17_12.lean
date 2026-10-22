/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_34

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Filter
open EReal

namespace ERealFunction

section Corollary_17_12

variable (h : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)

private theorem toReal_strictConvexOn_of_deriv2_pos
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hderiv2_pos : ∀ x ∈ effectiveDomain h, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x) :
    StrictConvexOn ℝ (erealOpenInterval α β) (fun x ↦ (h x : EReal).toReal) := by
  have hconv : Convex ℝ (erealOpenInterval α β) := by
    rw [convex_iff_ordConnected]
    simpa [erealOpenInterval] using
      (ordConnected_Ioo.preimage_mono
        (show Monotone ((↑) : ℝ → EReal) from EReal.coe_strictMono.monotone))
  have hdiff' : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (erealOpenInterval α β) := by
    simpa [hdom] using hdiff
  have hderiv2_pos' :
      ∀ x ∈ erealOpenInterval α β, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x := by
    simpa [hdom] using hderiv2_pos
  exact strictConvexOn_of_deriv2_pos' hconv hdiff'.continuousOn hderiv2_pos'

private theorem strictlyConvex_of_deriv2_pos
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hderiv2_pos : ∀ x ∈ effectiveDomain h, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x) :
    StrictlyConvex h := by
  have hstrictOn :
      StrictConvexOn ℝ (erealOpenInterval α β) (fun x ↦ (h x : EReal).toReal) :=
    toReal_strictConvexOn_of_deriv2_pos h α β hdom hdiff hderiv2_pos
  rw [strictConvexOn_iff_div] at hstrictOn
  intro x hx y hy hxy a ha0 ha1
  have hxI : x ∈ erealOpenInterval α β := by
    simpa [hdom] using hx
  have hyI : y ∈ erealOpenInterval α β := by
    simpa [hdom] using hy
  have hxyI : a • x + (1 - a) • y ∈ erealOpenInterval α β := by
    exact hstrictOn.1 hxI hyI ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  have hxy_dom : a • x + (1 - a) • y ∈ effectiveDomain h := by
    simpa [hdom] using hxyI
  have hineq_real :
      (h (a • x + (1 - a) • y) : EReal).toReal <
        a * (h x : EReal).toReal + (1 - a) * (h y : EReal).toReal := by
    have hb0 : 0 < 1 - a := sub_pos.mpr ha1
    have hineq := hstrictOn.2 hxI hyI hxy ha0 hb0
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hineq
  have hxy_top : (h (a • x + (1 - a) • y) : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hxy_dom)
  have hxy_bot : (h (a • x + (1 - a) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (h _).2
  have hx_top : (h x : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (h x : EReal) ≠ ⊥ := by
    exact ne_of_gt (h x).2
  have hy_top : (h y : EReal) ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (h y : EReal) ≠ ⊥ := by
    exact ne_of_gt (h y).2
  have hineq_ereal :
      (((h (a • x + (1 - a) • y) : EReal).toReal : ℝ) : EReal) <
        ((a * (h x : EReal).toReal + (1 - a) * (h y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hineq_real
  have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  calc
    (h (a • x + (1 - a) • y) : EReal)
        = (((h (a • x + (1 - a) • y) : EReal).toReal : ℝ) : EReal) := by
            symm
            exact EReal.coe_toReal hxy_top hxy_bot
    _ < ((a * (h x : EReal).toReal + (1 - a) * (h y : EReal).toReal : ℝ) : EReal) :=
      hineq_ereal
    _ = (a : EReal) * (h x : EReal) + (1 - a : EReal) * (h y : EReal) := by
      rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hx_top hx_bot,
        EReal.coe_toReal hy_top hy_bot, hsub_cast]

private theorem left_liminf_gt_bot_of_deriv2_pos
    (hαβ : α < β)
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hderiv2_pos : ∀ x ∈ effectiveDomain h, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x) :
    ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (h y : EReal)) (nhdsWithin x (Set.Ioi x)) := by
  intro x hxa
  let f : ℝ → ℝ := fun t ↦ (h t : EReal).toReal
  have hstrictOn :
      StrictConvexOn ℝ (erealOpenInterval α β) f :=
    toReal_strictConvexOn_of_deriv2_pos h α β hdom hdiff hderiv2_pos
  have hconvOn := hstrictOn.convexOn
  have hxb : (x : EReal) < β := by simpa [hxa] using hαβ
  rcases EReal.lt_iff_exists_real_btwn.mp hxb with ⟨y, hxy, hyβ⟩
  rcases EReal.lt_iff_exists_real_btwn.mp hyβ with ⟨z, hyz, hzβ⟩
  have hxy_real : x < y := by
    have hxy' : (x : EReal) < (y : EReal) := by simpa [hxa] using hxy
    exact_mod_cast hxy'
  have hyz_real : y < z := by
    exact_mod_cast hyz
  have hy_mem : y ∈ erealOpenInterval α β := by
    rw [mem_erealOpenInterval_iff]
    exact ⟨by simpa [hxa] using hxy, hyβ⟩
  have hz_mem : z ∈ erealOpenInterval α β := by
    rw [mem_erealOpenInterval_iff]
    exact ⟨by
      have h : α < (z : EReal) := by
        exact lt_trans (by simpa [hxa] using hxy) hyz
      simpa using h, hzβ⟩
  let ℓ : ℝ → ℝ := fun t ↦ ((z - t) * f y - (y - t) * f z) / (z - y)
  have hsecant : ∀ {t : ℝ}, t ∈ Set.Ioo x y → ((ℓ t : ℝ) : EReal) ≤ (h t : EReal) := by
    intro t ht
    have ht_mem : t ∈ erealOpenInterval α β := by
      rw [mem_erealOpenInterval_iff]
      refine ⟨?_, ?_⟩
      · have htx : (x : EReal) < (t : EReal) := by exact_mod_cast ht.1
        simpa [hxa] using htx
      · exact lt_trans (by exact_mod_cast ht.2) hyβ
    let a : ℝ := (z - y) / (z - t)
    let b : ℝ := (y - t) / (z - t)
    have hzt : 0 < z - t := by linarith [ht.2, hyz_real]
    have hyt : 0 < y - t := by linarith [ht.2]
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr hyz_real.le) hzt.le
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (sub_nonneg.mpr ht.2.le) hzt.le
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (lt_trans ht.2 hyz_real).ne]
      ring
    have hy_repr : a • t + b • z = y := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (lt_trans ht.2 hyz_real).ne]
      ring
    have hconv0 : f (a • t + b • z) ≤ a • f t + b • f z := by
      simpa [f] using hconvOn.2 ht_mem hz_mem ha hb hab
    have hconv :
        f y ≤ a * f t + b * f z := by
      rw [hy_repr] at hconv0
      simpa [f, smul_eq_mul] using hconv0
    have hconv' : (z - t) * f y ≤ (z - y) * f t + (y - t) * f z := by
      have hconv0 := hconv
      dsimp [a, b] at hconv0
      field_simp [sub_ne_zero.mpr (lt_trans ht.2 hyz_real).ne] at hconv0
      simpa [mul_comm] using hconv0
    have hlin : ℓ t ≤ f t := by
      have hyz_pos : 0 < z - y := sub_pos.mpr hyz_real
      dsimp [ℓ]
      refine (div_le_iff₀ hyz_pos).2 ?_
      linarith
    have ht_dom : t ∈ effectiveDomain h := by
      simpa [hdom] using ht_mem
    have ht_top : (h t : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht_dom)
    have ht_bot : (h t : EReal) ≠ ⊥ := ne_of_gt (h t).2
    have hcoe :
        (((h t : EReal).toReal : ℝ) : EReal) = (h t : EReal) :=
      EReal.coe_toReal ht_top ht_bot
    simpa [f, hcoe] using (show ((ℓ t : ℝ) : EReal) ≤ ((f t : ℝ) : EReal) from by
      exact_mod_cast hlin)
  have hsecant_eventually :
      ∀ᶠ t in nhdsWithin x (Set.Ioi x), ((ℓ t : ℝ) : EReal) ≤ (h t : EReal) := by
    have hmem : Set.Ioi x ∩ Set.Iio y ∈ nhdsWithin x (Set.Ioi x) := by
      exact inter_mem_nhdsWithin (Set.Ioi x) (Iio_mem_nhds hxy_real)
    filter_upwards [hmem] with t ht
    exact hsecant ⟨ht.1, ht.2⟩
  have hℓ_cont : Continuous ℓ := by
    dsimp [ℓ]
    continuity
  have hℓ_tendsto :
      Tendsto (fun t : ℝ ↦ ((ℓ t : ℝ) : EReal)) (nhdsWithin x (Set.Ioi x))
        (nhds ((ℓ x : ℝ) : EReal)) := by
    exact ((continuous_coe_real_ereal.comp hℓ_cont).continuousAt.continuousWithinAt).tendsto
  have hℓ_le :
      ((ℓ x : ℝ) : EReal) ≤
        Filter.liminf (fun t : ℝ ↦ (h t : EReal)) (nhdsWithin x (Set.Ioi x)) := by
    let _ : NeBot (nhdsWithin x (Set.Ioi x)) := nhdsWithin_Ioi_neBot le_rfl
    calc
      ((ℓ x : ℝ) : EReal)
          = Filter.liminf (fun t : ℝ ↦ ((ℓ t : ℝ) : EReal)) (nhdsWithin x (Set.Ioi x)) := by
              symm
              exact hℓ_tendsto.liminf_eq
      _ ≤ Filter.liminf (fun t : ℝ ↦ (h t : EReal)) (nhdsWithin x (Set.Ioi x)) :=
        Filter.liminf_le_liminf hsecant_eventually
  exact lt_of_lt_of_le (EReal.bot_lt_coe (ℓ x)) hℓ_le

private theorem right_liminf_gt_bot_of_deriv2_pos
    (hαβ : α < β)
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hderiv2_pos : ∀ x ∈ effectiveDomain h, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x) :
    ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (h y : EReal)) (nhdsWithin x (Set.Iio x)) := by
  intro x hxb
  let f : ℝ → ℝ := fun t ↦ (h t : EReal).toReal
  have hstrictOn :
      StrictConvexOn ℝ (erealOpenInterval α β) f :=
    toReal_strictConvexOn_of_deriv2_pos h α β hdom hdiff hderiv2_pos
  have hconvOn := hstrictOn.convexOn
  have hax : α < (x : EReal) := by simpa [hxb] using hαβ
  rcases EReal.lt_iff_exists_real_btwn.mp hax with ⟨z, hαz, hzx⟩
  rcases EReal.lt_iff_exists_real_btwn.mp hαz with ⟨y, hαy, hyz⟩
  have hyz_real : y < z := by
    exact_mod_cast hyz
  have hzx_real : z < x := by
    have hzx' : (z : EReal) < (x : EReal) := by simpa [hxb] using hzx
    exact_mod_cast hzx'
  have hy_mem : y ∈ erealOpenInterval α β := by
    rw [mem_erealOpenInterval_iff]
    exact ⟨hαy, by
      have h : (y : EReal) < β := by
        exact lt_trans hyz (by simpa [hxb] using hzx)
      simpa using h⟩
  have hz_mem : z ∈ erealOpenInterval α β := by
    rw [mem_erealOpenInterval_iff]
    exact ⟨hαz, by simpa [hxb] using hzx⟩
  let ℓ : ℝ → ℝ := fun t ↦ ((z - t) * f y - (y - t) * f z) / (z - y)
  have hsecant : ∀ {t : ℝ}, t ∈ Set.Ioo z x → ((ℓ t : ℝ) : EReal) ≤ (h t : EReal) := by
    intro t ht
    have ht_mem : t ∈ erealOpenInterval α β := by
      rw [mem_erealOpenInterval_iff]
      refine ⟨?_, ?_⟩
      · exact lt_trans hαz (by exact_mod_cast ht.1)
      · have htx : (t : EReal) < (x : EReal) := by exact_mod_cast ht.2
        simpa [hxb] using htx
    let a : ℝ := (t - z) / (t - y)
    let b : ℝ := (z - y) / (t - y)
    have htz : 0 < t - z := by linarith [ht.1]
    have hty : 0 < t - y := by linarith [hyz_real, ht.1]
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr ht.1.le) hty.le
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (sub_nonneg.mpr hyz_real.le) hty.le
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (lt_trans hyz_real ht.1).ne]
      ring
    have hz_repr : a • y + b • t = z := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (lt_trans hyz_real ht.1).ne]
      ring
    have hconv0 : f (a • y + b • t) ≤ a • f y + b • f t := by
      simpa [f] using hconvOn.2 hy_mem ht_mem ha hb hab
    have hconv :
        f z ≤ a * f y + b * f t := by
      rw [hz_repr] at hconv0
      simpa [f, smul_eq_mul] using hconv0
    have hconv' : (t - y) * f z ≤ (t - z) * f y + (z - y) * f t := by
      have hconv0 := hconv
      dsimp [a, b] at hconv0
      field_simp [sub_ne_zero.mpr (lt_trans hyz_real ht.1).ne] at hconv0
      simpa [mul_comm] using hconv0
    have hlin : ℓ t ≤ f t := by
      have hyz_pos : 0 < z - y := sub_pos.mpr hyz_real
      dsimp [ℓ]
      refine (div_le_iff₀ hyz_pos).2 ?_
      linarith
    have ht_dom : t ∈ effectiveDomain h := by
      simpa [hdom] using ht_mem
    have ht_top : (h t : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht_dom)
    have ht_bot : (h t : EReal) ≠ ⊥ := ne_of_gt (h t).2
    have hcoe :
        (((h t : EReal).toReal : ℝ) : EReal) = (h t : EReal) :=
      EReal.coe_toReal ht_top ht_bot
    simpa [f, hcoe] using (show ((ℓ t : ℝ) : EReal) ≤ ((f t : ℝ) : EReal) from by
      exact_mod_cast hlin)
  have hsecant_eventually :
      ∀ᶠ t in nhdsWithin x (Set.Iio x), ((ℓ t : ℝ) : EReal) ≤ (h t : EReal) := by
    have hmem : Set.Iio x ∩ Set.Ioi z ∈ nhdsWithin x (Set.Iio x) := by
      exact inter_mem_nhdsWithin (Set.Iio x) (Ioi_mem_nhds hzx_real)
    filter_upwards [hmem] with t ht
    exact hsecant ⟨ht.2, ht.1⟩
  have hℓ_cont : Continuous ℓ := by
    dsimp [ℓ]
    continuity
  have hℓ_tendsto :
      Tendsto (fun t : ℝ ↦ ((ℓ t : ℝ) : EReal)) (nhdsWithin x (Set.Iio x))
        (nhds ((ℓ x : ℝ) : EReal)) := by
    exact ((continuous_coe_real_ereal.comp hℓ_cont).continuousAt.continuousWithinAt).tendsto
  have hℓ_le :
      ((ℓ x : ℝ) : EReal) ≤
        Filter.liminf (fun t : ℝ ↦ (h t : EReal)) (nhdsWithin x (Set.Iio x)) := by
    let _ : NeBot (nhdsWithin x (Set.Iio x)) := nhdsWithin_Iio_neBot le_rfl
    calc
      ((ℓ x : ℝ) : EReal)
          = Filter.liminf (fun t : ℝ ↦ ((ℓ t : ℝ) : EReal)) (nhdsWithin x (Set.Iio x)) := by
              symm
              exact hℓ_tendsto.liminf_eq
      _ ≤ Filter.liminf (fun t : ℝ ↦ (h t : EReal)) (nhdsWithin x (Set.Iio x)) :=
        Filter.liminf_le_liminf hsecant_eventually
  exact lt_of_lt_of_le (EReal.bot_lt_coe (ℓ x)) hℓ_le

-- Proof sketch: use the positivity of the second derivative on the open interval `D` to obtain
-- strict convexity of the real-valued restriction of `h`, translate this to strict convexity of
-- the proper `]-∞,+∞]`-valued seed, and then apply Proposition 9.34 to its one-sided-limit
-- extension.
/-- Corollary 17.12 (1): if `D = dom h` is a nonempty open interval and the real-valued
representative of `h` is differentiable on `D` with strictly positive second derivative, then the
one-sided-limit extension of `h` across the boundary of `D` belongs to `Γ₀(ℝ)`. -/
theorem oneSidedLimitExtension_mem_gammaZero_of_deriv2_pos
    (hαβ : α < β)
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hderiv2_pos : ∀ x ∈ effectiveDomain h, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x) :
    oneSidedLimitExtension h α β
        (left_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos)
        (right_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos) ∈
      Γ₀(ℝ) := by
  let hαlim := left_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos
  let hβlim := right_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos
  have hstrict : StrictlyConvex h :=
    strictlyConvex_of_deriv2_pos h α β hdom hdiff hderiv2_pos
  exact oneSidedLimitExtension_mem_gammaZero h α β hαβ hdom hstrict hαlim hβlim

-- Proof sketch: rewrite `D` as `erealOpenInterval α β` and use the defining interior branch of
-- `oneSidedLimitExtensionEReal`.
/-- Corollary 17.12 (2): on the interval `D`, the one-sided-limit extension agrees with the
original function `h`. -/
theorem oneSidedLimitExtension_eqOn_domain
    (hdom : effectiveDomain h = erealOpenInterval α β) :
    EqOn (oneSidedLimitExtensionEReal h α β) (fun x ↦ (h x : EReal)) (effectiveDomain h) := by
  intro x hx
  have hx_interval : x ∈ erealOpenInterval α β := by
    simpa [hdom] using hx
  exact oneSidedLimitExtensionEReal_apply_of_mem_erealOpenInterval h α β hx_interval

-- Proof sketch: after rewriting `D = ]α,β[`, points of `D` lie on the interior branch of the
-- extension, and `hdom` makes those interior values finite.
/-- Corollary 17.12 (3): if `D = dom h`, then the open interval `D` is contained in the effective
domain of the one-sided-limit extension. -/
theorem domain_subset_effectiveDomain_oneSidedLimitExtension
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (h y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (h y : EReal)) (nhdsWithin x (Set.Iio x))) :
    effectiveDomain h ⊆
      effectiveDomain (oneSidedLimitExtension h α β hαlim hβlim) := by
  intro x hx
  rw [mem_effectiveDomain_iff, oneSidedLimitExtension_coe]
  have hx_interval : x ∈ erealOpenInterval α β := by
    simpa [hdom] using hx
  rw [oneSidedLimitExtensionEReal_apply_of_mem_erealOpenInterval h α β hx_interval]
  exact mem_effectiveDomain_iff.mp hx

-- Proof sketch: a finite value of the one-sided-limit extension must come either from the open
-- interval branch or from one of the two endpoint branches; rewrite this closed interval as
-- `closure D`.
/-- Corollary 17.12 (4): the effective domain of the one-sided-limit extension is contained in the
closure of `D`. -/
theorem effectiveDomain_oneSidedLimitExtension_subset_closure_domain
    (hαβ : α < β)
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (h y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (h y : EReal)) (nhdsWithin x (Set.Iio x))) :
    effectiveDomain (oneSidedLimitExtension h α β hαlim hβlim) ⊆
      closure (effectiveDomain h) := by
  intro x hx
  have hclosure :
      closure (effectiveDomain h) =
        {x : ℝ | α ≤ (x : EReal) ∧ (x : EReal) ≤ β} := by
    rw [hdom, erealOpenInterval]
    rw [(isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
        continuous_coe_real_ereal (Set.Ioo α β)).symm]
    ext t
    simp [closure_Ioo hαβ.ne]
  rw [hclosure]
  rw [mem_effectiveDomain_iff, oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal] at hx
  by_cases hx_interval : x ∈ erealOpenInterval α β
  · simpa [mem_erealOpenInterval_iff] using
      (show α ≤ (x : EReal) ∧ (x : EReal) ≤ β from by
        rcases mem_erealOpenInterval_iff.mp hx_interval with ⟨hxα, hxβ⟩
        exact ⟨hxα.le, hxβ.le⟩)
  · by_cases hxa : α = (x : EReal)
    · constructor
      · simp [hxa]
      · simpa [hxa] using hαβ.le
    · by_cases hxb : β = (x : EReal)
      · constructor
        · simpa [hxb] using hαβ.le
        · simp [hxb]
      · simp [hx_interval, hxa, hxb] at hx

-- Proof sketch: use the positive-second-derivative hypothesis to make `h` strictly convex on its
-- open interval domain, then invoke the strict-convexity preservation theorem for the one-sided
-- extension from Proposition 9.34.
/-- Corollary 17.12 (5): under the same hypotheses, the one-sided-limit extension of `h` is
strictly convex. -/
theorem oneSidedLimitExtension_strictlyConvex_of_deriv2_pos
    (hαβ : α < β)
    (hdom : effectiveDomain h = erealOpenInterval α β)
    (hdiff : DifferentiableOn ℝ (fun x ↦ (h x : EReal).toReal) (effectiveDomain h))
    (hderiv2_pos : ∀ x ∈ effectiveDomain h, 0 < (deriv^[2] fun t ↦ (h t : EReal).toReal) x) :
    StrictlyConvex
      (oneSidedLimitExtension h α β
        (left_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos)
        (right_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos)) := by
  let hαlim := left_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos
  let hβlim := right_liminf_gt_bot_of_deriv2_pos h α β hαβ hdom hdiff hderiv2_pos
  have hstrict : StrictlyConvex h :=
    strictlyConvex_of_deriv2_pos h α β hdom hdiff hderiv2_pos
  exact oneSidedLimitExtension_strictlyConvex h α β hαβ hdom hstrict hαlim hβlim

end Corollary_17_12

end ERealFunction
