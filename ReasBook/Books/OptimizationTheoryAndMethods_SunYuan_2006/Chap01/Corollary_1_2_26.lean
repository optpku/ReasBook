/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_25
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Set

noncomputable section

universe u

section Corollary126

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Source/core/bridge triage:
-- * source-facing: the Chapter 1 corollary comparing asymptotic error ratios under the
--   hypotheses of `Theorem_1_2_25`
-- * core/canonical owner: `Filter.limsup`
-- * bridge/view: `ENNReal.ofReal`, which records potentially unbounded nonnegative ratios
--   in the canonical extended-real codomain used elsewhere in the chapter

/-- Chapter01 Corollary 1.2.26: under the hypotheses of Theorem 1.2.25, if
`A : E ≃L[ℝ] E` identifies the derivative `fderiv ℝ F x` at `x` and
`ω t = max ‖u t - x‖ ‖v t - x‖` tends to `0` along `l`, then the limsup of the
error ratio, viewed in `ENNReal` via `ENNReal.ofReal`, is bounded by the condition
number `‖(A : E →L[ℝ] E)‖ * ‖(A.symm : E →L[ℝ] E)‖` times the limsup of the
corresponding image ratio in the same canonical codomain. -/
theorem limsup_normRatio_le_conditionNumber_mul_limsup_imageNormRatio
    {α : Type u}
    (D : Set E)
    (F : E → E)
    (x : E)
    (γ : NNReal)
    (A : E ≃L[ℝ] E)
    (u v : α → E)
    (l : Filter α)
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hcont : ContDiffOn ℝ 1 F D)
    (hLip : LipschitzOnWith γ (fderiv ℝ F) D)
    (hA : fderiv ℝ F x = (A : E →L[ℝ] E))
    (hω : Tendsto (fun t ↦ max ‖u t - x‖ ‖v t - x‖) l (nhds 0))
    (hv_ne : ∀ᶠ t in l, v t ≠ x)
    (hFv_ne : ∀ᶠ t in l, F (v t) ≠ F x) :
    l.limsup (fun t ↦ ENNReal.ofReal (‖u t - x‖ / ‖v t - x‖)) ≤
      ENNReal.ofReal (‖(A : E →L[ℝ] E)‖ * ‖(A.symm : E →L[ℝ] E)‖) *
        l.limsup (fun t ↦ ENNReal.ofReal (‖F (u t) - F x‖ / ‖F (v t) - F x‖)) := by
  by_cases hl : l = ⊥
  · -- The bottom-filter branch collapses both limsups to `0`.
    simp [hl]
  · haveI : NeBot l := ⟨hl⟩
    let ω : α → ℝ := fun t ↦ max ‖u t - x‖ ‖v t - x‖
    let κ : α → ℝ := fun t ↦
      (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) /
        ((1 / ‖(A.symm : E →L[ℝ] E)‖) - (γ : ℝ) * ω t)
    let factor : α → ENNReal := fun t ↦ ENNReal.ofReal (κ t)
    let lhs : α → ENNReal := fun t ↦ ENNReal.ofReal (‖u t - x‖ / ‖v t - x‖)
    let rhs : α → ENNReal := fun t ↦ ENNReal.ofReal (‖F (u t) - F x‖ / ‖F (v t) - F x‖)
    let μ : ℝ := ‖(A.symm : E →L[ℝ] E)‖
    let ε : ℝ := 1 / (2 * μ * ((γ : ℝ) + 1))
    let α₀ : ℝ := 1 / (2 * μ)
    let K : ℝ := ‖(A : E →L[ℝ] E)‖ * μ
    -- Route correction: use the exact linearization at the base point `x`, instead of the
    -- existential local constants from Theorem 1.2.25, so the source condition number survives.
    have hnot_subsingleton : ¬ Subsingleton E := by
      intro hsub
      have hfalse : ∀ᶠ t in l, False := by
        filter_upwards [hv_ne] with t ht
        exact ht (hsub.elim (v t) x)
      have hempty : (∅ : Set α) ∈ l := by
        change {t : α | False} ∈ l
        exact hfalse
      exact hl (Filter.empty_mem_iff_bot.mp hempty)
    haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
    have hμ_pos : 0 < μ := by
      simpa [μ] using A.norm_symm_pos
    have hA_pos : 0 < ‖(A : E →L[ℝ] E)‖ := by
      simpa using A.norm_pos
    have hK_pos : 0 < K := by
      exact mul_pos hA_pos hμ_pos
    have hconstants :
        0 < ε ∧ 0 < α₀ ∧ α₀ < α₀ + ‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ε + 1 ∧
          (γ : ℝ) * ε ≤ α₀ := by
      simpa [μ, ε, α₀] using
        chosenBiLipschitzConstants (γ := γ) (μ := μ) (c := ‖(A : E →L[ℝ] E)‖)
          hμ_pos (norm_nonneg _)
    rcases hconstants with ⟨hε_pos, hα₀_pos, -, hγε_le_α₀⟩
    have htwoα₀ : (2 : ℝ) * α₀ = 1 / μ := by
      dsimp [α₀]
      field_simp [hμ_pos.ne']
    have hω_small : ∀ᶠ t in l, ω t < ε := by
      have hω' : Tendsto ω l (nhds 0) := by simpa [ω] using hω
      exact (tendsto_order.1 hω').2 _ hε_pos
    -- First squeeze the common radius `ω t` to `0`, then deduce `u t → x` and `v t → x`.
    have hu_tendsto : Tendsto u l (nhds x) := by
      refine Metric.tendsto_nhds.2 ?_
      intro δ hδ
      have hω' : Tendsto ω l (nhds 0) := by simpa [ω] using hω
      have hsmall : ∀ᶠ t in l, ω t < δ := (tendsto_order.1 hω').2 _ hδ
      filter_upwards [hsmall] with t ht
      simpa [ω, dist_eq_norm] using
        (lt_of_le_of_lt (le_max_left ‖u t - x‖ ‖v t - x‖) ht)
    have hv_tendsto : Tendsto v l (nhds x) := by
      refine Metric.tendsto_nhds.2 ?_
      intro δ hδ
      have hω' : Tendsto ω l (nhds 0) := by simpa [ω] using hω
      have hsmall : ∀ᶠ t in l, ω t < δ := (tendsto_order.1 hω').2 _ hδ
      filter_upwards [hsmall] with t ht
      simpa [ω, dist_eq_norm] using
        (lt_of_le_of_lt (le_max_right ‖u t - x‖ ‖v t - x‖) ht)
    have hu_memD : ∀ᶠ t in l, u t ∈ D := hu_tendsto (hD_open.mem_nhds hx)
    have hv_memD : ∀ᶠ t in l, v t ∈ D := hv_tendsto (hD_open.mem_nhds hx)
    -- At each large `t`, combine the base-point Taylor remainder with the operator bounds.
    have hpointwise :
        ∀ᶠ t in l, lhs t ≤ factor t * rhs t := by
      filter_upwards [hu_memD, hv_memD, hv_ne, hFv_ne, hω_small] with t huD hvD hvx_ne hFv hxω
      have hω_le_ε : ω t ≤ ε := le_of_lt hxω
      have hγω_le_α₀ : (γ : ℝ) * ω t ≤ α₀ := by
        calc
          (γ : ℝ) * ω t ≤ (γ : ℝ) * ε := by
            gcongr
          _ ≤ α₀ := hγε_le_α₀
      have hlower_pos : 0 < (1 / μ) - (γ : ℝ) * ω t := by
        have hα₀_le : α₀ ≤ (1 / μ) - (γ : ℝ) * ω t := by
          nlinarith [htwoα₀, hγω_le_α₀]
        exact lt_of_lt_of_le hα₀_pos hα₀_le
      have hupper_nonneg : 0 ≤ ‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t := by
        positivity
      have hv_norm_pos : 0 < ‖v t - x‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hvx_ne)
      have hFv_norm_pos : 0 < ‖F (v t) - F x‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hFv)
      have herr_u0 :
          ‖F (u t) - F x - (A : E →L[ℝ] E) (u t - x)‖ ≤
            (γ : ℝ) * max ‖u t - x‖ ‖x - x‖ * ‖u t - x‖ := by
        simpa [hA] using
          linearizationErrorBoundAtBasePoint D F x γ hD_open hD_convex hcont hLip huD hx hx
      have herr_u :
          ‖F (u t) - F x - (A : E →L[ℝ] E) (u t - x)‖ ≤
            (γ : ℝ) * ω t * ‖u t - x‖ := by
        refine herr_u0.trans ?_
        have hmax_le : max ‖u t - x‖ ‖x - x‖ ≤ ω t := by
          dsimp [ω]
          simpa using le_max_left ‖u t - x‖ ‖v t - x‖
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmax_le (NNReal.coe_nonneg γ))
          (norm_nonneg _)
      have herr_v0 :
          ‖F (v t) - F x - (A : E →L[ℝ] E) (v t - x)‖ ≤
            (γ : ℝ) * max ‖v t - x‖ ‖x - x‖ * ‖v t - x‖ := by
        simpa [hA] using
          linearizationErrorBoundAtBasePoint D F x γ hD_open hD_convex hcont hLip hvD hx hx
      have herr_v :
          ‖F (v t) - F x - (A : E →L[ℝ] E) (v t - x)‖ ≤
            (γ : ℝ) * ω t * ‖v t - x‖ := by
        refine herr_v0.trans ?_
        have hmax_le : max ‖v t - x‖ ‖x - x‖ ≤ ω t := by
          dsimp [ω]
          simpa using le_max_right ‖u t - x‖ ‖v t - x‖
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmax_le (NNReal.coe_nonneg γ))
          (norm_nonneg _)
      have hlinear_u :
          ‖(A : E →L[ℝ] E) (u t - x)‖ ≤
            ‖F (u t) - F x‖ + (γ : ℝ) * ω t * ‖u t - x‖ := by
        have hdecomp :
            (A : E →L[ℝ] E) (u t - x) =
              F (u t) - F x - (F (u t) - F x - (A : E →L[ℝ] E) (u t - x)) := by
          abel_nf
        calc
          ‖(A : E →L[ℝ] E) (u t - x)‖ =
              ‖F (u t) - F x - (F (u t) - F x - (A : E →L[ℝ] E) (u t - x))‖ := by
                simpa using congrArg norm hdecomp
          _ ≤ ‖F (u t) - F x‖ + ‖F (u t) - F x - (A : E →L[ℝ] E) (u t - x)‖ :=
                norm_sub_le _ _
          _ ≤ ‖F (u t) - F x‖ + (γ : ℝ) * ω t * ‖u t - x‖ := by
            gcongr
      have hlower :
          ((1 / μ) - (γ : ℝ) * ω t) * ‖u t - x‖ ≤ ‖F (u t) - F x‖ := by
        have hmain :
            (1 / μ) * ‖u t - x‖ ≤
              ‖F (u t) - F x‖ + (γ : ℝ) * ω t * ‖u t - x‖ := by
          calc
            (1 / μ) * ‖u t - x‖ ≤ ‖(A : E →L[ℝ] E) (u t - x)‖ := by
              simpa [μ] using invOpNorm_mul_norm_le_norm_apply A (u t - x)
            _ ≤ ‖F (u t) - F x‖ + (γ : ℝ) * ω t * ‖u t - x‖ := hlinear_u
        nlinarith [hmain]
      have hupper :
          ‖F (v t) - F x‖ ≤
            (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) * ‖v t - x‖ := by
        have hupper_core :
            ‖F (v t) - F x‖ ≤
              ‖(A : E →L[ℝ] E) (v t - x)‖ + (γ : ℝ) * ω t * ‖v t - x‖ := by
          calc
            ‖F (v t) - F x‖ =
                ‖(F (v t) - F x - (A : E →L[ℝ] E) (v t - x)) +
                    (A : E →L[ℝ] E) (v t - x)‖ := by
                  simp [sub_eq_add_neg, add_assoc, add_left_comm]
            _ ≤ ‖F (v t) - F x - (A : E →L[ℝ] E) (v t - x)‖ +
                  ‖(A : E →L[ℝ] E) (v t - x)‖ := norm_add_le _ _
            _ ≤ (γ : ℝ) * ω t * ‖v t - x‖ + ‖(A : E →L[ℝ] E) (v t - x)‖ := by
              gcongr
            _ = ‖(A : E →L[ℝ] E) (v t - x)‖ + (γ : ℝ) * ω t * ‖v t - x‖ := by
              ring
        calc
          ‖F (v t) - F x‖ ≤ ‖(A : E →L[ℝ] E) (v t - x)‖ + (γ : ℝ) * ω t * ‖v t - x‖ :=
            hupper_core
          _ ≤ ‖(A : E →L[ℝ] E)‖ * ‖v t - x‖ + (γ : ℝ) * ω t * ‖v t - x‖ := by
            gcongr
            exact (A : E →L[ℝ] E).le_opNorm (v t - x)
          _ = (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) * ‖v t - x‖ := by
            ring
      have hcross :
          ((1 / μ) - (γ : ℝ) * ω t) * ‖F (v t) - F x‖ * ‖u t - x‖ ≤
            (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) * ‖F (u t) - F x‖ * ‖v t - x‖ := by
        have hcross_left :
            ((1 / μ) - (γ : ℝ) * ω t) * ‖F (v t) - F x‖ * ‖u t - x‖ ≤
              ‖F (u t) - F x‖ * ‖F (v t) - F x‖ := by
          have :=
            mul_le_mul_of_nonneg_right hlower (norm_nonneg (‖F (v t) - F x‖))
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have hcross_right :
            ‖F (u t) - F x‖ * ‖F (v t) - F x‖ ≤
              (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) * ‖F (u t) - F x‖ * ‖v t - x‖ := by
          have :=
            mul_le_mul_of_nonneg_left hupper (norm_nonneg (‖F (u t) - F x‖))
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        exact hcross_left.trans hcross_right
      have hratio_real :
          ‖u t - x‖ / ‖v t - x‖ ≤
            ((‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) /
                ((1 / μ) - (γ : ℝ) * ω t)) *
              (‖F (u t) - F x‖ / ‖F (v t) - F x‖) := by
        let lower : ℝ := (1 / μ) - (γ : ℝ) * ω t
        let upper : ℝ := ‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t
        have hcross' :
            lower * ‖F (v t) - F x‖ * ‖u t - x‖ ≤
              upper * ‖F (u t) - F x‖ * ‖v t - x‖ := by
          simpa [lower, upper] using hcross
        have hlower_pos' : 0 < lower := by
          simpa [lower] using hlower_pos
        have hcross_div :
            lower * ‖F (v t) - F x‖ * (‖u t - x‖ / ‖v t - x‖) ≤
              upper * ‖F (u t) - F x‖ := by
          have hcross_div' :
              (lower * ‖F (v t) - F x‖ * ‖u t - x‖) / ‖v t - x‖ ≤
                upper * ‖F (u t) - F x‖ := by
            apply (div_le_iff₀ hv_norm_pos).2
            simpa [mul_comm, mul_left_comm, mul_assoc] using hcross'
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcross_div'
        have hmain :
            ‖u t - x‖ / ‖v t - x‖ ≤
              (upper * ‖F (u t) - F x‖) / (lower * ‖F (v t) - F x‖) := by
          have hlf_pos : 0 < lower * ‖F (v t) - F x‖ := mul_pos hlower_pos' hFv_norm_pos
          apply (le_div_iff₀ hlf_pos).2
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcross_div
        calc
          ‖u t - x‖ / ‖v t - x‖
              ≤ (upper * ‖F (u t) - F x‖) / (lower * ‖F (v t) - F x‖) := hmain
          _ = (upper / lower) * (‖F (u t) - F x‖ / ‖F (v t) - F x‖) := by
                field_simp [hlower_pos'.ne', hFv_norm_pos.ne']
      have hκ_nonneg : 0 ≤ κ t := by
        dsimp [κ]
        exact div_nonneg hupper_nonneg hlower_pos.le
      -- Convert the real ratio estimate into the ENNReal inequality used by `Filter.limsup`.
      dsimp [lhs, factor, rhs]
      calc
        ENNReal.ofReal (‖u t - x‖ / ‖v t - x‖)
            ≤ ENNReal.ofReal
                (((‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) /
                    ((1 / μ) - (γ : ℝ) * ω t)) *
                  (‖F (u t) - F x‖ / ‖F (v t) - F x‖)) :=
              ENNReal.ofReal_le_ofReal hratio_real
        _ = ENNReal.ofReal
              ((‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * ω t) /
                ((1 / μ) - (γ : ℝ) * ω t)) *
              ENNReal.ofReal (‖F (u t) - F x‖ / ‖F (v t) - F x‖) := by
              rw [ENNReal.ofReal_mul hκ_nonneg]
    have hκ_tendsto : Tendsto κ l (nhds K) := by
      have hμ_ne : μ ≠ 0 := hμ_pos.ne'
      have hκ_cont :
          ContinuousAt
            (fun r : ℝ ↦
              (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * r) /
                ((1 / μ) - (γ : ℝ) * r))
            0 := by
        exact
          (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.div
            ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt)
            (by simpa [hμ_ne] using one_div_ne_zero hμ_ne)
      have hκ_zero :
          (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * 0) / ((1 / μ) - (γ : ℝ) * 0) = K := by
        calc
          (‖(A : E →L[ℝ] E)‖ + (γ : ℝ) * 0) / ((1 / μ) - (γ : ℝ) * 0)
              = ‖(A : E →L[ℝ] E)‖ / (1 / μ) := by ring_nf
          _ = ‖(A : E →L[ℝ] E)‖ * μ := by
                field_simp [hμ_ne]
          _ = K := by rfl
      exact hκ_zero ▸ (hκ_cont.tendsto.comp (by simpa [ω] using hω))
    have hfactor_tendsto : Tendsto factor l (nhds (ENNReal.ofReal K)) := by
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hκ_tendsto
    have hfactor_limsup : l.limsup factor = ENNReal.ofReal K := by
      exact Filter.Tendsto.limsup_eq hfactor_tendsto
    have hlhs_le :
        l.limsup lhs ≤ l.limsup (fun t ↦ factor t * rhs t) := by
      exact Filter.limsup_le_limsup hpointwise
    have hmul_le :
        l.limsup (fun t ↦ factor t * rhs t) ≤ ENNReal.ofReal K * l.limsup rhs := by
      have hmul_raw :
          l.limsup (factor * rhs) ≤ l.limsup factor * l.limsup rhs := by
        exact ENNReal.limsup_mul_le' (f := l) (u := factor) (v := rhs)
          (Or.inl (by
            rw [hfactor_limsup]
            exact ne_of_gt (ENNReal.ofReal_pos.mpr hK_pos)))
          (Or.inl (by
            rw [hfactor_limsup]
            simp))
      have hmul :
          l.limsup (factor * rhs) ≤ ENNReal.ofReal K * l.limsup rhs := by
        simpa [hfactor_limsup] using hmul_raw
      change l.limsup (factor * rhs) ≤ ENNReal.ofReal K * l.limsup rhs
      exact hmul
    simpa [lhs, rhs, K, μ, ENNReal.ofReal_mul (norm_nonneg _)] using hlhs_le.trans hmul_le

end Corollary126
