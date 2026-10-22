/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Tactic.NormNum
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_1_11.Path
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_1_2

noncomputable section

section

variable {n : ℕ}

-- Local declaration justification (source-local notation): this item follows the book's fixed
-- trust-region step space `ℝ^n`, and keeping `Point` file-local avoids exporting a redundant
-- public alias solely for theorem readability.
local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * Primary domain: step-space trust-region geometry for the Chapter 6 owner
--   `TrustRegionSubproblem`.
-- * Inspected owner/data declarations: `TrustRegionSubproblem.quadraticModel`,
--   `TrustRegionSubproblem.cauchyPoint`, `TrustRegionSubproblem.newtonStep`, and
--   `TrustRegionSubproblem.doglegPath`.
-- * Primitive owner data already lives in `TrustRegionSubproblem`; the Cauchy point and Newton
--   step are derived owner API.
-- * The reusable double-dogleg ratio/path and breakpoint API now lives in the item-owned
--   foundation module `Theorem_6_1_11.Path`.
-- * This file keeps only the source-facing monotonicity theorems and theorem-local proof helpers
--   in the positive-definite Hessian regime. Translated `xk + …` points remain bridge
--   expressions for source-facing distance statements.

namespace TrustRegionSubproblem

/-- Helper for Chapter06 Theorem 6.1.11: on the second double-dogleg segment from the Cauchy
point to `η s_k^N`, the displacement initially points outward from the Cauchy point when
`γ ≤ η`. -/
theorem inner_cauchyPoint_intermediateNewtonStep_sub_nonneg
    (P : TrustRegionSubproblem n) (h_hessianApprox_posDef : P.hessianApprox.PosDef) (η : ℝ)
    (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η) :
    0 ≤ dotProduct P.cauchyPoint.ofLp
      ((P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η -
          P.cauchyPoint).ofLp) := by
  by_cases h_grad : P.gradient = 0
  · have hcauchy : P.cauchyPoint = 0 := by
      -- The zero-gradient branch collapses both the Cauchy point and the Newton step.
      rw [P.cauchyPoint_eq, P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad, smul_zero]
    have hnewton : P.newtonStep h_hessianApprox_posDef.isUnit = 0 := by
      rw [newtonStep, h_grad]
      simp
    simp [doubleDoglegIntermediateNewtonStep, hcauchy, hnewton]
  · let α : ℝ := P.cauchyPointScale * P.radius / ‖P.gradient‖
    let invQuad : ℝ :=
      dotProduct P.gradient.ofLp ((P.hessianApprox⁻¹).mulVec P.gradient.ofLp)
    let gDot : ℝ := dotProduct P.gradient.ofLp P.gradient.ofLp
    have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
    have h_grad_ofLp : P.gradient.ofLp ≠ 0 := by
      simpa using h_grad
    have hcurv_pos : 0 < P.gradientCurvature := by
      -- Positive definiteness makes the curvature strictly positive away from `g = 0`.
      simpa [TrustRegionSubproblem.gradientCurvature] using
        h_hessianApprox_posDef.dotProduct_mulVec_pos h_grad_ofLp
    have hcauchy :
        P.cauchyPoint = -(α : ℝ) • P.gradient := by
      -- Use the closed form of the Cauchy point on the gradient ray.
      simpa [α] using P.cauchyPoint_eq_of_ne_zero h_grad
    have hscale_eq :
        P.cauchyPointScale =
          min ((‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) 1 := by
      exact P.cauchyPointScale_eq_min_of_pos_curvature hcurv_pos
    have hscale_nonneg : 0 ≤ P.cauchyPointScale := by
      -- The positive-curvature Cauchy scale is the minimum of two nonnegative scalars.
      rw [hscale_eq]
      refine le_min ?_ zero_le_one
      exact div_nonneg (by positivity) (mul_nonneg P.radius_pos.le hcurv_pos.le)
    have hα_nonneg : 0 ≤ α := by
      exact div_nonneg (mul_nonneg hscale_nonneg P.radius_pos.le) hnorm_pos.le
    have hgDot_eq : gDot = ‖P.gradient‖ ^ (2 : ℕ) := by
      -- Normalize the gradient self-dot-product to the Euclidean norm square.
      simpa [gDot, dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq P.gradient).symm
    have hgDot_nonneg : 0 ≤ gDot := by
      rw [hgDot_eq]
      positivity
    have hscale_upper :
        P.cauchyPointScale ≤
          (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) := by
      rw [hscale_eq]
      exact min_le_left _ _
    have hα_le :
        α ≤ gDot / P.gradientCurvature := by
      -- The Cauchy-point truncation gives the same sharp upper bound as in Exercise 6.7.
      have hscale_mul :
          P.cauchyPointScale * (P.radius * P.gradientCurvature) ≤ ‖P.gradient‖ ^ (3 : ℕ) := by
        have hmul :=
          mul_le_mul_of_nonneg_right hscale_upper (mul_nonneg P.radius_pos.le hcurv_pos.le)
        have hmul' := hmul
        have hden_pos : 0 < P.radius * P.gradientCurvature := mul_pos P.radius_pos hcurv_pos
        field_simp [hden_pos.ne'] at hmul'
        have hr_cancel :
            P.radius * ‖P.gradient‖ ^ (3 : ℕ) / P.radius = ‖P.gradient‖ ^ (3 : ℕ) := by
          field_simp [P.radius_pos.ne']
        simpa [mul_assoc, hr_cancel] using hmul'
      have hα_mul : α * P.gradientCurvature ≤ ‖P.gradient‖ ^ (2 : ℕ) := by
        have hdiv :
            (P.cauchyPointScale * P.radius * P.gradientCurvature) / ‖P.gradient‖ ≤
              ‖P.gradient‖ ^ (2 : ℕ) := by
          exact (div_le_iff₀ hnorm_pos).2
            (by
              simpa [pow_two, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hscale_mul)
        simpa [α, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      have hα_le_norm : α ≤ ‖P.gradient‖ ^ (2 : ℕ) / P.gradientCurvature := by
        exact (le_div_iff₀ hcurv_pos).2
          (by simpa [mul_assoc, mul_left_comm, mul_comm] using hα_mul)
      simpa [hgDot_eq] using hα_le_norm
    have hquartic_div :
        gDot ^ (2 : ℕ) / P.gradientCurvature ≤ invQuad := by
      -- Convert the inverse-Hessian estimate from Exercise 6.7 into a bound on `gᵀ B⁻¹ g`.
      have hquartic := P.gradientNormFourth_le_gradientCurvature_mul_inverseQuadratic
        h_hessianApprox_posDef
      have hdiv : ‖P.gradient‖ ^ (4 : ℕ) / P.gradientCurvature ≤ invQuad := by
        exact (div_le_iff₀ hcurv_pos).2
          (by simpa [invQuad, mul_comm, mul_left_comm, mul_assoc] using hquartic)
      have hgDot_sq : gDot ^ (2 : ℕ) = ‖P.gradient‖ ^ (4 : ℕ) := by
        rw [hgDot_eq]
        ring
      simpa [hgDot_sq] using hdiv
    have h_invQuad_pos : 0 < invQuad := by
      have hgrad_fourth_pos : 0 < ‖P.gradient‖ ^ (4 : ℕ) := by positivity
      have hcurv_inv_pos : 0 < P.gradientCurvature * invQuad := by
        exact lt_of_lt_of_le hgrad_fourth_pos
          (P.gradientNormFourth_le_gradientCurvature_mul_inverseQuadratic h_hessianApprox_posDef)
      by_contra h_invQuad_nonpos
      have h_rhs_nonpos : P.gradientCurvature * invQuad ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hcurv_pos.le (not_lt.mp h_invQuad_nonpos)
      linarith
    have hgamma_invQuad :
        P.doubleDoglegGamma h_hessianApprox_posDef.isUnit * invQuad =
          gDot ^ (2 : ℕ) / P.gradientCurvature := by
      -- Rewrite the double-dogleg denominator to the coordinate inverse-Hessian quadratic form.
      have hnewton_dot :
          -dotProduct P.gradient (P.newtonStep h_hessianApprox_posDef.isUnit) = invQuad := by
        have hcoord :
            dotProduct P.gradient.ofLp (P.newtonStep h_hessianApprox_posDef.isUnit).ofLp =
              -invQuad := by
          simp [invQuad, P.ofLp_newtonStep_eq_neg_mulVec_inv h_hessianApprox_posDef.isUnit]
        simpa using congrArg Neg.neg hcoord
      rw [doubleDoglegGamma, hnewton_dot]
      field_simp [hcurv_pos.ne', h_invQuad_pos.ne']
      rw [hgDot_eq]
      ring
    have hα_self_le_gamma_inv : α * gDot ≤
        P.doubleDoglegGamma h_hessianApprox_posDef.isUnit * invQuad := by
      -- Combine the Cauchy-point bound with the quartic estimate encoded in `γ`.
      have hmul := mul_le_mul_of_nonneg_left hα_le hgDot_nonneg
      have hupper_eq :
          gDot * (gDot / P.gradientCurvature) =
            P.doubleDoglegGamma h_hessianApprox_posDef.isUnit * invQuad := by
        calc
          gDot * (gDot / P.gradientCurvature) = gDot ^ (2 : ℕ) / P.gradientCurvature := by
            field_simp [pow_two, hcurv_pos.ne']
          _ = P.doubleDoglegGamma h_hessianApprox_posDef.isUnit * invQuad := by
            symm
            exact hgamma_invQuad
      have hupper : gDot * (gDot / P.gradientCurvature) ≤
          P.doubleDoglegGamma h_hessianApprox_posDef.isUnit * invQuad := by
        simp [hupper_eq]
      exact le_trans
        (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul)
        hupper
    have hα_self_le_eta_inv : α * gDot ≤ η * invQuad := by
      have hgamma_scaled :=
        mul_le_mul_of_nonneg_right h_gamma_le_eta h_invQuad_pos.le
      exact le_trans hα_self_le_gamma_inv hgamma_scaled
    have hdiff_nonneg : 0 ≤ η * invQuad - α * gDot := by
      linarith
    have hfactor_nonneg : 0 ≤ α * (η * invQuad - α * gDot) := by
      positivity
    have hcoords :
        dotProduct P.cauchyPoint.ofLp
          ((P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η -
              P.cauchyPoint).ofLp) =
          α * (η * invQuad - α * gDot) := by
      -- Expand the Cauchy and Newton formulas in coordinates and collect the scalar factors.
      have hstep_coords :
          (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η -
              P.cauchyPoint).ofLp =
            η • (P.newtonStep h_hessianApprox_posDef.isUnit).ofLp -
              (-(α : ℝ) • P.gradient.ofLp) := by
        simp [doubleDoglegIntermediateNewtonStep, hcauchy]
      rw [show P.cauchyPoint.ofLp = -(α : ℝ) • P.gradient.ofLp by simp [hcauchy]]
      rw [hstep_coords]
      simp [invQuad, gDot, P.ofLp_newtonStep_eq_neg_mulVec_inv h_hessianApprox_posDef.isUnit,
        dotProduct_add, dotProduct_smul, dotProduct_comm, mul_comm, mul_left_comm,
        sub_eq_add_neg]
      ring
    rw [hcoords]
    exact hfactor_nonneg

/-- First claim in Chapter06 Theorem 6.1.11: the norm of the step-valued double-dogleg path is
monotone on `τ ∈ [0, 2]`. -/
theorem norm_doubleDoglegPath_monotoneOn
    (P : TrustRegionSubproblem n) (h_hessianApprox_posDef : P.hessianApprox.PosDef) (η : ℝ)
    (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η)
    (h_eta_le_one : η ≤ 1) :
    MonotoneOn (fun τ : ℝ ↦ ‖P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ‖)
      (Set.Icc (0 : ℝ) 2) := by
  have _ := h_eta_le_one
  intro a ha b hb hab
  by_cases hb_one : b ≤ 1
  · have ha_one : a ≤ 1 := le_trans hab hb_one
    -- The first leg is the same ray through the Cauchy point as in the standard dogleg path.
    have hray : ‖a • P.cauchyPoint‖ ≤ ‖b • P.cauchyPoint‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.1, Real.norm_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hab (norm_nonneg P.cauchyPoint)
    simpa [P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit η a
      ha_one,
      P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit η b hb_one]
      using hray
  · have hb_one_lt : 1 < b := lt_of_not_ge hb_one
    by_cases ha_one : a ≤ 1
    · have ha_to_cauchy :
          ‖P.doubleDoglegPath h_hessianApprox_posDef.isUnit η a‖ ≤ ‖P.cauchyPoint‖ := by
        -- The first leg reaches the Cauchy point monotonically at `τ = 1`.
        have hray : ‖a • P.cauchyPoint‖ ≤ ‖P.cauchyPoint‖ := by
          rw [norm_smul, Real.norm_of_nonneg ha.1]
          simpa using mul_le_mul_of_nonneg_right ha_one (norm_nonneg P.cauchyPoint)
        simpa [P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit η a
          ha_one] using hray
      have hsecond :
          ‖P.cauchyPoint‖ ≤ ‖P.doubleDoglegPath h_hessianApprox_posDef.isUnit η b‖ := by
        have hmono :
            MonotoneOn
              (fun t : ℝ ↦
                ‖P.cauchyPoint + t •
                  (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η -
                    P.cauchyPoint)‖)
              (Set.Ici (0 : ℝ)) :=
          norm_add_smul_sub_monotoneOn_of_inner_nonneg
            (P.inner_cauchyPoint_intermediateNewtonStep_sub_nonneg
              h_hessianApprox_posDef η h_gamma_le_eta)
        have hzero : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by
          simp
        have hb_shift : b - 1 ∈ Set.Ici (0 : ℝ) := by
          simpa [Set.mem_Ici] using sub_nonneg.mpr hb_one_lt.le
        have hb_shift_nonneg : (0 : ℝ) ≤ b - 1 := by
          linarith
        have hseg := hmono hzero hb_shift hb_shift_nonneg
        simpa [P.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
          h_hessianApprox_posDef.isUnit η b hb_one_lt hb.2] using hseg
      exact le_trans ha_to_cauchy hsecond
    · have ha_one_lt : 1 < a := lt_of_not_ge ha_one
      have hmono :
          MonotoneOn
            (fun t : ℝ ↦
              ‖P.cauchyPoint + t •
                (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η -
                  P.cauchyPoint)‖)
            (Set.Ici (0 : ℝ)) :=
        norm_add_smul_sub_monotoneOn_of_inner_nonneg
          (P.inner_cauchyPoint_intermediateNewtonStep_sub_nonneg
            h_hessianApprox_posDef η h_gamma_le_eta)
      have ha_shift : a - 1 ∈ Set.Ici (0 : ℝ) := by
        simpa [Set.mem_Ici] using sub_nonneg.mpr ha_one_lt.le
      have hb_shift : b - 1 ∈ Set.Ici (0 : ℝ) := by
        simpa [Set.mem_Ici] using sub_nonneg.mpr hb_one_lt.le
      have hab_shift : a - 1 ≤ b - 1 := by
        linarith
      have hseg := hmono ha_shift hb_shift hab_shift
      -- The second leg reuses the generic segment-norm monotonicity from Exercise 6.7.
      simpa [P.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
        h_hessianApprox_posDef.isUnit η a ha_one_lt ha.2,
        P.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
          h_hessianApprox_posDef.isUnit η b hb_one_lt hb.2] using hseg

/-- Along the first double-dogleg segment, the trust-region quadratic model does not increase. -/
theorem quadraticModel_cauchyPoint_le_quadraticModel_zero
    (P : TrustRegionSubproblem n) :
    P P.cauchyPoint ≤ P 0 := by
  rcases P.cauchyPoint_isCauchyPointOnGradientRay with ⟨_, hmin⟩
  have hzero_mem : (0 : Point) ∈ P.gradientRayFeasibleSet := by
    refine ⟨?_, ?_⟩
    · rw [TrustRegionSubproblem.mem_feasibleSet_iff]
      simpa using P.radius_pos.le
    · refine ⟨0, le_rfl, by simp⟩
  -- The Cauchy point minimizes the quadratic model on the feasible gradient ray,
  -- and that ray contains `0`.
  exact (isMinOn_iff.mp hmin) 0 hzero_mem

variable (P : TrustRegionSubproblem n) (h_hessianApprox_posDef : P.hessianApprox.PosDef) (η : ℝ)
variable (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η)
variable (h_eta_le_one : η ≤ 1)

/-- Helper for Chapter06 Theorem 6.1.11: applying the Hessian approximation to the Newton step
returns `-g_k`. -/
theorem hessianApprox_mulVec_newtonStep_eq_neg_gradient
    :
    P.hessianApprox.mulVec (P.newtonStep h_hessianApprox_posDef.isUnit) = -P.gradient := by
  letI := h_hessianApprox_posDef.isUnit.invertible
  ext i
  have hcoord :
      P.hessianApprox.mulVec (P.newtonStep h_hessianApprox_posDef.isUnit).ofLp =
        -P.gradient.ofLp := by
    -- Apply `B_k` to the coordinate Newton-step formula `-B_k⁻¹ g_k`.
    calc
      P.hessianApprox.mulVec (P.newtonStep h_hessianApprox_posDef.isUnit).ofLp
          = P.hessianApprox.mulVec
              (-((P.hessianApprox⁻¹).mulVec P.gradient.ofLp)) := by
            rw [P.ofLp_newtonStep_eq_neg_mulVec_inv h_hessianApprox_posDef.isUnit]
      _ = -P.hessianApprox.mulVec ((P.hessianApprox⁻¹).mulVec P.gradient.ofLp) := by
            rw [Matrix.mulVec_neg]
      _ = -((P.hessianApprox * P.hessianApprox⁻¹).mulVec P.gradient.ofLp) := by
            rw [Matrix.mulVec_mulVec]
      _ = -P.gradient.ofLp := by
            simp
  simpa using congrFun hcoord i

/-- Helper for Chapter06 Theorem 6.1.11: along the first double-dogleg leg, the quadratic model
decreases as the point moves from `0` to the Cauchy point. -/
theorem quadraticModel_antitoneOn_cauchy_ray
    :
    AntitoneOn (fun τ : ℝ ↦ P (τ • P.cauchyPoint)) (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases h_grad : P.gradient = 0
  · have hcauchy : P.cauchyPoint = 0 := by
      -- The zero-gradient branch collapses the whole first leg to the origin.
      rw [P.cauchyPoint_eq, P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad, smul_zero]
    simp [hcauchy]
  · let ua : ℝ := a * P.cauchyPointScale
    let ub : ℝ := b * P.cauchyPointScale
    have hnorm_pos : 0 < ‖P.gradient‖ := norm_pos_iff.mpr h_grad
    have hscale_nonneg : 0 ≤ P.cauchyPointScale := P.cauchyPointScale_nonneg
    have hua_nonneg : 0 ≤ ua := by
      exact mul_nonneg ha.1 hscale_nonneg
    have hub_nonneg : 0 ≤ ub := by
      exact mul_nonneg hb.1 hscale_nonneg
    have huab : ua ≤ ub := by
      exact mul_le_mul_of_nonneg_right hab hscale_nonneg
    have hub_le_scale : ub ≤ P.cauchyPointScale := by
      simpa [ub] using mul_le_mul_of_nonneg_right hb.2 hscale_nonneg
    have hpred_mono :
        P.predictedReduction (ua • P.gradientBoundaryStep) ≤
          P.predictedReduction (ub • P.gradientBoundaryStep) := by
      by_cases h_curv : P.gradientCurvature ≤ 0
      · have hdiff_formula (u v : ℝ) :
            P.predictedReduction (v • P.gradientBoundaryStep) -
                P.predictedReduction (u • P.gradientBoundaryStep) =
              P.radius * (v - u) *
                  (2 * ‖P.gradient‖ ^ (3 : ℕ) -
                    P.radius * P.gradientCurvature * (u + v)) /
                (2 * ‖P.gradient‖ ^ (2 : ℕ)) := by
          rw [P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad v,
            P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad u]
          field_simp [pow_two, hnorm_pos.ne']
          ring
        have hcurv_scaled_nonpos :
            P.radius * P.gradientCurvature * (ua + ub) ≤ 0 := by
          have hradius_curv_nonpos : P.radius * P.gradientCurvature ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos P.radius_pos.le h_curv
          exact
            mul_nonpos_of_nonpos_of_nonneg hradius_curv_nonpos
              (add_nonneg hua_nonneg hub_nonneg)
        have hfactor_nonneg :
            0 ≤ 2 * ‖P.gradient‖ ^ (3 : ℕ) -
              P.radius * P.gradientCurvature * (ua + ub) := by
          have hnorm_cube_nonneg : 0 ≤ 2 * ‖P.gradient‖ ^ (3 : ℕ) := by
            positivity
          nlinarith
        have hdiff_nonneg :
            0 ≤ P.predictedReduction (ub • P.gradientBoundaryStep) -
              P.predictedReduction (ua • P.gradientBoundaryStep) := by
          rw [hdiff_formula ua ub]
          exact div_nonneg
            (mul_nonneg (mul_nonneg P.radius_pos.le (sub_nonneg.mpr huab)) hfactor_nonneg)
            (by positivity)
        linarith
      · let ρ : ℝ := (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)
        have h_curv_pos : 0 < P.gradientCurvature := lt_of_not_ge h_curv
        have hρ_pos : 0 < ρ := by
          unfold ρ
          exact div_pos (pow_pos hnorm_pos _) (mul_pos P.radius_pos h_curv_pos)
        have hscale_le_rho : P.cauchyPointScale ≤ ρ := by
          rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv_pos]
          exact min_le_left _ _
        have hub_le_rho : ub ≤ ρ := le_trans hub_le_scale hscale_le_rho
        have hua_le_rho : ua ≤ ρ := le_trans huab hub_le_rho
        have hpred_rho_form (u : ℝ) :
            P.predictedReduction (u • P.gradientBoundaryStep) =
              P.radius * ‖P.gradient‖ * u -
                ((P.radius * ‖P.gradient‖) / (2 * ρ)) * u ^ (2 : ℕ) := by
          rw [P.predictedReduction_smul_gradientBoundaryStep_eq_of_ne_zero h_grad u]
          unfold ρ
          field_simp [ρ, pow_two, hnorm_pos.ne', (ne_of_gt P.radius_pos), h_curv_pos.ne']
        have hdiff_formula (u v : ℝ) :
            P.predictedReduction (v • P.gradientBoundaryStep) -
                P.predictedReduction (u • P.gradientBoundaryStep) =
              ((P.radius * ‖P.gradient‖) / (2 * ρ)) * (v - u) * (2 * ρ - u - v) := by
          rw [hpred_rho_form u, hpred_rho_form v]
          field_simp [hρ_pos.ne']
          ring
        have hcoeff_nonneg : 0 ≤ (P.radius * ‖P.gradient‖) / (2 * ρ) := by
          exact div_nonneg (mul_nonneg P.radius_pos.le hnorm_pos.le) (by positivity)
        have htail_nonneg : 0 ≤ 2 * ρ - ua - ub := by
          nlinarith
        have hdiff_nonneg :
            0 ≤ P.predictedReduction (ub • P.gradientBoundaryStep) -
              P.predictedReduction (ua • P.gradientBoundaryStep) := by
          rw [hdiff_formula ua ub]
          exact mul_nonneg (mul_nonneg hcoeff_nonneg (sub_nonneg.mpr huab)) htail_nonneg
        linarith
    -- Convert the ray comparison back from predicted reduction to the quadratic model.
    have hmodel_ray :
        P (ub • P.gradientBoundaryStep) ≤ P (ua • P.gradientBoundaryStep) := by
      have hpred_model := hpred_mono
      rw [TrustRegionSubproblem.predictedReduction_eq, TrustRegionSubproblem.predictedReduction_eq]
        at hpred_model
      linarith
    simpa [ua, ub, P.cauchyPoint_eq, smul_smul] using hmodel_ray

/-- Helper for Chapter06 Theorem 6.1.11: the quadratic model on the Newton ray is the scalar
quadratic `q(0) - (t - t^2 / 2) (-g_kᵀ s_k^N)`. -/
theorem quadraticModel_scaled_newtonStep_eq
    (t : ℝ)
    :
    P (t • P.newtonStep h_hessianApprox_posDef.isUnit) =
      P 0 -
        (t - t ^ (2 : ℕ) / 2) *
          (-dotProduct P.gradient (P.newtonStep h_hessianApprox_posDef.isUnit)) := by
  let sN : Point := P.newtonStep h_hessianApprox_posDef.isUnit
  have hsN :
      P.hessianApprox.mulVec sN = -P.gradient := by
    simpa [sN] using
      TrustRegionSubproblem.hessianApprox_mulVec_newtonStep_eq_neg_gradient
        P h_hessianApprox_posDef
  have hinc :
      P (t • sN) - P 0 =
        t * dotProduct P.gradient sN +
          (1 / 2 : ℝ) * t ^ (2 : ℕ) *
            dotProduct sN (P.hessianApprox.mulVec sN) := by
    -- Specialize the quadratic increment formula to the Newton ray from the origin.
    simpa [sN] using
      TrustRegionSubproblem.quadraticModel_increment_eq P (0 : Point) sN t
  calc
    P (t • sN)
        = P 0 +
            (t * dotProduct P.gradient sN +
              (1 / 2 : ℝ) * t ^ (2 : ℕ) *
                dotProduct sN (P.hessianApprox.mulVec sN)) := by
            linarith
    _ = P 0 -
          (t - t ^ (2 : ℕ) / 2) *
            (-dotProduct P.gradient sN) := by
          rw [hsN]
          simp [dotProduct_comm]
          ring

/-- Helper for Chapter06 Theorem 6.1.11: along the Newton ray from `η s_k^N` to `s_k^N`, the
quadratic model decreases. -/
theorem quadraticModel_antitoneOn_scaled_newtonStep
    :
    AntitoneOn (fun t : ℝ ↦ P (t • P.newtonStep h_hessianApprox_posDef.isUnit))
      (Set.Icc η 1) := by
  intro a ha b hb hab
  have hcoeff_nonneg :
      0 ≤ -dotProduct P.gradient (P.newtonStep h_hessianApprox_posDef.isUnit) := by
    have hquad_nonneg :=
      h_hessianApprox_posDef.posSemidef.dotProduct_mulVec_nonneg
        (P.newtonStep h_hessianApprox_posDef.isUnit)
    rw [P.hessianApprox_mulVec_newtonStep_eq_neg_gradient h_hessianApprox_posDef] at hquad_nonneg
    simpa [dotProduct_comm] using hquad_nonneg
  have hscalar_mono :
      a - a ^ (2 : ℕ) / 2 ≤ b - b ^ (2 : ℕ) / 2 := by
    -- The scalar Newton-ray model has derivative `1 - t`, so it increases on `(-∞, 1]`.
    nlinarith [hab, hb.2]
  have hmodel_ray :
      P (b • P.newtonStep h_hessianApprox_posDef.isUnit) ≤
        P (a • P.newtonStep h_hessianApprox_posDef.isUnit) := by
    rw [P.quadraticModel_scaled_newtonStep_eq h_hessianApprox_posDef b,
      P.quadraticModel_scaled_newtonStep_eq h_hessianApprox_posDef a]
    nlinarith
  simpa using hmodel_ray

/-- Helper for Chapter06 Theorem 6.1.11: along the middle double-dogleg leg from the Cauchy
point to `η s_k^N`, the quadratic model decreases. -/
theorem quadraticModel_antitoneOn_cauchy_to_intermediate
    (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η)
    (h_eta_le_one : η ≤ 1)
    :
    AntitoneOn
      (fun t : ℝ ↦
        P
          (P.cauchyPoint + t •
            (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η -
              P.cauchyPoint)))
      (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases h_grad : P.gradient = 0
  · have hcauchy : P.cauchyPoint = 0 := by
      -- The zero-gradient branch collapses both breakpoints to the origin.
      rw [P.cauchyPoint_eq, P.gradientBoundaryStep_eq_zero_of_eq_zero h_grad, smul_zero]
    have hnewton : P.newtonStep h_hessianApprox_posDef.isUnit = 0 := by
      rw [newtonStep, h_grad]
      simp
    simp [doubleDoglegIntermediateNewtonStep, hcauchy, hnewton]
  · let d : Point :=
      P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η - P.cauchyPoint
    let m : ℝ :=
      dotProduct P.gradient d + dotProduct d (P.hessianApprox.mulVec P.cauchyPoint)
    let q : ℝ := dotProduct d (P.hessianApprox.mulVec d)
    have hq_nonneg : 0 ≤ q := by
      -- Positive semidefiniteness controls the quadratic coefficient on the segment.
      unfold q
      exact h_hessianApprox_posDef.posSemidef.dotProduct_mulVec_nonneg d
    have hone_sub_eta_nonneg : 0 ≤ 1 - η := by
      nlinarith
    have hgrad_d_nonpos : dotProduct P.gradient d ≤ 0 := by
      let α : ℝ := P.cauchyPointScale * P.radius / ‖P.gradient‖
      have hcauchy : P.cauchyPoint = -(α : ℝ) • P.gradient := by
        simpa [α] using P.cauchyPoint_eq_of_ne_zero h_grad
      have hscale_pos : 0 < P.cauchyPointScale := by
        by_cases h_curv : P.gradientCurvature ≤ 0
        · rw [P.cauchyPointScale_eq_one_of_nonpos_curvature h_curv]
          norm_num
        · have h_curv_pos : 0 < P.gradientCurvature := lt_of_not_ge h_curv
          rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv_pos]
          have hratio_pos :
              0 < (‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature) := by
            exact div_pos (pow_pos (norm_pos_iff.mpr h_grad) _) (mul_pos P.radius_pos h_curv_pos)
          exact lt_min hratio_pos zero_lt_one
      have hα_pos : 0 < α := by
        exact div_pos (mul_pos hscale_pos P.radius_pos) (norm_pos_iff.mpr h_grad)
      have hcpd_nonneg : 0 ≤ dotProduct P.cauchyPoint.ofLp d.ofLp := by
        simpa [d] using
          P.inner_cauchyPoint_intermediateNewtonStep_sub_nonneg
            h_hessianApprox_posDef η h_gamma_le_eta
      have hcoords :
          dotProduct P.cauchyPoint.ofLp d.ofLp =
            -α * dotProduct P.gradient.ofLp d.ofLp := by
        have hcauchy_ofLp : P.cauchyPoint.ofLp = -(α : ℝ) • P.gradient.ofLp := by
          simp [hcauchy]
        rw [hcauchy_ofLp]
        simp
      rw [hcoords] at hcpd_nonneg
      have hcoord_nonpos : dotProduct P.gradient.ofLp d.ofLp ≤ 0 := by
        nlinarith
      simpa using hcoord_nonpos
    have hBsη :
        P.hessianApprox.mulVec
            (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η) =
          -η • P.gradient := by
      -- The intermediate point is the scaled Newton step, so applying `B_k` is explicit.
      calc
        P.hessianApprox.mulVec
            (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η)
            = η • P.hessianApprox.mulVec (P.newtonStep h_hessianApprox_posDef.isUnit) := by
                simp [doubleDoglegIntermediateNewtonStep, Matrix.mulVec_smul]
        _ = η • (-P.gradient) := by
          rw [P.hessianApprox_mulVec_newtonStep_eq_neg_gradient h_hessianApprox_posDef]
        _ = -η • P.gradient := by
          simp
    have hmq_nonpos : m + q ≤ 0 := by
      have hd_sum :
          P.cauchyPoint + d =
            P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η := by
        simp [d]
      have hmq_eq : m + q = (1 - η) * dotProduct P.gradient d := by
        unfold m q
        calc
          dotProduct P.gradient d +
              dotProduct d (P.hessianApprox.mulVec P.cauchyPoint) +
              dotProduct d (P.hessianApprox.mulVec d)
              =
            dotProduct P.gradient d +
              dotProduct d (P.hessianApprox.mulVec (P.cauchyPoint + d)) := by
                rw [Matrix.mulVec_add, dotProduct_add]
                ring
          _ =
              dotProduct P.gradient d +
                dotProduct d (P.hessianApprox.mulVec
                  (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η)) := by
                simp [d]
          _ = dotProduct P.gradient d + dotProduct d (-η • P.gradient) := by
                rw [hBsη]
          _ = (1 - η) * dotProduct P.gradient d := by
                simp [dotProduct_comm]
                ring
      rw [hmq_eq]
      nlinarith
    have hslope_nonpos : m + ((a + b) / 2) * q ≤ 0 := by
      -- The segment slope is affine increasing, so the endpoint slope controls the whole interval.
      nlinarith [hmq_nonpos, hq_nonneg, ha.1, hb.2]
    have hdiff_nonpos :
        b * m + (1 / 2 : ℝ) * b ^ (2 : ℕ) * q ≤
          a * m + (1 / 2 : ℝ) * a ^ (2 : ℕ) * q := by
      have hfac :
          b * m + (1 / 2 : ℝ) * b ^ (2 : ℕ) * q -
              (a * m + (1 / 2 : ℝ) * a ^ (2 : ℕ) * q) =
            (b - a) * (m + ((a + b) / 2) * q) := by
        ring
      have hmul_nonpos :
          (b - a) * (m + ((a + b) / 2) * q) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) hslope_nonpos
      nlinarith [hfac, hmul_nonpos]
    have ha_model :
        P (P.cauchyPoint + a • d) =
          P P.cauchyPoint + (a * m + (1 / 2 : ℝ) * a ^ (2 : ℕ) * q) := by
      have hinc :
          P (P.cauchyPoint + a • d) - P P.cauchyPoint =
            a * m + (1 / 2 : ℝ) * a ^ (2 : ℕ) * q := by
        have hraw := P.quadraticModel_increment_eq P.cauchyPoint d a
        unfold m q
        ring_nf at hraw ⊢
        exact hraw
      linarith
    have hb_model :
        P (P.cauchyPoint + b • d) =
          P P.cauchyPoint + (b * m + (1 / 2 : ℝ) * b ^ (2 : ℕ) * q) := by
      have hinc :
          P (P.cauchyPoint + b • d) - P P.cauchyPoint =
            b * m + (1 / 2 : ℝ) * b ^ (2 : ℕ) * q := by
        have hraw := P.quadraticModel_increment_eq P.cauchyPoint d b
        unfold m q
        ring_nf at hraw ⊢
        exact hraw
      linarith
    -- Route correction: once the one-variable quadratic is normalized, a single factorization
    -- controls the monotonicity on the whole segment.
    have hsegment :
        P (P.cauchyPoint + b • d) ≤ P (P.cauchyPoint + a • d) := by
      rw [hb_model, ha_model]
      nlinarith
    simpa [d] using hsegment

/-- Helper for Chapter06 Theorem 6.1.11: on `τ ∈ [1, 2]`, the double-dogleg path is the
shifted segment from the Cauchy point to `η s_k^N`, including the left endpoint `τ = 1`. -/
theorem doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_le_of_le_two
    (τ : ℝ) (hτ₁ : 1 ≤ τ) (hτ₂ : τ ≤ 2)
    :
    P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ =
      P.cauchyPoint + (τ - 1) •
        (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η - P.cauchyPoint) := by
  by_cases hτ : τ = 1
  · subst hτ
    -- At the breakpoint `τ = 1`, the shifted segment formula reduces to the Cauchy point.
    simp [doubleDoglegIntermediateNewtonStep]
  · have hτ_lt : 1 < τ := lt_of_le_of_ne hτ₁ (Ne.symm hτ)
    -- Away from the breakpoint, reuse the existing open-interval segment formula.
    simpa using
      P.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_lt_of_le_two
        h_hessianApprox_posDef.isUnit η τ hτ_lt hτ₂

/-- Helper for Chapter06 Theorem 6.1.11: along the first double-dogleg leg, the quadratic model
decreases along the path parameter `τ ∈ [0, 1]`. -/
  theorem quadraticModel_antitoneOn_doubleDoglegPath_firstLeg
    :
    AntitoneOn (fun τ : ℝ ↦ P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ))
      (Set.Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hmono := P.quadraticModel_antitoneOn_cauchy_ray
  have hseg := hmono ha hb hab
  -- Rewrite the first leg into the canonical Cauchy ray already handled above.
  simpa [P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit η a ha.2,
    P.doubleDoglegPath_eq_smul_cauchyPoint_of_le_one h_hessianApprox_posDef.isUnit η b hb.2]
    using hseg

/-- Helper for Chapter06 Theorem 6.1.11: along the second double-dogleg leg, the quadratic
model decreases along the path parameter `τ ∈ [1, 2]`. -/
theorem quadraticModel_antitoneOn_doubleDoglegPath_secondLeg
    (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η)
    (h_eta_le_one : η ≤ 1)
    :
    AntitoneOn (fun τ : ℝ ↦ P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ))
      (Set.Icc (1 : ℝ) 2) := by
  intro a ha b hb hab
  have ha_shift : a - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [ha.1]
    · nlinarith [ha.2]
  have hb_shift : b - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · nlinarith [hb.1]
    · nlinarith [hb.2]
  have hab_shift : a - 1 ≤ b - 1 := by
    linarith
  have hmono :=
    P.quadraticModel_antitoneOn_cauchy_to_intermediate
      h_hessianApprox_posDef η h_gamma_le_eta h_eta_le_one
  have hseg := hmono ha_shift hb_shift hab_shift
  -- Rewrite the second leg into the canonical shifted segment controlled above.
  simpa [P.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_le_of_le_two
      h_hessianApprox_posDef η a ha.1 ha.2,
    P.doubleDoglegPath_eq_cauchyPoint_add_smul_of_one_le_of_le_two
      h_hessianApprox_posDef η b hb.1 hb.2] using hseg

/-- Helper for Chapter06 Theorem 6.1.11: on the third double-dogleg leg, the path is an affine
reparameterization of the Newton ray. -/
theorem doubleDoglegPath_eq_smul_newtonStep_of_two_lt
    (τ : ℝ) (hτ : 2 < τ)
    :
    P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ =
      (η + (τ - 2) * (1 - η)) • P.newtonStep h_hessianApprox_posDef.isUnit := by
  let sN : Point := P.newtonStep h_hessianApprox_posDef.isUnit
  rw [P.doubleDoglegPath_eq_intermediateNewtonStep_add_smul_of_two_lt
    h_hessianApprox_posDef.isUnit η τ hτ]
  change η • sN + (τ - 2) • (sN - η • sN) =
    (η + (τ - 2) * (1 - η)) • sN
  calc
    η • sN + (τ - 2) • (sN - η • sN)
        = η • sN + ((τ - 2) • sN - (τ - 2) • (η • sN)) := by
            rw [smul_sub]
    _ = η • sN + ((τ - 2) • sN + (τ - 2) • (-η • sN)) := by
          simp [sub_eq_add_neg]
    _ = η • sN + ((τ - 2) • sN + (-((τ - 2) * η)) • sN) := by
          simp [smul_smul]
    _ = (η + ((τ - 2) + -((τ - 2) * η))) • sN := by
          rw [← add_smul, ← add_smul]
    _ = (η + (τ - 2) * (1 - η)) • sN := by
          congr 1
          ring

/-- Helper for Chapter06 Theorem 6.1.11: on `τ ∈ [2, ∞)`, the third double-dogleg path equals
the Newton ray with affine parameter `η + (τ - 2) (1 - η)`, including the breakpoint `τ = 2`. -/
theorem doubleDoglegPath_eq_smul_newtonStep_of_two_le
    (τ : ℝ) (hτ : 2 ≤ τ)
    :
    P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ =
      (η + (τ - 2) * (1 - η)) • P.newtonStep h_hessianApprox_posDef.isUnit := by
  by_cases hτ_eq : τ = 2
  · subst hτ_eq
    -- At the breakpoint `τ = 2`, the affine Newton parameter is exactly `η`.
    simp [doubleDoglegIntermediateNewtonStep]
  · have hτ_lt : 2 < τ := lt_of_le_of_ne hτ (Ne.symm hτ_eq)
    -- Away from the breakpoint, reuse the open third-leg parameterization.
    simpa using
      P.doubleDoglegPath_eq_smul_newtonStep_of_two_lt
        h_hessianApprox_posDef η τ hτ_lt

/-- Helper for Chapter06 Theorem 6.1.11: along the third double-dogleg leg, the quadratic model
decreases along the path parameter `τ ∈ [2, 3]`. -/
theorem quadraticModel_antitoneOn_doubleDoglegPath_thirdLeg
    (h_eta_le_one : η ≤ 1)
    :
    AntitoneOn (fun τ : ℝ ↦ P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ))
      (Set.Icc (2 : ℝ) 3) := by
  let u : ℝ → ℝ := fun τ ↦ η + (τ - 2) * (1 - η)
  have hone_sub_eta_nonneg : 0 ≤ 1 - η := by
    linarith
  have hu_mem {τ : ℝ} (hτ : τ ∈ Set.Icc (2 : ℝ) 3) : u τ ∈ Set.Icc η 1 := by
    constructor
    · -- The affine parameter starts at `η` when `τ = 2` and increases afterwards.
      dsimp [u]
      nlinarith [hone_sub_eta_nonneg, hτ.1, hτ.2]
    · -- Because `τ ≤ 3`, the affine parameter never exceeds `1`.
      dsimp [u]
      nlinarith [hone_sub_eta_nonneg, h_eta_le_one, hτ.1, hτ.2]
  intro a ha b hb hab
  have huab : u a ≤ u b := by
    -- The affine reparameterization is monotone because `1 - η ≥ 0`.
    dsimp [u]
    nlinarith [hone_sub_eta_nonneg, hab]
  have hmono := P.quadraticModel_antitoneOn_scaled_newtonStep h_hessianApprox_posDef η
  have hseg := hmono (hu_mem ha) (hu_mem hb) huab
  -- Rewrite the third leg into the affine Newton ray controlled above.
  simpa [u, P.doubleDoglegPath_eq_smul_newtonStep_of_two_le
      h_hessianApprox_posDef η a ha.1,
    P.doubleDoglegPath_eq_smul_newtonStep_of_two_le
      h_hessianApprox_posDef η b hb.1] using hseg

/-- Along the second double-dogleg segment, the trust-region quadratic model does not increase. -/
theorem quadraticModel_intermediate_le_cauchy
    (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η)
    (h_eta_le_one : η ≤ 1)
    :
    P (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η) ≤
      P P.cauchyPoint := by
  have hmono :=
    P.quadraticModel_antitoneOn_cauchy_to_intermediate h_hessianApprox_posDef η
      h_gamma_le_eta h_eta_le_one
  have hseg := hmono (by simp) (by simp) zero_le_one
  -- Specialize the middle-segment antitonicity at the two breakpoints.
  simpa [doubleDoglegIntermediateNewtonStep] using hseg

/-- Along the third double-dogleg segment, the trust-region quadratic model does not increase. -/
theorem quadraticModel_newtonStep_le_intermediate
    (h_eta_le_one : η ≤ 1)
    :
    P (P.newtonStep h_hessianApprox_posDef.isUnit) ≤
      P (P.doubleDoglegIntermediateNewtonStep h_hessianApprox_posDef.isUnit η) := by
  have hmono := P.quadraticModel_antitoneOn_scaled_newtonStep h_hessianApprox_posDef η
  have hseg := hmono ⟨le_rfl, h_eta_le_one⟩ ⟨h_eta_le_one, le_rfl⟩ h_eta_le_one
  -- Specialize the Newton-ray antitonicity at `t = η` and `t = 1`.
  simpa [doubleDoglegIntermediateNewtonStep] using hseg

/-- Chapter06 Theorem 6.1.11 (2): the trust-region quadratic model decreases monotonically along
the full step-valued double-dogleg path on `τ ∈ [0, 3]`. -/
theorem quadraticModel_antitoneOn_doubleDoglegPath
    (h_gamma_le_eta : P.doubleDoglegGamma h_hessianApprox_posDef.isUnit ≤ η)
    (h_eta_le_one : η ≤ 1)
    :
    AntitoneOn (fun τ : ℝ ↦ P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η τ))
      (Set.Icc (0 : ℝ) 3) := by
  have hfirst := P.quadraticModel_antitoneOn_doubleDoglegPath_firstLeg h_hessianApprox_posDef η
  have hsecond :=
    P.quadraticModel_antitoneOn_doubleDoglegPath_secondLeg
      h_hessianApprox_posDef η h_gamma_le_eta h_eta_le_one
  have hthird :=
    P.quadraticModel_antitoneOn_doubleDoglegPath_thirdLeg
      h_hessianApprox_posDef η h_eta_le_one
  intro a ha b hb hab
  by_cases hb_one : b ≤ 1
  · have ha_one : a ≤ 1 := le_trans hab hb_one
    -- Both parameters lie on the first leg, so the first-leg antitonicity closes the goal.
    exact hfirst ⟨ha.1, ha_one⟩ ⟨hb.1, hb_one⟩ hab
  · have hb_one_lt : 1 < b := lt_of_not_ge hb_one
    by_cases hb_two : b ≤ 2
    · by_cases ha_one : a ≤ 1
      · have hb_to_one :
            P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η b) ≤
              P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 1) := by
          -- Crossing from the second leg back to the first leg goes through `τ = 1`.
          exact hsecond (by simp) ⟨hb_one_lt.le, hb_two⟩ hb_one_lt.le
        have hone_to_ha :
            P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 1) ≤
              P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η a) := by
          exact hfirst ⟨ha.1, ha_one⟩ (by simp) ha_one
        exact le_trans hb_to_one hone_to_ha
      · have ha_one_lt : 1 < a := lt_of_not_ge ha_one
        have ha_two : a ≤ 2 := le_trans hab hb_two
        -- Both parameters lie on the second leg.
        exact hsecond ⟨ha_one_lt.le, ha_two⟩ ⟨hb_one_lt.le, hb_two⟩ hab
    · have hb_two_lt : 2 < b := lt_of_not_ge hb_two
      by_cases ha_two : a ≤ 2
      · have hb_to_two :
            P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η b) ≤
              P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 2) := by
          -- Crossing from the third leg goes first through the breakpoint `τ = 2`.
          exact hthird ⟨le_rfl, by norm_num⟩ ⟨hb_two_lt.le, hb.2⟩ hb_two_lt.le
        by_cases ha_one : a ≤ 1
        · have htwo_to_one :
              P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 2) ≤
                P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 1) := by
            exact hsecond (by simp) (by simp) one_le_two
          have hone_to_ha :
              P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 1) ≤
                P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η a) := by
            exact hfirst ⟨ha.1, ha_one⟩ (by simp) ha_one
          exact le_trans hb_to_two (le_trans htwo_to_one hone_to_ha)
        · have ha_one_lt : 1 < a := lt_of_not_ge ha_one
          have htwo_to_ha :
              P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η 2) ≤
                P (P.doubleDoglegPath h_hessianApprox_posDef.isUnit η a) := by
            exact hsecond ⟨ha_one_lt.le, ha_two⟩ (by simp) ha_two
          exact le_trans hb_to_two htwo_to_ha
      · have ha_two_lt : 2 < a := lt_of_not_ge ha_two
        -- Both parameters lie on the third leg.
        exact hthird ⟨ha_two_lt.le, ha.2⟩ ⟨hb_two_lt.le, hb.2⟩ hab

end TrustRegionSubproblem

end
