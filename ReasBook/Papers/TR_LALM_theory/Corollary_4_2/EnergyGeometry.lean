/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.DeterministicMultiplier

public section

open scoped InnerProductSpace LALM NNReal

namespace LALM.Correction

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: a bounded multiplier gives the uniform lower
bound for the augmented Lagrangian on the regularity region. -/
lemma augmentedLagrangian_lowerBound
    (h : EqualityConstrained.Regularity f c) (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (bound : ℝ)
    (hrho : 0 < rho) (hx : x ∈ h.region)
    (hmultiplier : ‖multiplier‖ ≤ bound) (hbound : 0 ≤ bound) :
    h.objectiveLower - bound ^ 2 / (2 * rho) ≤
      ℒ[f, c; rho](x, multiplier) := by
  -- Complete the penalty square after Cauchy-Schwarz and Young's inequality.
  have hinner : -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hyoungDivided :=
    div_le_div_of_nonneg_right hyoung htwoNonneg
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
    calc
      ‖multiplier‖ * ‖c x‖ = (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2) / 2 :=
        hyoungDivided
      _ = rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq : ‖multiplier‖ ^ 2 ≤ bound ^ 2 :=
    (sq_le_sq₀ (norm_nonneg multiplier) hbound).2 hmultiplier
  have htwoPos : (0 : ℝ) < 2 := by norm_num
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * rho) ≤ bound ^ 2 / (2 * rho) :=
    (div_le_div_iff_of_pos_right (mul_pos htwoPos hrho)).2 hmultiplierSq
  rw [augmentedLagrangian_def]
  have hobjective := h.objectiveLower_le x hx
  linarith

/-- Helper for Corollary 4.2: a segment in the regularity region gives the
quadratic upper Taylor estimate for the objective. -/
private lemma objectiveChange_le
    (h : EqualityConstrained.Regularity f c)
    (x y : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x y ⊆ h.region) :
    f y - f x ≤
      ⟪gradient f x, y - x⟫_ℝ +
        (h.gradientLipschitz : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  -- Bound the signed Taylor remainder by its norm and use segmentwise smoothness.
  have hremainder := LALM.norm_sub_sub_fderiv_le f h.gradientLipschitz h.region x y
    (fun _ hz ↦ h.differentiableAt_objective hz) h.lipschitzOn_objectiveFDeriv hsegment
  have hsigned :
      f y - f x - fderiv ℝ f x (y - x) ≤
        ‖f y - f x - fderiv ℝ f x (y - x)‖ := by
    simpa only [Real.norm_eq_abs] using
      (le_abs_self (f y - f x - fderiv ℝ f x (y - x)))
  rw [← inner_gradient_left] at hremainder hsigned
  linarith

/-- Helper for Corollary 4.2: the two corrected admissible segments bound the
objective change by the corrected objective part of the model constant. -/
lemma objectiveChangeAlongCorrectedStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p)
    (hstep : ‖p‖ ≤ params.delta) :
    f (nextPoint c x p) - f x ≤
      ⟪gradient f x, p⟫_ℝ +
        (h.gradientBound * stepConstant h +
          (h.gradientLipschitz / 2) * displacementFactor h params.delta ^ 2) *
            ‖p‖ ^ 2 := by
  -- Apply Taylor's estimate separately to the base and correction segments.
  have hbase := objectiveChange_le h x (trialPoint x p) hadm.1
  rw [trialPoint_def, add_sub_cancel_left] at hbase
  have hcorrection := objectiveChange_le h
    (trialPoint x p) (nextPoint c x p) hadm.2
  rw [nextPoint_def, add_sub_cancel_left] at hcorrection
  have htrial := trialPoint_mem_region h x p hadm
  have hgradient := h.norm_gradient_le (trialPoint x p) htrial
  have hcorrectionNorm := norm_step_le h x p hadm
  have hinnerCorrection :
      ⟪gradient f (trialPoint x p), step c x p⟫_ℝ ≤
        h.gradientBound * stepConstant h * ‖p‖ ^ 2 := by
    calc
      ⟪gradient f (trialPoint x p), step c x p⟫_ℝ ≤
          ‖gradient f (trialPoint x p)‖ * ‖step c x p‖ :=
        real_inner_le_norm _ _
      _ ≤ h.gradientBound * (stepConstant h * ‖p‖ ^ 2) :=
        mul_le_mul hgradient hcorrectionNorm (norm_nonneg _)
          (NNReal.coe_nonneg _)
      _ = h.gradientBound * stepConstant h * ‖p‖ ^ 2 := by ring
  -- Both quadratic Taylor remainders fit under the corrected displacement factor.
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  have hcorrectionBoundNonneg : 0 ≤ stepConstant h * ‖p‖ ^ 2 :=
    mul_nonneg hstepConstantNonneg (sq_nonneg _)
  have hcorrectionSq :
      ‖step c x p‖ ^ 2 ≤ (stepConstant h * ‖p‖ ^ 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hcorrectionBoundNonneg).2 hcorrectionNorm
  have hstepSq : ‖p‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrectionSqScaled :
      ‖step c x p‖ ^ 2 ≤
        stepConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := by
    calc
      ‖step c x p‖ ^ 2 ≤ (stepConstant h * ‖p‖ ^ 2) ^ 2 := hcorrectionSq
      _ = stepConstant h ^ 2 * ‖p‖ ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ stepConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := by
        gcongr
      _ = stepConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := rfl
  have hfactorComparison :
      1 + stepConstant h ^ 2 * (params.delta : ℝ) ^ 2 ≤
        displacementFactor h params.delta ^ 2 := by
    rw [displacementFactor_def]
    nlinarith [mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta)]
  have hremainderNorm :
      ‖p‖ ^ 2 + ‖step c x p‖ ^ 2 ≤
        displacementFactor h params.delta ^ 2 * ‖p‖ ^ 2 := by
    calc
      ‖p‖ ^ 2 + ‖step c x p‖ ^ 2 ≤
          ‖p‖ ^ 2 + stepConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 :=
        add_le_add (le_refl _) hcorrectionSqScaled
      _ = (1 + stepConstant h ^ 2 * params.delta ^ 2) * ‖p‖ ^ 2 := by ring
      _ ≤ displacementFactor h params.delta ^ 2 * ‖p‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfactorComparison (sq_nonneg _)
  have hremainder :
      (h.gradientLipschitz / 2) * (‖p‖ ^ 2 + ‖step c x p‖ ^ 2) ≤
        (h.gradientLipschitz / 2) * displacementFactor h params.delta ^ 2 *
          ‖p‖ ^ 2 := by
    calc
      (h.gradientLipschitz / 2) * (‖p‖ ^ 2 + ‖step c x p‖ ^ 2) ≤
          (h.gradientLipschitz / 2) *
            (displacementFactor h params.delta ^ 2 * ‖p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hremainderNorm (by positivity)
      _ = (h.gradientLipschitz / 2) * displacementFactor h params.delta ^ 2 *
          ‖p‖ ^ 2 := by ring
  -- Normalize the corrected endpoint and collect the two segment estimates.
  rw [trialPoint_def] at hcorrection hinnerCorrection
  rw [nextPoint_def, trialPoint_def]
  nlinarith

/-- Helper for Corollary 4.2: the objective change across both corrected
admissible legs is bounded by the corrected displacement factor. -/
lemma normObjectiveChangeAlongCorrectedStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x p : EuclideanSpace ℝ (Fin n))
    (hadm : IsAdmissible h x p) (hstep : ‖p‖ ≤ params.delta) :
    ‖f (nextPoint c x p) - f x‖ ≤
      h.gradientBound * displacementFactor h params.delta * ‖p‖ := by
  -- Apply the mean-value estimate separately on the base and correction legs.
  have hbaseObjective :
      ‖f (trialPoint x p) - f x‖ ≤ h.gradientBound * ‖p‖ := by
    have hmean :
        ‖f (trialPoint x p) - f x‖ ≤
          h.gradientBound * ‖trialPoint x p - x‖ := by
      apply (convex_segment x (trialPoint x p)).norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ)
      · intro u hu
        exact h.differentiableAt_objective (hadm.1 hu)
      · intro u hu
        simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
          h.norm_gradient_le u (hadm.1 hu)
      · exact left_mem_segment ℝ x (trialPoint x p)
      · exact right_mem_segment ℝ x (trialPoint x p)
    simpa only [trialPoint_def, add_sub_cancel_left] using hmean
  have hcorrectionObjective :
      ‖f (nextPoint c x p) - f (trialPoint x p)‖ ≤
        h.gradientBound * ‖step c x p‖ := by
    have hmean :
        ‖f (nextPoint c x p) - f (trialPoint x p)‖ ≤
          h.gradientBound * ‖nextPoint c x p - trialPoint x p‖ := by
      apply (convex_segment (trialPoint x p) (nextPoint c x p)).norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ)
      · intro u hu
        exact h.differentiableAt_objective (hadm.2 hu)
      · intro u hu
        simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
          h.norm_gradient_le u (hadm.2 hu)
      · exact left_mem_segment ℝ (trialPoint x p) (nextPoint c x p)
      · exact right_mem_segment ℝ (trialPoint x p) (nextPoint c x p)
    simpa only [nextPoint_def, add_sub_cancel_left] using hmean
  -- Use the base-step radius to turn the quadratic correction into a linear term.
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  have hcorrectionLinear :
      ‖step c x p‖ ≤ stepConstant h * params.delta * ‖p‖ := by
    calc
      ‖step c x p‖ ≤ stepConstant h * ‖p‖ ^ 2 := norm_step_le h x p hadm
      _ = (stepConstant h * ‖p‖) * ‖p‖ := by ring
      _ ≤ (stepConstant h * params.delta) * ‖p‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep hstepConstantNonneg) (norm_nonneg _)
  have hdecomposition :
      f (nextPoint c x p) - f x =
        (f (nextPoint c x p) - f (trialPoint x p)) +
          (f (trialPoint x p) - f x) := by
    ring
  rw [hdecomposition]
  calc
    ‖(f (nextPoint c x p) - f (trialPoint x p)) +
        (f (trialPoint x p) - f x)‖ ≤
        ‖f (nextPoint c x p) - f (trialPoint x p)‖ +
          ‖f (trialPoint x p) - f x‖ := norm_add_le _ _
    _ ≤ h.gradientBound * ‖step c x p‖ + h.gradientBound * ‖p‖ :=
      add_le_add hcorrectionObjective hbaseObjective
    _ ≤ h.gradientBound * (stepConstant h * params.delta * ‖p‖) +
        h.gradientBound * ‖p‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcorrectionLinear (NNReal.coe_nonneg _))
        (le_refl _)
    _ = h.gradientBound * displacementFactor h params.delta * ‖p‖ := by
      rw [displacementFactor_def]
      ring

/-- Helper for Corollary 4.2: the corrected constraint remainder is controlled
by the constraint part of the corrected model constant. -/
lemma constraintRemainderAlongCorrectedStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (lambda : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p)
    (hstep : ‖p‖ ≤ params.delta)
    (heffective :
      ‖lambda + (params.rho : ℝ) • c x‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ⟪lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p), error c x p⟫_ℝ +
        (params.rho / 2) * ‖error c x p‖ ^ 2 ≤
      (errorFactor h params.delta *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) +
        (params.rho / 2) * errorFactor h params.delta ^ 2 * params.delta ^ 2) *
          ‖p‖ ^ 2 := by
  -- Bound the linearized constraint increment at the admissible base point.
  have hx := base_mem_region h x p hadm
  have hderivativeNorm : ‖fderiv ℝ c x‖ ≤ h.constraintGradientBound := by
    rw [← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    exact h.norm_constraintGradient_le x hx
  have hlinearizedStep :
      ‖fderiv ℝ c x p‖ ≤ h.constraintGradientBound * ‖p‖ := by
    calc
      ‖fderiv ℝ c x p‖ ≤ ‖fderiv ℝ c x‖ * ‖p‖ :=
        (fderiv ℝ c x).le_opNorm p
      _ ≤ h.constraintGradientBound * ‖p‖ :=
        mul_le_mul_of_nonneg_right hderivativeNorm (norm_nonneg _)
  have heffectiveLinearized :
      ‖lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p)‖ ≤
        3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
    have hdecomposition :
        lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p) =
          (lambda + (params.rho : ℝ) • c x) +
            (params.rho : ℝ) • fderiv ℝ c x p := by
      module
    rw [hdecomposition]
    calc
      ‖(lambda + (params.rho : ℝ) • c x) +
          (params.rho : ℝ) • fderiv ℝ c x p‖ ≤
          ‖lambda + (params.rho : ℝ) • c x‖ +
            ‖(params.rho : ℝ) • fderiv ℝ c x p‖ := norm_add_le _ _
      _ ≤ 3 * params.multiplierBound +
          params.rho * (h.constraintGradientBound * ‖p‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1]
        exact add_le_add heffective
          (mul_le_mul_of_nonneg_left hlinearizedStep params.spec.1.2.2.1.le)
      _ ≤ 3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
        have hcoefficient :
            (0 : ℝ) ≤ params.rho * h.constraintGradientBound := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hstep hcoefficient]
  -- The public corrected-error estimate supplies the quadratic remainder scale.
  have herror := norm_error_le_factor h params.delta x p hadm hstep
  have hlinearizedBoundNonneg :
      (0 : ℝ) ≤ 3 * params.multiplierBound +
        params.rho * h.constraintGradientBound * params.delta :=
    (norm_nonneg _).trans heffectiveLinearized
  have hinnerContribution :
      ⟪lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p), error c x p⟫_ℝ ≤
        errorFactor h params.delta *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) * ‖p‖ ^ 2 := by
    calc
      ⟪lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p), error c x p⟫_ℝ ≤
          ‖lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p)‖ *
            ‖error c x p‖ := real_inner_le_norm _ _
      _ ≤ (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
          (errorFactor h params.delta * ‖p‖ ^ 2) :=
        mul_le_mul heffectiveLinearized herror (norm_nonneg _)
          hlinearizedBoundNonneg
      _ = errorFactor h params.delta *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) * ‖p‖ ^ 2 := by
        ring
  -- Square the corrected error only after recording a nonnegative upper bound.
  have herrorFactorNonneg : 0 ≤ errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  have hstepSq : ‖p‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herrorBoundNonneg : 0 ≤ errorFactor h params.delta * ‖p‖ ^ 2 :=
    mul_nonneg herrorFactorNonneg (sq_nonneg _)
  have herrorSq :
      ‖error c x p‖ ^ 2 ≤
        errorFactor h params.delta ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := by
    have hsquaredError :
        ‖error c x p‖ ^ 2 ≤
          (errorFactor h params.delta * ‖p‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herrorBoundNonneg).2 herror
    calc
      ‖error c x p‖ ^ 2 ≤
          (errorFactor h params.delta * ‖p‖ ^ 2) ^ 2 := hsquaredError
      _ = errorFactor h params.delta ^ 2 * ‖p‖ ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ errorFactor h params.delta ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := by
        gcongr
      _ = errorFactor h params.delta ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := rfl
  have hpenaltyContribution :
      (params.rho / 2) * ‖error c x p‖ ^ 2 ≤
        (params.rho / 2) * errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖p‖ ^ 2 := by
    calc
      (params.rho / 2) * ‖error c x p‖ ^ 2 ≤
          (params.rho / 2) *
            (errorFactor h params.delta ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herrorSq (by positivity)
      _ = (params.rho / 2) * errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖p‖ ^ 2 := by ring
  -- Add the pairing and squared-error contributions in model-constant normal form.
  nlinarith

/-- Helper for Corollary 4.2: the corrected endpoint constraint is its base
linearization plus the corrected nonlinear error. -/
private lemma constraintValue_nextPoint_eq_linearization_add_error
    (x p : EuclideanSpace ℝ (Fin n)) :
    c (nextPoint c x p) = c x + fderiv ℝ c x p + error c x p := by
  -- Rearrange the public corrected-error definition at the canonical endpoint.
  rw [error_def]
  module

/-- Helper for Corollary 4.2: one corrected augmented-Lagrangian difference
splits into its linearized core and corrected constraint remainder. -/
private lemma augmentedLagrangianChangeAlongCorrectedStep_eq
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (lambda : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    ℒ[f, c; params.rho](nextPoint c x p, lambda) -
        ℒ[f, c; params.rho](x, lambda) =
      (f (nextPoint c x p) - f x) + ⟪lambda, fderiv ℝ c x p⟫_ℝ +
        (params.rho / 2) *
          (‖c x + fderiv ℝ c x p‖ ^ 2 - ‖c x‖ ^ 2) +
        ⟪lambda + (params.rho : ℝ) • (c x + fderiv ℝ c x p), error c x p⟫_ℝ +
        (params.rho / 2) * ‖error c x p‖ ^ 2 := by
  -- Substitute the corrected error interface and expand the resulting norm square.
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    constraintValue_nextPoint_eq_linearization_add_error (c := c) x p,
    norm_add_sq_real]
  simp only [inner_add_right, inner_add_left, inner_smul_left,
    starRingEnd_apply, star_trivial]
  ring

/-- Helper for Corollary 4.2: corrected transition geometry bounds the true
augmented-Lagrangian change by its linearized core and corrected model constant. -/
lemma augmentedLagrangianChangeAlongCorrectedStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (lambda : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) (hadm : IsAdmissible h x p)
    (hstep : ‖p‖ ≤ params.delta)
    (heffective :
      ‖lambda + (params.rho : ℝ) • c x‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](nextPoint c x p, lambda) -
        ℒ[f, c; params.rho](x, lambda) ≤
      (⟪gradient f x, p⟫_ℝ + ⟪lambda, fderiv ℝ c x p⟫_ℝ +
        (params.rho / 2) *
          (‖c x + fderiv ℝ c x p‖ ^ 2 - ‖c x‖ ^ 2)) +
        modelConstant h params.delta params.rho params.multiplierBound * ‖p‖ ^ 2 := by
  have hobjective := objectiveChangeAlongCorrectedStep_le h params x p hadm hstep
  have hconstraint :=
    constraintRemainderAlongCorrectedStep_le h params x lambda p hadm hstep heffective
  -- Expand the exact difference and collect the two corrected remainder bounds.
  rw [augmentedLagrangianChangeAlongCorrectedStep_eq params x lambda p,
    modelConstant_def]
  nlinarith

end LALM.Correction

end
