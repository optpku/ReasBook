/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.DeterministicMultiplier

public section

open scoped InnerProductSpace LALM NNReal

namespace LALM.Correction.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

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
private lemma objectiveChangeAlongCorrectedStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hadm : IsAdmissible h (run.point k) (run.baseStep k))
    (hstep : ‖run.baseStep k‖ ≤ params.delta) :
    f (run.point (k + 1)) - f (run.point k) ≤
      ⟪gradient f (run.point k), run.baseStep k⟫_ℝ +
        (h.gradientBound * stepConstant h +
          (h.gradientLipschitz / 2) * displacementFactor h params.delta ^ 2) *
            ‖run.baseStep k‖ ^ 2 := by
  -- Apply Taylor's estimate separately to the base and correction segments.
  have hbase := objectiveChange_le h (run.point k)
    (trialPoint (run.point k) (run.baseStep k)) hadm.1
  rw [trialPoint_def, add_sub_cancel_left] at hbase
  have hcorrection := objectiveChange_le h
    (trialPoint (run.point k) (run.baseStep k))
    (nextPoint c (run.point k) (run.baseStep k)) hadm.2
  rw [nextPoint_def, trialPoint_def, add_sub_cancel_left] at hcorrection
  have htrial := trialPoint_mem_region h (run.point k) (run.baseStep k) hadm
  have hgradient := h.norm_gradient_le
    (trialPoint (run.point k) (run.baseStep k)) htrial
  have hcorrectionNorm := norm_step_le h (run.point k) (run.baseStep k) hadm
  have hinnerCorrection :
      ⟪gradient f (trialPoint (run.point k) (run.baseStep k)),
          step c (run.point k) (run.baseStep k)⟫_ℝ ≤
        h.gradientBound * stepConstant h * ‖run.baseStep k‖ ^ 2 := by
    calc
      ⟪gradient f (trialPoint (run.point k) (run.baseStep k)),
          step c (run.point k) (run.baseStep k)⟫_ℝ ≤
          ‖gradient f (trialPoint (run.point k) (run.baseStep k))‖ *
            ‖step c (run.point k) (run.baseStep k)‖ := real_inner_le_norm _ _
      _ ≤ h.gradientBound *
          (stepConstant h * ‖run.baseStep k‖ ^ 2) :=
        mul_le_mul hgradient hcorrectionNorm (norm_nonneg _)
          (NNReal.coe_nonneg _)
      _ = h.gradientBound * stepConstant h * ‖run.baseStep k‖ ^ 2 := by ring
  rw [trialPoint_def] at hinnerCorrection
  -- Both quadratic Taylor remainders fit under the corrected displacement factor.
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  have hcorrectionBoundNonneg :
      0 ≤ stepConstant h * ‖run.baseStep k‖ ^ 2 :=
    mul_nonneg hstepConstantNonneg (sq_nonneg _)
  have hcorrectionSq :
      ‖step c (run.point k) (run.baseStep k)‖ ^ 2 ≤
        (stepConstant h * ‖run.baseStep k‖ ^ 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hcorrectionBoundNonneg).2 hcorrectionNorm
  have hstepSq : ‖run.baseStep k‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrectionSqScaled :
      ‖step c (run.point k) (run.baseStep k)‖ ^ 2 ≤
        stepConstant h ^ 2 * params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 := by
    calc
      ‖step c (run.point k) (run.baseStep k)‖ ^ 2 ≤
          (stepConstant h * ‖run.baseStep k‖ ^ 2) ^ 2 := hcorrectionSq
      _ = stepConstant h ^ 2 * ‖run.baseStep k‖ ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by ring
      _ ≤ stepConstant h ^ 2 * params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 := by
        gcongr
      _ = stepConstant h ^ 2 * params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 := rfl
  have hfactorComparison :
      1 + stepConstant h ^ 2 * (params.delta : ℝ) ^ 2 ≤
        displacementFactor h params.delta ^ 2 := by
    rw [displacementFactor_def]
    nlinarith [mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta)]
  have hremainderNorm :
      ‖run.baseStep k‖ ^ 2 + ‖step c (run.point k) (run.baseStep k)‖ ^ 2 ≤
        displacementFactor h params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 := by
    calc
      ‖run.baseStep k‖ ^ 2 +
          ‖step c (run.point k) (run.baseStep k)‖ ^ 2 ≤
          ‖run.baseStep k‖ ^ 2 +
            stepConstant h ^ 2 * params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 :=
        add_le_add_right hcorrectionSqScaled _
      _ = (1 + stepConstant h ^ 2 * params.delta ^ 2) *
          ‖run.baseStep k‖ ^ 2 := by ring
      _ ≤ displacementFactor h params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hfactorComparison (sq_nonneg _)
  have hremainder :
      (h.gradientLipschitz / 2) *
          (‖run.baseStep k‖ ^ 2 +
            ‖step c (run.point k) (run.baseStep k)‖ ^ 2) ≤
        (h.gradientLipschitz / 2) * displacementFactor h params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by
    calc
      (h.gradientLipschitz / 2) *
          (‖run.baseStep k‖ ^ 2 +
            ‖step c (run.point k) (run.baseStep k)‖ ^ 2) ≤
          (h.gradientLipschitz / 2) *
            (displacementFactor h params.delta ^ 2 * ‖run.baseStep k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hremainderNorm (by positivity)
      _ = (h.gradientLipschitz / 2) * displacementFactor h params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by ring
  -- Add both segment estimates and replace the corrected endpoint by the run successor.
  rw [run.point_succ, nextPoint_def, trialPoint_def]
  nlinarith

/-- Helper for Corollary 4.2: model optimality gives the exact change of the
linearized augmented-Lagrangian terms for the corrected base step. -/
private lemma linearizedAugmentedLagrangianChange_eq
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) :
    ⟪gradient f (run.point k), run.baseStep k⟫_ℝ +
          ⟪run.multiplier k, fderiv ℝ c (run.point k) (run.baseStep k)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)‖ ^ 2 -
            ‖c (run.point k)‖ ^ 2) =
      -params.beta * ‖run.baseStep k‖ ^ 2 -
        (params.rho / 2) *
          ‖fderiv ℝ c (run.point k) (run.baseStep k)‖ ^ 2 := by
  -- Pair the damped normal equation with the stored base step.
  have hoptimal := congrArg (fun v ↦ ⟪v, run.baseStep k⟫_ℝ)
    (run.baseStepOptimality k)
  simp only [inner_add_left, inner_sub_left, inner_neg_left, inner_smul_left,
    starRingEnd_apply, star_trivial, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq] at hoptimal
  rw [norm_add_sq_real]
  nlinarith

/-- Helper for Corollary 4.2: the corrected constraint value is its base
linearization plus the corrected nonlinear error. -/
private lemma constraintValue_eq_linearization_add_error
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) :
    c (run.point (k + 1)) =
      c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k) +
        error c (run.point k) (run.baseStep k) := by
  -- Substitute the corrected point update and rearrange the error definition.
  rw [run.point_succ, error_def]
  module

/-- Helper for Corollary 4.2: one corrected augmented-Lagrangian difference
splits into its linearized core, objective remainder, and corrected error terms. -/
private lemma augmentedLagrangianChange_eq_linearized
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) -
        ℒ[f, c; params.rho](run.point k, run.multiplier k) =
      (f (run.point (k + 1)) - f (run.point k)) +
        ⟪run.multiplier k, fderiv ℝ c (run.point k) (run.baseStep k)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)‖ ^ 2 -
            ‖c (run.point k)‖ ^ 2) +
        ⟪run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)),
          error c (run.point k) (run.baseStep k)⟫_ℝ +
        (params.rho / 2) * ‖error c (run.point k) (run.baseStep k)‖ ^ 2 := by
  -- Substitute the corrected error interface and expand the resulting norm square.
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    constraintValue_eq_linearization_add_error h params run k, norm_add_sq_real]
  simp only [inner_add_right, inner_add_left, inner_smul_left,
    starRingEnd_apply, star_trivial]
  ring

/-- Helper for Corollary 4.2: the corrected constraint remainder contributes
at most the constraint part of the corrected model constant. -/
private lemma constraintRemainderContribution_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hadm : IsAdmissible h (run.point k) (run.baseStep k))
    (hstep : ‖run.baseStep k‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ⟪run.multiplier k + (params.rho : ℝ) •
          (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)),
        error c (run.point k) (run.baseStep k)⟫_ℝ +
        (params.rho / 2) * ‖error c (run.point k) (run.baseStep k)‖ ^ 2 ≤
      (errorFactor h params.delta *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) +
        (params.rho / 2) * errorFactor h params.delta ^ 2 * params.delta ^ 2) *
          ‖run.baseStep k‖ ^ 2 := by
  -- Bound the linearized constraint increment at the admissible base point.
  have hx := base_mem_region h (run.point k) (run.baseStep k) hadm
  have hderivativeNorm :
      ‖fderiv ℝ c (run.point k)‖ ≤ h.constraintGradientBound := by
    rw [← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    exact h.norm_constraintGradient_le (run.point k) hx
  have hlinearizedStep :
      ‖fderiv ℝ c (run.point k) (run.baseStep k)‖ ≤
        h.constraintGradientBound * ‖run.baseStep k‖ := by
    calc
      ‖fderiv ℝ c (run.point k) (run.baseStep k)‖ ≤
          ‖fderiv ℝ c (run.point k)‖ * ‖run.baseStep k‖ :=
        (fderiv ℝ c (run.point k)).le_opNorm (run.baseStep k)
      _ ≤ h.constraintGradientBound * ‖run.baseStep k‖ :=
        mul_le_mul_of_nonneg_right hderivativeNorm (norm_nonneg _)
  have heffectiveLinearized :
      ‖run.multiplier k + (params.rho : ℝ) •
          (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k))‖ ≤
        3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
    have hdecomposition :
        run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)) =
          (run.multiplier k + (params.rho : ℝ) • c (run.point k)) +
            (params.rho : ℝ) • fderiv ℝ c (run.point k) (run.baseStep k) := by
      module
    rw [hdecomposition]
    calc
      ‖(run.multiplier k + (params.rho : ℝ) • c (run.point k)) +
          (params.rho : ℝ) • fderiv ℝ c (run.point k) (run.baseStep k)‖ ≤
          ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ +
            ‖(params.rho : ℝ) • fderiv ℝ c (run.point k) (run.baseStep k)‖ :=
        norm_add_le _ _
      _ ≤ 3 * params.multiplierBound +
          params.rho * (h.constraintGradientBound * ‖run.baseStep k‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
        exact add_le_add heffective
          (mul_le_mul_of_nonneg_left hlinearizedStep run.rho_pos.le)
      _ ≤ 3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
        have hcoefficient :
            (0 : ℝ) ≤ params.rho * h.constraintGradientBound := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hstep hcoefficient]
  -- The corrected error estimate supplies the quadratic remainder scale.
  have herror := norm_error_le_factor h params.delta
    (run.point k) (run.baseStep k) hadm hstep
  have hlinearizedBoundNonneg :
      (0 : ℝ) ≤ 3 * params.multiplierBound +
        params.rho * h.constraintGradientBound * params.delta :=
    (norm_nonneg _).trans heffectiveLinearized
  have hinnerContribution :
      ⟪run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)),
          error c (run.point k) (run.baseStep k)⟫_ℝ ≤
        errorFactor h params.delta *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.baseStep k‖ ^ 2 := by
    calc
      ⟪run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)),
          error c (run.point k) (run.baseStep k)⟫_ℝ ≤
          ‖run.multiplier k + (params.rho : ℝ) •
            (c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k))‖ *
              ‖error c (run.point k) (run.baseStep k)‖ := real_inner_le_norm _ _
      _ ≤ (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
          (errorFactor h params.delta * ‖run.baseStep k‖ ^ 2) :=
        mul_le_mul heffectiveLinearized herror (norm_nonneg _) hlinearizedBoundNonneg
      _ = errorFactor h params.delta *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.baseStep k‖ ^ 2 := by ring
  -- Squaring the corrected error and using the step radius controls the penalty term.
  have herrorFactorNonneg : 0 ≤ errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  have hstepSq : ‖run.baseStep k‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herrorBoundNonneg :
      0 ≤ errorFactor h params.delta * ‖run.baseStep k‖ ^ 2 :=
    mul_nonneg herrorFactorNonneg (sq_nonneg _)
  have herrorSq :
      ‖error c (run.point k) (run.baseStep k)‖ ^ 2 ≤
        errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by
    have hsquaredError :
        ‖error c (run.point k) (run.baseStep k)‖ ^ 2 ≤
          (errorFactor h params.delta * ‖run.baseStep k‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herrorBoundNonneg).2 herror
    calc
      ‖error c (run.point k) (run.baseStep k)‖ ^ 2 ≤
          (errorFactor h params.delta * ‖run.baseStep k‖ ^ 2) ^ 2 := hsquaredError
      _ = errorFactor h params.delta ^ 2 * ‖run.baseStep k‖ ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by ring
      _ ≤ errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by
        gcongr
      _ = errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := rfl
  have hpenaltyContribution :
      (params.rho / 2) * ‖error c (run.point k) (run.baseStep k)‖ ^ 2 ≤
        (params.rho / 2) * errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by
    calc
      (params.rho / 2) * ‖error c (run.point k) (run.baseStep k)‖ ^ 2 ≤
          (params.rho / 2) *
            (errorFactor h params.delta ^ 2 * params.delta ^ 2 *
              ‖run.baseStep k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herrorSq (by positivity)
      _ = (params.rho / 2) * errorFactor h params.delta ^ 2 * params.delta ^ 2 *
          ‖run.baseStep k‖ ^ 2 := by ring
  -- Add the pairing and squared-error contributions in model-constant normal form.
  nlinarith

/-- Helper for Corollary 4.2: the true corrected augmented-Lagrangian change is
bounded by its base-model core plus the corrected model constant. -/
private lemma augmentedLagrangianChange_le_modelConstant
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hadm : IsAdmissible h (run.point k) (run.baseStep k))
    (hstep : ‖run.baseStep k‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k + (params.rho : ℝ) • c (run.point k)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) -
        ℒ[f, c; params.rho](run.point k, run.multiplier k) ≤
      (⟪gradient f (run.point k), run.baseStep k⟫_ℝ +
          ⟪run.multiplier k, fderiv ℝ c (run.point k) (run.baseStep k)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k) + fderiv ℝ c (run.point k) (run.baseStep k)‖ ^ 2 -
            ‖c (run.point k)‖ ^ 2)) +
        modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.baseStep k‖ ^ 2 := by
  have hobjective := objectiveChangeAlongCorrectedStep_le h params run k hadm hstep
  have hconstraint :=
    constraintRemainderContribution_le h params run k hadm hstep heffective
  -- Expand the exact difference and collect the two corrected remainder bounds.
  rw [augmentedLagrangianChange_eq_linearized h params run k, modelConstant_def]
  nlinarith

/-- Helper for Corollary 4.2: every transition in an admissible corrected prefix
decreases the fixed-multiplier augmented Lagrangian by a half-beta base-step term. -/
theorem augmentedLagrangianDescent
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N) (hk : k < N) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) ≤
      ℒ[f, c; params.rho](run.point k, run.multiplier k) -
        (params.beta / 2) * ‖run.baseStep k‖ ^ 2 := by
  -- Prefix bounds provide the corrected transition, base-step radius, and multipliers.
  have hadm := (run.isAdmissiblePrefix_iff h N).1 h_admissible k hk
  have hstep := run.norm_baseStep_le h params h_admissible hk
  have hMultiplier :
      ∀ j ≤ k, ‖run.multiplier j‖ ≤ params.multiplierBound := by
    intro j hj
    exact run.norm_multiplier_le h params h_admissible (hj.trans (Nat.le_of_lt hk))
  have heffective := run.norm_effectiveMultiplier_le h params k hMultiplier
  have hchange := augmentedLagrangianChange_le_modelConstant
    h params run k hadm hstep heffective
  rw [linearizedAugmentedLagrangianChange_eq h params run k] at hchange
  have hmodelTerm :
      modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.baseStep k‖ ^ 2 ≤
        (3 * (params.beta : ℝ) / 8) * ‖run.baseStep k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) *
        ‖fderiv ℝ c (run.point k) (run.baseStep k)‖ ^ 2 := by positivity
  have hproximalNonneg :
      (0 : ℝ) ≤ params.beta * ‖run.baseStep k‖ ^ 2 :=
    mul_nonneg run.beta_pos.le (sq_nonneg _)
  have hchangeFinal :
      ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) -
          ℒ[f, c; params.rho](run.point k, run.multiplier k) ≤
        -(params.beta / 2) * ‖run.baseStep k‖ ^ 2 := by
    nlinarith
  -- Move the old augmented-Lagrangian value back to the right-hand side.
  linarith

/-- Helper for Corollary 4.2: a corrected multiplier update increases the
augmented Lagrangian by its squared increment divided by the penalty. -/
private lemma augmentedLagrangian_multiplier_succ_eq
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier (k + 1)) =
      ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) +
        ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho := by
  -- Expand the multiplier term and replace the update by its corrected-point residual.
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    run.multiplier_succ_eq_add, inner_add_left, inner_smul_left,
    add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  field_simp [run.rho_pos.ne']
  ring

/-- Helper for Corollary 4.2: the admissible parameter inequality bounds the
multiplier-primal coefficient after division by the penalty. -/
private lemma multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  -- Clear the positive proximal and penalty denominators in the parameter inequality.
  have hscaled :
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Corollary 4.2: a bounded multiplier gives the uniform lower
bound for the augmented Lagrangian on the regularity region. -/
private lemma augmentedLagrangian_lowerBound_of_norm_multiplier_le
    (h : EqualityConstrained.Regularity f c) (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (B : ℝ)
    (hrho : 0 < rho) (hx : x ∈ h.region)
    (hmultiplier : ‖multiplier‖ ≤ B) (hB : 0 ≤ B) :
    h.objectiveLower - B ^ 2 / (2 * rho) ≤
      ℒ[f, c; rho](x, multiplier) := by
  -- Cauchy-Schwarz and Young's inequality complete the multiplier square.
  have hinner : -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have hyoungDivided := div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
    calc
      ‖multiplier‖ * ‖c x‖ = (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2) / 2 :=
        hyoungDivided
      _ = rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq : ‖multiplier‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg multiplier) hB).2 hmultiplier
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * rho) ≤ B ^ 2 / (2 * rho) :=
    (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hrho)).2 hmultiplierSq
  rw [augmentedLagrangian_def]
  have hobjective := h.objectiveLower_le x hx
  linarith

/-- Helper for Corollary 4.2: every positive-index corrected Lyapunov step
decreases by a quarter-beta base-step term. -/
theorem lyapunovDescent
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    run.lyapunov h params (k + 1) ≤
      run.lyapunov h params k -
        (params.beta / 4) * ‖run.baseStep k‖ ^ 2 := by
  -- Combine primal descent with the already-isolated multiplier-increment estimate.
  have hlagrangian := run.augmentedLagrangianDescent h params h_admissible hk
  have hmultiplier :=
    run.norm_multiplier_succ_sub_sq_le h params h_admissible hk_pos hk
  have hmultiplierDiv :
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    have hdivided := (div_le_div_iff_of_pos_right run.rho_pos).2 hmultiplier
    calc
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound *
              (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2)) /
                params.rho := hdivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
              (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by ring
  have hcoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have hcurrent :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep k‖ ^ 2 ≤
        (params.beta / 8) * ‖run.baseStep k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
  -- The preceding-step Lyapunov term cancels exactly after the multiplier update.
  rw [run.lyapunov_def, run.lyapunov_def,
    augmentedLagrangian_multiplier_succ_eq h params run, Nat.add_sub_cancel]
  nlinarith

/-- Helper for Corollary 4.2: every positive-index corrected Lyapunov value in
an admissible prefix is at least the uniform lower bound. -/
theorem lyapunovLowerBound_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    lyapunovLowerBound h params ≤ run.lyapunov h params k := by
  -- The corrected endpoint of the preceding admissible transition is `run.point k`.
  have hkPrevious : k - 1 < N := by omega
  have hadm := (run.isAdmissiblePrefix_iff h N).1 h_admissible
    (k - 1) hkPrevious
  have hx := nextPoint_mem_region h (run.point (k - 1))
    (run.baseStep (k - 1)) hadm
  rw [← run.point_succ (k - 1), Nat.sub_add_cancel hk_pos] at hx
  have hmultiplier := run.norm_multiplier_le h params h_admissible hk
  have hlower := augmentedLagrangian_lowerBound_of_norm_multiplier_le h params.rho
    (run.point k) (run.multiplier k) params.multiplierBound run.rho_pos hx
    hmultiplier (by positivity)
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep (k - 1)‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg run.rho_pos.le) (sq_nonneg _)
  -- Adding the nonnegative base-step correction preserves the augmented lower bound.
  rw [lyapunovLowerBound_def, run.lyapunov_def]
  linarith

end LALM.Correction.Run

end
