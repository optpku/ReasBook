/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalPath
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedCanonicalPath

public section

open MeasureTheory
open scoped BigOperators InnerProductSpace LALM NNReal

namespace LALM.FiniteStopped

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Theorem 3.7: one bounded base transition controls KKT
stationarity at its endpoint by the current step and estimator error. -/
theorem normBaseStationarityNext_le_of_transitionBounds
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (g p : EuclideanSpace ℝ (Fin n))
    (hminimizes : IsMinOn
      (LALM.stepModelWithGradient c g params.rho params.beta x multiplier)
        Set.univ p)
    (hsegment : segment ℝ x (x + p) ⊆ h.region)
    (hstep : ‖p‖ ≤ params.delta)
    (hmultiplier :
      ‖baseNextMultiplier c params.rho x multiplier p‖ ≤
        params.multiplierBound) :
    ‖KKT.stationarity f c (x + p)
        (baseNextMultiplier c params.rho x multiplier p)‖ ≤
      LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖p‖ +
        ‖g - gradient f x‖ := by
  have hx : x ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hxNext : x + p ∈ h.region := hsegment (right_mem_segment ℝ _ _)
  have herror := normScaledBaseConstraintGradientError_le h params x p hsegment hstep
  have hnormal := basePerturbedMultiplierIdentity_of_minimizes c g params.rho
    params.beta x multiplier p hminimizes
  have hstationarityIdentity :
      KKT.stationarity f c (x + p)
          (baseNextMultiplier c params.rho x multiplier p) =
        ((-(params.beta : ℝ) • p +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
              (baseLinearizationError c x p)) +
          (gradient f (x + p) - gradient f x) +
          (EqualityConstrained.constraintGradient c (x + p) -
            EqualityConstrained.constraintGradient c x)
              (baseNextMultiplier c params.rho x multiplier p)) -
            (g - gradient f x) := by
    rw [KKT.stationarity_def]
    simp only [sub_apply]
    linear_combination (norm := module) hnormal
  have hpointDistance : dist (x + p) x = ‖p‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (x + p) - gradient f x‖ ≤
        h.gradientLipschitz * ‖p‖ := by
    calc
      ‖gradient f (x + p) - gradient f x‖ =
          dist (gradient f (x + p)) (gradient f x) := (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz * dist (x + p) x :=
        h.lipschitzOn_gradient.dist_le_mul (x + p) hxNext x hx
      _ = h.gradientLipschitz * ‖p‖ := by rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x‖ ≤
        h.constraintGradientLipschitz * ‖p‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x‖ =
          dist (EqualityConstrained.constraintGradient c (x + p))
            (EqualityConstrained.constraintGradient c x) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz * dist (x + p) x :=
        h.lipschitzOn_constraintGradient.dist_le_mul (x + p) hxNext x hx
      _ = h.constraintGradientLipschitz * ‖p‖ := by rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x)
            (baseNextMultiplier c params.rho x multiplier p)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound * ‖p‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x)
            (baseNextMultiplier c params.rho x multiplier p)‖ ≤
          ‖EqualityConstrained.constraintGradient c (x + p) -
            EqualityConstrained.constraintGradient c x‖ *
              ‖baseNextMultiplier c params.rho x multiplier p‖ :=
        (EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x).le_opNorm _
      _ ≤ (h.constraintGradientLipschitz * ‖p‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound * ‖p‖ := by
        ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hproximalError :
      ‖-(params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho * ‖p‖ := by
    calc
      ‖-(params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)‖ ≤
          ‖-(params.beta : ℝ) • p‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
              (baseLinearizationError c x p)‖ := norm_add_le _ _
      _ = params.beta * ‖p‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hbeta]
      _ ≤ params.beta * ‖p‖ +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖p‖ := add_le_add_right herror _
      _ = LALM.primalConstant h params.delta params.beta params.rho * ‖p‖ := by
        rw [LALM.primalConstant_def]
        ring
  have hdeterministic :
      ‖(-(params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)) +
        (gradient f (x + p) - gradient f x) +
        (EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x)
            (baseNextMultiplier c params.rho x multiplier p)‖ ≤
      LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖p‖ := by
    calc
      ‖(-(params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)) +
        (gradient f (x + p) - gradient f x) +
        (EqualityConstrained.constraintGradient c (x + p) -
          EqualityConstrained.constraintGradient c x)
            (baseNextMultiplier c params.rho x multiplier p)‖ ≤
          ‖-(params.beta : ℝ) • p +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
              (baseLinearizationError c x p)‖ +
          ‖gradient f (x + p) - gradient f x‖ +
          ‖(EqualityConstrained.constraintGradient c (x + p) -
            EqualityConstrained.constraintGradient c x)
              (baseNextMultiplier c params.rho x multiplier p)‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • p +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
              (baseLinearizationError c x p))
          (gradient f (x + p) - gradient f x)
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • p +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
                (baseLinearizationError c x p)) +
            (gradient f (x + p) - gradient f x))
          ((EqualityConstrained.constraintGradient c (x + p) -
            EqualityConstrained.constraintGradient c x)
              (baseNextMultiplier c params.rho x multiplier p))
        linarith
      _ ≤ LALM.primalConstant h params.delta params.beta params.rho * ‖p‖ +
          h.gradientLipschitz * ‖p‖ +
          h.constraintGradientLipschitz * params.multiplierBound * ‖p‖ :=
        add_le_add (add_le_add hproximalError hgradientDifference) hoperatorApplied
      _ = LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖p‖ := by
        rw [LALM.primalComparisonConstant_def]
        ring
  rw [hstationarityIdentity]
  exact (norm_sub_le _ _).trans (add_le_add hdeterministic (le_refl _))

/-- Helper for Theorem 3.7: the base multiplier update identifies squared
constraint feasibility with the penalty-scaled multiplier increment. -/
theorem baseConstraintNormSq_eq_multiplierIncrementNormSqDiv
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    ‖c (x + p)‖ ^ 2 =
      ‖baseNextMultiplier c params.rho x multiplier p - multiplier‖ ^ 2 /
        (params.rho : ℝ) ^ 2 := by
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [baseNextMultiplier_def, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hrho]
  field_simp [hrho.ne']

/-- Theorem 3.7: adjacent bounded base transitions control the squared KKT
residual by the two step energies and the two estimator-error energies. -/
theorem baseKKTResidualSquare_le_of_adjacentTransitions
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (previousPoint currentPoint : EuclideanSpace ℝ (Fin n))
    (previousMultiplier currentMultiplier : EuclideanSpace ℝ (Fin m))
    (previousGradient currentGradient previousStep currentStep :
      EuclideanSpace ℝ (Fin n))
    (hpreviousMinimizes : IsMinOn
      (LALM.stepModelWithGradient c previousGradient params.rho params.beta
        previousPoint previousMultiplier) Set.univ previousStep)
    (hcurrentMinimizes : IsMinOn
      (LALM.stepModelWithGradient c currentGradient params.rho params.beta
        currentPoint currentMultiplier) Set.univ currentStep)
    (hpoint : currentPoint = previousPoint + previousStep)
    (hmultiplier : currentMultiplier =
      baseNextMultiplier c params.rho previousPoint previousMultiplier previousStep)
    (hsegmentPrevious : segment ℝ previousPoint
      (previousPoint + previousStep) ⊆ h.region)
    (hsegmentCurrent : segment ℝ currentPoint
      (currentPoint + currentStep) ⊆ h.region)
    (hstepPrevious : ‖previousStep‖ ≤ params.delta)
    (hstepCurrent : ‖currentStep‖ ≤ params.delta)
    (hmultiplierCurrent : ‖currentMultiplier‖ ≤ params.multiplierBound)
    (hmultiplierNext :
      ‖baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep‖ ≤
        params.multiplierBound) :
    KKT.residual f c (currentPoint + currentStep)
        (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep) ^ 2 ≤
      LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2 +
          ‖currentGradient - gradient f currentPoint‖ ^ 2 +
          ‖previousGradient - gradient f previousPoint‖ ^ 2) := by
  have hxCurrent : currentPoint ∈ h.region :=
    hsegmentCurrent (left_mem_segment ℝ _ _)
  have hstationarity := normBaseStationarityNext_le_of_transitionBounds
    h params currentPoint currentMultiplier currentGradient currentStep
      hcurrentMinimizes hsegmentCurrent hstepCurrent hmultiplierNext
  have hcomparisonNonneg :
      0 ≤ LALM.primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.primalComparisonConstant_def, LALM.primalConstant_def]
    positivity
  have hstationarityRightNonneg :
      0 ≤ LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖currentStep‖ +
        ‖currentGradient - gradient f currentPoint‖ :=
    add_nonneg (mul_nonneg hcomparisonNonneg (norm_nonneg _)) (norm_nonneg _)
  have hstationaritySquared :
      ‖KKT.stationarity f c (currentPoint + currentStep)
          (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep)‖ ^ 2 ≤
        (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖currentStep‖ +
          ‖currentGradient - gradient f currentPoint‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hstationarityRightNonneg).2 hstationarity
  have hstationaritySquare :
      ‖KKT.stationarity f c (currentPoint + currentStep)
          (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep)‖ ^ 2 ≤
        2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 * ‖currentStep‖ ^ 2 +
          2 * ‖currentGradient - gradient f currentPoint‖ ^ 2 := by
    calc
      _ ≤ (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖currentStep‖ +
          ‖currentGradient - gradient f currentPoint‖) ^ 2 := hstationaritySquared
      _ ≤ 2 * (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖currentStep‖) ^ 2 +
          2 * ‖currentGradient - gradient f currentPoint‖ ^ 2 := by
        nlinarith [sq_nonneg
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖currentStep‖ -
            ‖currentGradient - gradient f currentPoint‖)]
      _ = 2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 * ‖currentStep‖ ^ 2 +
          2 * ‖currentGradient - gradient f currentPoint‖ ^ 2 := by ring
  have hconstraintGradient :=
    normBaseConstraintGradientMultiplierIncrement_le_of_adjacentTransitions
      (f := f) (c := c) h params previousPoint currentPoint
      previousMultiplier currentMultiplier previousGradient currentGradient
      previousStep currentStep hpreviousMinimizes hcurrentMinimizes hpoint hmultiplier
      hsegmentPrevious hsegmentCurrent hstepPrevious hstepCurrent hmultiplierCurrent
  have hmultiplierIncrement :=
    normBaseMultiplierIncrementSquare_le_of_constraintGradientBound
      h params currentPoint
      (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep -
        currentMultiplier)
      currentStep previousStep
      (currentGradient - gradient f currentPoint)
      (previousGradient - gradient f previousPoint)
      hxCurrent hconstraintGradient
  have hfeasibility :
      ‖c (currentPoint + currentStep)‖ ^ 2 ≤
        LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 *
          (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
        LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
          (‖currentGradient - gradient f currentPoint‖ ^ 2 +
            ‖previousGradient - gradient f previousPoint‖ ^ 2) := by
    calc
      ‖c (currentPoint + currentStep)‖ ^ 2 =
          ‖baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep -
            currentMultiplier‖ ^ 2 / (params.rho : ℝ) ^ 2 :=
        baseConstraintNormSq_eq_multiplierIncrementNormSqDiv params
          currentPoint currentMultiplier currentStep
      _ ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound * (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
            LALM.multiplierErrorConstant h *
              (‖currentGradient - gradient f currentPoint‖ ^ 2 +
                ‖previousGradient - gradient f previousPoint‖ ^ 2)) /
              (params.rho : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmultiplierIncrement (sq_nonneg _)
      _ = LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 *
          (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
        LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
          (‖currentGradient - gradient f currentPoint‖ ^ 2 +
            ‖previousGradient - gradient f previousPoint‖ ^ 2) := by ring
  have hprimalCoefficient :
      2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 +
          LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 ≤
        LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound := by
    rw [LALM.stochasticResidualConstant_def]
    exact le_max_left _ _
  have herrorCoefficient :
      2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 ≤
        LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound := by
    rw [LALM.stochasticResidualConstant_def]
    exact le_max_right _ _
  have hstepSumNonneg :
      0 ≤ ‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have herrorSumNonneg :
      0 ≤ ‖currentGradient - gradient f currentPoint‖ ^ 2 +
        ‖previousGradient - gradient f previousPoint‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hstationarityExpanded :
      ‖KKT.stationarity f c (currentPoint + currentStep)
          (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep)‖ ^ 2 ≤
        2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 *
          (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
        2 * (‖currentGradient - gradient f currentPoint‖ ^ 2 +
          ‖previousGradient - gradient f previousPoint‖ ^ 2) := by
    calc
      _ ≤ 2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 * ‖currentStep‖ ^ 2 +
          2 * ‖currentGradient - gradient f currentPoint‖ ^ 2 := hstationaritySquare
      _ ≤ _ := by
        have htwo : (0 : ℝ) ≤ 2 := by norm_num
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _))
            (mul_nonneg htwo (sq_nonneg _)))
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) htwo)
  calc
    KKT.residual f c (currentPoint + currentStep)
        (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep) ^ 2 =
        ‖KKT.stationarity f c (currentPoint + currentStep)
            (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep)‖ ^ 2 +
          ‖c (currentPoint + currentStep)‖ ^ 2 := by
      rw [KKT.residual_def,
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ (2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 +
            LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2) *
          (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
        (2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
          (‖currentGradient - gradient f currentPoint‖ ^ 2 +
            ‖previousGradient - gradient f previousPoint‖ ^ 2) := by
      calc
        _ ≤ (2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2 *
              (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
            2 * (‖currentGradient - gradient f currentPoint‖ ^ 2 +
              ‖previousGradient - gradient f previousPoint‖ ^ 2)) +
            (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2 *
              (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
            LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
              (‖currentGradient - gradient f currentPoint‖ ^ 2 +
                ‖previousGradient - gradient f previousPoint‖ ^ 2)) :=
          add_le_add hstationarityExpanded hfeasibility
        _ = _ := by ring
    _ ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
      LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentGradient - gradient f currentPoint‖ ^ 2 +
          ‖previousGradient - gradient f previousPoint‖ ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hprimalCoefficient hstepSumNonneg)
        (mul_le_mul_of_nonneg_right herrorCoefficient herrorSumNonneg)
    _ = LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2 +
          ‖currentGradient - gradient f currentPoint‖ ^ 2 +
          ‖previousGradient - gradient f previousPoint‖ ^ 2) := by ring

end LALM.FiniteStopped

namespace LALM.FiniteStopped.StoppedAttemptAnalysis

open LALM.FiniteStopped

universe u' v'

variable {n' m' : ℕ}
variable {Ξ' : Type u'} [MeasurableSpace Ξ'] {ν' : Measure Ξ'}
  [IsProbabilityMeasure ν']
variable {Ω' : Type v'} [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']
variable {f' : EuclideanSpace ℝ (Fin n') → ℝ}
variable {c' : EuclideanSpace ℝ (Fin n') → EuclideanSpace ℝ (Fin m')}
variable {x₀' : EuclideanSpace ℝ (Fin n')}
variable {multiplier₀' : EuclideanSpace ℝ (Fin m')}
variable {h' : EqualityConstrained.Regularity f' c'}
variable {oracle' : EqualityConstrained.StochasticOracle f' h'.region ν'}
variable {params' : LALM.Parameters h' x₀' multiplier₀'}
variable {Q' B' b' : ℕ+} {confidence' : ℝ} {K' : ℕ}
variable {X' : Set (EuclideanSpace ℝ (Fin n'))}

/-- Theorem 3.7: the canonical finite stopped prefix satisfies the stochastic
KKT residual estimate at every interior adjacent pair of transitions. -/
theorem canonicalFiniteStoppedResidualSquare_le_of_prefixInvariant
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω') {k : ℕ}
    (hkPos : 1 ≤ k)
    (hkPrefix : k < canonicalPrefixLength attempt omega) :
    KKT.residual f' c' (attempt.point
        (⟨k + 1, by
          have hprefixLe := canonicalPrefixLength_le attempt omega
          omega⟩ : Fin (K' + 1)) omega)
        (attempt.multiplier
          (⟨k + 1, by
            have hprefixLe := canonicalPrefixLength_le attempt omega
            omega⟩ : Fin (K' + 1)) omega) ^ 2 ≤
      LALM.stochasticResidualConstant h' params'.delta params'.beta params'.rho
          params'.multiplierBound *
        (activeBaseStepIntegrand attempt k omega +
          activeBaseStepIntegrand attempt (k - 1) omega +
          activeGradientErrorIntegrand attempt k omega +
          activeGradientErrorIntegrand attempt (k - 1) omega) := by
  have hprefixLe : canonicalPrefixLength attempt omega ≤ K' :=
    canonicalPrefixLength_le attempt omega
  have hK : 1 ≤ K' := by omega
  let previous : Fin K' := ⟨k - 1, by omega⟩
  let current : Fin K' := ⟨k, by omega⟩
  have hpreviousPrefix : previous.1 < canonicalPrefixLength attempt omega := by
    dsimp only [previous]
    omega
  have hcurrentPrefix : current.1 < canonicalPrefixLength attempt omega := by
    dsimp only [current]
    exact hkPrefix
  have hactivePrevious : attempt.activeAt previous.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega previous.1 previous.isLt).2
      hpreviousPrefix
  have hactiveCurrent : attempt.activeAt current.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega current.1 current.isLt).2
      hcurrentPrefix
  have hprevSucc : previous.succ = current.castSucc := by
    apply Fin.ext
    change (k - 1) + 1 = k
    omega
  have hpointPreviousSucc :
      attempt.point previous.succ omega =
        attempt.point previous.castSucc omega + attempt.baseStep previous omega := by
    unfold StoppedAttempt.baseStep
    calc
      attempt.point previous.succ omega =
          (attempt.point previous.succ omega - attempt.point previous.castSucc omega) +
            attempt.point previous.castSucc omega :=
        (sub_add_cancel (attempt.point previous.succ omega)
          (attempt.point previous.castSucc omega)).symm
      _ = attempt.point previous.castSucc omega +
          (attempt.point previous.succ omega - attempt.point previous.castSucc omega) :=
        add_comm _ _
  have hpoint :
      attempt.point current.castSucc omega =
        attempt.point previous.castSucc omega + attempt.baseStep previous omega := by
    rw [← hprevSucc]
    exact hpointPreviousSucc
  have hpointCurrentSucc :
      attempt.point current.succ omega =
        attempt.point current.castSucc omega + attempt.baseStep current omega := by
    unfold StoppedAttempt.baseStep
    module
  have hpreviousStep : ‖attempt.baseStep previous omega‖ ≤ params'.delta :=
    invariant.step_bound omega previous hpreviousPrefix
  have hcurrentStep : ‖attempt.baseStep current omega‖ ≤ params'.delta :=
    invariant.step_bound omega current hcurrentPrefix
  have hpreviousMultiplier :
      ‖attempt.multiplier previous.castSucc omega‖ ≤ params'.multiplierBound := by
    apply invariant.multiplier_bound omega previous.castSucc
    change k - 1 ≤ canonicalPrefixLength attempt omega
    omega
  have hcurrentMultiplier :
      ‖attempt.multiplier current.castSucc omega‖ ≤ params'.multiplierBound := by
    apply invariant.multiplier_bound omega current.castSucc
    change k ≤ canonicalPrefixLength attempt omega
    omega
  have hmultiplierPreviousUpdate :=
    multiplier_succ_eq_actual_of_prefix_invariant attempt invariant omega previous
      hpreviousPrefix
  have hmultiplierUpdate :
      attempt.multiplier current.castSucc omega =
        baseNextMultiplier c' params'.rho
          (attempt.point previous.castSucc omega)
          (attempt.multiplier previous.castSucc omega)
          (attempt.baseStep previous omega) := by
    rw [baseNextMultiplier_def, ← hpointPreviousSucc, ← hprevSucc]
    exact hmultiplierPreviousUpdate
  have hpreviousPointMem : attempt.point previous.castSucc omega ∈ X' :=
    point_mem_of_active attempt previous.castSucc omega hactivePrevious
  have hcurrentPointMem : attempt.point current.castSucc omega ∈ X' :=
    point_mem_of_active attempt current.castSucc omega hactiveCurrent
  have hsegmentPrevious := segment_subset_region_of_mem_X_of_step_bound attempt
    (attempt.point previous.castSucc omega) (attempt.baseStep previous omega)
    hpreviousPointMem hpreviousStep
  have hsegmentCurrent := segment_subset_region_of_mem_X_of_step_bound attempt
    (attempt.point current.castSucc omega) (attempt.baseStep current omega)
    hcurrentPointMem hcurrentStep
  have hpreviousMinimizes :=
    activeBaseStep_minimizes_model_of_active attempt previous omega hactivePrevious
  have hcurrentMinimizes :=
    activeBaseStep_minimizes_model_of_active attempt current omega hactiveCurrent
  have hnextMultiplierCurrentActual :
      attempt.multiplier current.succ omega =
        baseNextMultiplier c' params'.rho
          (attempt.point current.castSucc omega)
          (attempt.multiplier current.castSucc omega)
          (attempt.baseStep current omega) := by
    rw [baseNextMultiplier_def, ← hpointCurrentSucc]
    exact multiplier_succ_eq_actual_of_prefix_invariant attempt invariant omega
      current hcurrentPrefix
  have hmultiplierNext :
      ‖baseNextMultiplier c' params'.rho
          (attempt.point current.castSucc omega)
          (attempt.multiplier current.castSucc omega)
          (attempt.baseStep current omega)‖ ≤ params'.multiplierBound := by
    rw [← hnextMultiplierCurrentActual]
    apply invariant.multiplier_bound omega current.succ
    change k + 1 ≤ canonicalPrefixLength attempt omega
    omega
  have hresidual :=
    baseKKTResidualSquare_le_of_adjacentTransitions
      (f := f') (c := c') h' params'
      (attempt.point previous.castSucc omega)
      (attempt.point current.castSucc omega)
      (attempt.multiplier previous.castSucc omega)
      (attempt.multiplier current.castSucc omega)
      (clippedEstimateAt h' oracle' Q' B' b' previous.1
        (attempt.state previous.castSucc omega, attempt.batch previous.1 omega))
      (clippedEstimateAt h' oracle' Q' B' b' current.1
        (attempt.state current.castSucc omega, attempt.batch current.1 omega))
      (attempt.baseStep previous omega) (attempt.baseStep current omega)
      hpreviousMinimizes hcurrentMinimizes hpoint hmultiplierUpdate
      hsegmentPrevious hsegmentCurrent hpreviousStep hcurrentStep
      hcurrentMultiplier hmultiplierNext
  have hcurrentStepEnergy :=
    activeBaseStepIntegrand_eq_stepSquare_of_active attempt current omega
      hactiveCurrent
  have hpreviousStepEnergy :=
    activeBaseStepIntegrand_eq_stepSquare_of_active attempt previous omega
      hactivePrevious
  have hcurrentErrorEnergy :=
    activeGradientErrorIntegrand_eq_gradientErrorSquare_of_active attempt current
      omega hactiveCurrent
  have hpreviousErrorEnergy :=
    activeGradientErrorIntegrand_eq_gradientErrorSquare_of_active attempt previous
      omega hactivePrevious
  have hpreviousIndex : previous.1 + 1 = k := by
    dsimp only [previous]
    omega
  have hcurrentEndpointIndex :
      current.succ =
        (⟨k + 1, by
          have hprefixLe := canonicalPrefixLength_le attempt omega
          omega⟩ : Fin (K' + 1)) := by
    apply Fin.ext
    rfl
  calc
    KKT.residual f' c' (attempt.point
        (⟨k + 1, by
          have hprefixLe := canonicalPrefixLength_le attempt omega
          omega⟩ : Fin (K' + 1)) omega)
        (attempt.multiplier
          (⟨k + 1, by
            have hprefixLe := canonicalPrefixLength_le attempt omega
            omega⟩ : Fin (K' + 1)) omega) ^ 2 =
        KKT.residual f' c'
          (attempt.point current.castSucc omega + attempt.baseStep current omega)
          (baseNextMultiplier c' params'.rho
            (attempt.point current.castSucc omega)
            (attempt.multiplier current.castSucc omega)
            (attempt.baseStep current omega)) ^ 2 := by
      rw [← hcurrentEndpointIndex, hpointCurrentSucc, hnextMultiplierCurrentActual]
    _ ≤ LALM.stochasticResidualConstant h' params'.delta params'.beta params'.rho
          params'.multiplierBound *
        (‖attempt.baseStep current omega‖ ^ 2 +
          ‖attempt.baseStep previous omega‖ ^ 2 +
          ‖clippedEstimateAt h' oracle' Q' B' b' current.1
              (attempt.state current.castSucc omega, attempt.batch current.1 omega) -
            gradient f' (attempt.point current.castSucc omega)‖ ^ 2 +
          ‖clippedEstimateAt h' oracle' Q' B' b' previous.1
              (attempt.state previous.castSucc omega, attempt.batch previous.1 omega) -
            gradient f' (attempt.point previous.castSucc omega)‖ ^ 2) := hresidual
    _ = LALM.stochasticResidualConstant h' params'.delta params'.beta params'.rho
          params'.multiplierBound *
        (activeBaseStepIntegrand attempt k omega +
          activeBaseStepIntegrand attempt (k - 1) omega +
          activeGradientErrorIntegrand attempt k omega +
          activeGradientErrorIntegrand attempt (k - 1) omega) := by
      rw [← hcurrentStepEnergy, ← hpreviousStepEnergy,
        ← hcurrentErrorEnergy, ← hpreviousErrorEnergy]

/-- Theorem 3.7: the same stopped residual estimate in the natural-index
adapter used by the article's `R_{k+1}` notation. -/
theorem canonicalFiniteStoppedResidualSquare_le_of_prefixInvariant_nat
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω') {k : ℕ}
    (hkPos : 1 ≤ k)
    (hkPrefix : k < canonicalPrefixLength attempt omega) :
    KKT.residual f' c' (canonicalPointNat attempt (k + 1) omega)
        (canonicalMultiplierNat attempt (k + 1) omega) ^ 2 ≤
      LALM.stochasticResidualConstant h' params'.delta params'.beta params'.rho
          params'.multiplierBound *
        (activeBaseStepIntegrand attempt k omega +
          activeBaseStepIntegrand attempt (k - 1) omega +
          activeGradientErrorIntegrand attempt k omega +
          activeGradientErrorIntegrand attempt (k - 1) omega) := by
  have hprefixLe : canonicalPrefixLength attempt omega ≤ K' :=
    canonicalPrefixLength_le attempt omega
  have hkK : k ≤ K' := by omega
  have hendpointK : k + 1 ≤ K' := by omega
  have hfinite := canonicalFiniteStoppedResidualSquare_le_of_prefixInvariant
    (f' := f') (c' := c') attempt invariant omega hkPos hkPrefix
  rw [canonicalPointNat_eq_point attempt (k + 1) hendpointK omega,
    canonicalMultiplierNat_eq_multiplier attempt (k + 1) hendpointK omega]
  exact hfinite

/-- Helper for Theorem 3.7: adjacent nonnegative energies over a finite
prefix are bounded by twice the corresponding full-range energy. -/
theorem sumAdjacent_nonneg_le_two_range
    (a : ℕ → ℝ) (K : ℕ) (hK : 2 ≤ K)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ Finset.Ico 1 K, (a k + a (k - 1))) ≤
      2 * ∑ k ∈ Finset.range K, a k := by
  have hshift :
      (∑ k ∈ Finset.Ico 1 K, a (k - 1)) =
        ∑ j ∈ Finset.range (K - 1), a j := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    omega
  have hsubset : Finset.range (K - 1) ⊆ Finset.range K := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hrange :
      (∑ j ∈ Finset.range (K - 1), a j) ≤
        ∑ j ∈ Finset.range K, a j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j hjLong _hjShort ↦ ha j)
  have hsplit :
      (∑ j ∈ Finset.range K, a j) =
        a 0 + ∑ k ∈ Finset.Ico 1 K, a k := by
    have hKpos : 1 ≤ K := by omega
    rw [Finset.sum_range_eq_add_Ico a hKpos]
  rw [Finset.sum_add_distrib, hshift, hsplit]
  linarith [ha 0, hrange]

/-- Helper for Theorem 3.7: every active canonical endpoint remains in the
regularity region, including a retained first-exit endpoint. -/
theorem canonicalPointNat_succ_mem_region_of_prefixInvariant
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω') {k : ℕ}
    (hkPrefix : k < canonicalPrefixLength attempt omega) :
    canonicalPointNat attempt (k + 1) omega ∈ h'.region := by
  have hprefixLe : canonicalPrefixLength attempt omega ≤ K' :=
    canonicalPrefixLength_le attempt omega
  have hkK : k < K' := by omega
  let kFin : Fin K' := ⟨k, hkK⟩
  have hactive : attempt.activeAt kFin.castSucc omega :=
    (activeAt_iff_lt_canonicalPrefixLength attempt omega k kFin.isLt).2 hkPrefix
  have hstep : ‖attempt.baseStep kFin omega‖ ≤ params'.delta :=
    invariant.step_bound omega kFin hkPrefix
  have hsegment := segment_subset_region_of_mem_X_of_step_bound attempt
    (attempt.point kFin.castSucc omega) (attempt.baseStep kFin omega)
    (point_mem_of_active attempt kFin.castSucc omega hactive) hstep
  have hendpoint : attempt.point kFin.succ omega ∈ h'.region := by
    have hpoint :
        attempt.point kFin.succ omega =
          attempt.point kFin.castSucc omega + attempt.baseStep kFin omega := by
      unfold StoppedAttempt.baseStep
      module
    rw [hpoint]
    exact hsegment (right_mem_segment ℝ _ _)
  rw [canonicalPointNat_eq_point attempt (k + 1) (by omega) omega]
  have hindex :
      (⟨k + 1, by omega⟩ : Fin (K' + 1)) = kFin.succ := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact hendpoint

/-- Theorem 3.7: the canonical stopped pathwise residual energy counts only
active transitions and is controlled by the total step and estimator energies. -/
noncomputable def canonicalPathwiseResidualEnergy
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (omega : Ω') : ℝ :=
    ∑ k ∈ Finset.Ico 1 K',
    if _hk : k < canonicalPrefixLength attempt omega then
      KKT.residualExtension h'
          (canonicalPointNat attempt (k + 1) omega,
            canonicalMultiplierNat attempt (k + 1) omega) ^ 2
    else 0

/-- Helper for Theorem 3.7: each natural-index canonical point observable is
measurable, with the finite stopped point used inside the horizon and zero
padding beyond it. -/
theorem measurable_canonicalPointNat
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X') (k : ℕ) :
    Measurable (canonicalPointNat attempt k) := by
  by_cases hk : k ≤ K'
  · have heq : canonicalPointNat attempt k =
        attempt.point ⟨k, Nat.lt_succ_iff.mpr hk⟩ := by
      funext omega
      exact canonicalPointNat_eq_point attempt k hk omega
    rw [heq]
    exact measurable_point attempt ⟨k, Nat.lt_succ_iff.mpr hk⟩
  · have heq : canonicalPointNat attempt k =
        fun _ : Ω' ↦ (0 : EuclideanSpace ℝ (Fin n')) := by
      funext omega
      simp only [canonicalPointNat, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Theorem 3.7: each natural-index canonical multiplier observable
is measurable, with zero padding beyond the finite stopped horizon. -/
theorem measurable_canonicalMultiplierNat
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X') (k : ℕ) :
    Measurable (canonicalMultiplierNat attempt k) := by
  by_cases hk : k ≤ K'
  · have heq : canonicalMultiplierNat attempt k =
        attempt.multiplier ⟨k, Nat.lt_succ_iff.mpr hk⟩ := by
      funext omega
      exact canonicalMultiplierNat_eq_multiplier attempt k hk omega
    rw [heq]
    unfold StoppedAttempt.multiplier
    exact measurable_fst.comp
      (measurable_snd.comp
        (measurable_snd.comp
          (measurable_snd.comp
            (attempt.measurable_state ⟨k, Nat.lt_succ_iff.mpr hk⟩))))
  · have heq : canonicalMultiplierNat attempt k =
        fun _ : Ω' ↦ (0 : EuclideanSpace ℝ (Fin m')) := by
      funext omega
      simp only [canonicalMultiplierNat, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Theorem 3.7: the globally extended squared canonical residual
at one natural index is measurable. -/
theorem measurable_canonicalResidualSquare
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X') (k : ℕ) :
    Measurable (fun omega ↦
      KKT.residualExtension h'
        (canonicalPointNat attempt k omega, canonicalMultiplierNat attempt k omega) ^ 2) := by
  exact (KKT.measurable_residualExtension h').comp
    ((measurable_canonicalPointNat attempt k).prodMk
      (measurable_canonicalMultiplierNat attempt k)) |>.pow_const 2

/-- Helper for Theorem 3.7: the stopped canonical residual energy is
measurable as a finite sum of active residual sections. -/
theorem measurable_canonicalPathwiseResidualEnergy
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X') :
    Measurable (canonicalPathwiseResidualEnergy attempt) := by
  unfold canonicalPathwiseResidualEnergy
  apply Finset.measurable_sum
  intro k hk
  have hkK : k < K' := (Finset.mem_Ico.mp hk).2
  let kFin : Fin (K' + 1) := ⟨k, Nat.lt_succ_of_lt hkK⟩
  have hevent : MeasurableSet {omega : Ω' |
      k < canonicalPrefixLength attempt omega} := by
    have hactive : MeasurableSet {omega : Ω' | attempt.activeAt kFin omega} :=
      attempt.measurableSet_activeAt kFin
    have heq : {omega : Ω' | k < canonicalPrefixLength attempt omega} =
        {omega : Ω' | attempt.activeAt kFin omega} := by
      ext omega
      simpa only [Set.mem_setOf_eq, kFin] using
        (activeAt_iff_lt_canonicalPrefixLength attempt omega k hkK).symm
    rw [heq]
    exact hactive
  have hres := measurable_canonicalResidualSquare attempt (k + 1)
  exact Measurable.ite hevent hres measurable_const

/-- Helper for Theorem 3.7: the globally extended squared residual is
nonnegative at every pair. -/
theorem canonicalResidualExtension_square_nonneg
    (h : EqualityConstrained.Regularity f' c')
    (z : EuclideanSpace ℝ (Fin n') × EuclideanSpace ℝ (Fin m')) :
    0 ≤ KKT.residualExtension h z ^ 2 :=
  sq_nonneg _

/-- Helper for Theorem 3.7: the canonical stopped residual energy is
nonnegative pathwise. -/
theorem canonicalPathwiseResidualEnergy_nonneg
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X') (omega : Ω') :
    0 ≤ canonicalPathwiseResidualEnergy attempt omega := by
  unfold canonicalPathwiseResidualEnergy
  exact Finset.sum_nonneg fun k hk ↦ by
    split
    · exact canonicalResidualExtension_square_nonneg h'
        (canonicalPointNat attempt (k + 1) omega,
          canonicalMultiplierNat attempt (k + 1) omega)
    · exact le_rfl

/-- Helper for Theorem 3.7: positive algorithm parameters make the stochastic
residual comparison constant nonnegative. -/
theorem stochasticResidualConstant_nonneg_of_parameters
    (h : EqualityConstrained.Regularity f' c')
    (params : LALM.Parameters h x₀' multiplier₀') :
    0 ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
      params.multiplierBound := by
  rw [LALM.stochasticResidualConstant_def]
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hsecond :
      0 ≤ 2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 := by
    positivity
  exact hsecond.trans (le_max_right _ _)

/-- Theorem 3.7: the canonical stopped pathwise residual energy is bounded by
the stochastic residual constant times twice the total finite energies. -/
theorem canonicalPathwiseResidualEnergy_le_of_prefixInvariant
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 2 ≤ K') (omega : Ω') :
    canonicalPathwiseResidualEnergy attempt omega ≤
      2 * LALM.stochasticResidualConstant h' params'.delta params'.beta params'.rho
          params'.multiplierBound *
        (pathwiseBaseStepEnergy attempt omega +
          pathwiseGradientErrorEnergy attempt omega) := by
  let C : ℝ := LALM.stochasticResidualConstant h' params'.delta params'.beta
    params'.rho params'.multiplierBound
  have hC : 0 ≤ C := by
    exact stochasticResidualConstant_nonneg_of_parameters h' params'
  let a : ℕ → ℝ := fun k ↦
    activeBaseStepIntegrand attempt k omega +
      activeGradientErrorIntegrand attempt k omega
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp only [a]
    exact add_nonneg
      (activeBaseStepIntegrand_nonneg attempt k omega)
      (activeGradientErrorIntegrand_nonneg attempt k omega)
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico 1 K') :
      (if hp : k < canonicalPrefixLength attempt omega then
          KKT.residualExtension h'
              (canonicalPointNat attempt (k + 1) omega,
                canonicalMultiplierNat attempt (k + 1) omega) ^ 2
        else 0) ≤ C * (a k + a (k - 1)) := by
    have hkPos : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    by_cases hp : k < canonicalPrefixLength attempt omega
    · rw [dif_pos hp]
      have hregion := canonicalPointNat_succ_mem_region_of_prefixInvariant
        (f' := f') (c' := c') attempt invariant omega hp
      have hext :
          KKT.residualExtension h'
              (canonicalPointNat attempt (k + 1) omega,
                canonicalMultiplierNat attempt (k + 1) omega) =
            KKT.residual f' c' (canonicalPointNat attempt (k + 1) omega)
              (canonicalMultiplierNat attempt (k + 1) omega) := by
        exact KKT.residualExtension_eq h' hregion
      rw [hext]
      have hres := canonicalFiniteStoppedResidualSquare_le_of_prefixInvariant_nat
        (f' := f') (c' := c') attempt invariant omega hkPos hp
      dsimp only [C, a]
      calc
        KKT.residual f' c' (canonicalPointNat attempt (k + 1) omega)
              (canonicalMultiplierNat attempt (k + 1) omega) ^ 2 ≤
            C * (activeBaseStepIntegrand attempt k omega +
              activeBaseStepIntegrand attempt (k - 1) omega +
              activeGradientErrorIntegrand attempt k omega +
              activeGradientErrorIntegrand attempt (k - 1) omega) := hres
        _ = C * (a k + a (k - 1)) := by ring
    · rw [dif_neg hp]
      exact mul_nonneg hC (add_nonneg (ha k) (ha (k - 1)))
  have hadjacent := sumAdjacent_nonneg_le_two_range a K' hK ha
  unfold canonicalPathwiseResidualEnergy
  calc
    (∑ k ∈ Finset.Ico 1 K',
        if hk : k < canonicalPrefixLength attempt omega then
          KKT.residualExtension h'
              (canonicalPointNat attempt (k + 1) omega,
                canonicalMultiplierNat attempt (k + 1) omega) ^ 2
        else 0) ≤
      ∑ k ∈ Finset.Ico 1 K', C * (a k + a (k - 1)) := by
        exact Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ = C * ∑ k ∈ Finset.Ico 1 K', (a k + a (k - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ C * (2 * ∑ k ∈ Finset.range K', a k) :=
      mul_le_mul_of_nonneg_left hadjacent hC
    _ = 2 * LALM.stochasticResidualConstant h' params'.delta params'.beta
          params'.rho params'.multiplierBound *
        (pathwiseBaseStepEnergy attempt omega +
          pathwiseGradientErrorEnergy attempt omega) := by
      dsimp only [C, a, pathwiseBaseStepEnergy, pathwiseGradientErrorEnergy]
      rw [Finset.sum_add_distrib]
      ring

/-- Theorem 3.7: the canonical stopped residual energy is integrable under the
finite prefix invariant. -/
theorem integrable_canonicalPathwiseResidualEnergy_of_prefixInvariant
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 2 ≤ K') :
    Integrable (canonicalPathwiseResidualEnergy attempt) P' := by
  let C : ℝ := LALM.stochasticResidualConstant h' params'.delta params'.beta
    params'.rho params'.multiplierBound
  have hbase := integrable_pathwiseBaseStepEnergy attempt invariant
  have herr := integrable_pathwiseGradientErrorEnergy attempt
  have hsum : Integrable (fun omega ↦
      pathwiseBaseStepEnergy attempt omega +
        pathwiseGradientErrorEnergy attempt omega) P' := hbase.add herr
  have hmajorant : Integrable (fun omega ↦
      2 * C * (pathwiseBaseStepEnergy attempt omega +
        pathwiseGradientErrorEnergy attempt omega)) P' := by
    simpa only [Pi.add_apply] using hsum.const_mul (2 * C)
  refine Integrable.mono' hmajorant
    (measurable_canonicalPathwiseResidualEnergy attempt).aestronglyMeasurable
    (ae_of_all P' fun omega ↦ ?_)
  have hbound := canonicalPathwiseResidualEnergy_le_of_prefixInvariant
    (f' := f') (c' := c') attempt invariant hK omega
  have hnonneg := canonicalPathwiseResidualEnergy_nonneg
    (f' := f') (c' := c') attempt omega
  simpa only [Real.norm_of_nonneg hnonneg, C] using hbound

/-- Theorem 3.7: integrating the canonical stopped residual energy gives the
stopped aggregate residual numerator in terms of the two finite energies. -/
theorem integral_canonicalPathwiseResidualEnergy_le_of_prefixInvariant
    (attempt : StoppedAttempt h' oracle' P' x₀' multiplier₀' params' Q' B' b'
      confidence' K' X')
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (hK : 2 ≤ K') :
    (∫ omega, canonicalPathwiseResidualEnergy attempt omega ∂P') ≤
      2 * LALM.stochasticResidualConstant h' params'.delta params'.beta params'.rho
          params'.multiplierBound *
        (stoppedBaseStepEnergy attempt + stoppedGradientErrorEnergy attempt) := by
  let C : ℝ := LALM.stochasticResidualConstant h' params'.delta params'.beta
    params'.rho params'.multiplierBound
  have hresidual := integrable_canonicalPathwiseResidualEnergy_of_prefixInvariant
    (f' := f') (c' := c') attempt invariant hK
  have hbase := integrable_pathwiseBaseStepEnergy attempt invariant
  have herr := integrable_pathwiseGradientErrorEnergy attempt
  have hmajorant : Integrable (fun omega ↦
      2 * C * (pathwiseBaseStepEnergy attempt omega +
        pathwiseGradientErrorEnergy attempt omega)) P' := by
    simpa only [Pi.add_apply] using (hbase.add herr).const_mul (2 * C)
  have hpoint := canonicalPathwiseResidualEnergy_le_of_prefixInvariant
    (f' := f') (c' := c') attempt invariant hK
  calc
    (∫ omega, canonicalPathwiseResidualEnergy attempt omega ∂P') ≤
        ∫ omega, 2 * C * (pathwiseBaseStepEnergy attempt omega +
          pathwiseGradientErrorEnergy attempt omega) ∂P' :=
      integral_mono hresidual hmajorant hpoint
    _ = 2 * C *
        ((∫ omega, pathwiseBaseStepEnergy attempt omega ∂P') +
          ∫ omega, pathwiseGradientErrorEnergy attempt omega ∂P') := by
      rw [integral_const_mul, integral_add hbase herr]
    _ = 2 * LALM.stochasticResidualConstant h' params'.delta params'.beta
          params'.rho params'.multiplierBound *
        (stoppedBaseStepEnergy attempt + stoppedGradientErrorEnergy attempt) := by
      rw [integral_pathwiseBaseStepEnergy attempt invariant,
        integral_pathwiseGradientErrorEnergy attempt]

/-- Theorem 3.7: the canonical finite stopped residual numerator is bounded
by the article's stochastic complexity constant once the schedule coupling is
closed. -/
theorem finiteStoppedCanonicalResidualNumerator_le
    (attempt : SPIDER.StoppedScheduledAttempt h' oracle' P' x₀' multiplier₀'
      params' confidence' K' X')
    (hK : 2 ≤ K')
    (path : FiniteStoppedPath attempt)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (hbudget : path.baseStepBudget =
      LALM.StochasticRun.initialStepBound h' params')
    (hcoefficient : path.errorStepCoefficient =
      LALM.StochasticRun.errorStepConstant h' params') :
    (∫ omega, canonicalPathwiseResidualEnergy attempt omega ∂P') ≤
      LALM.StochasticRun.complexityConstant h' oracle' params' := by
  have hresidual := integral_canonicalPathwiseResidualEnergy_le_of_prefixInvariant
    (f' := f') (c' := c') attempt path.invariant hK
  have henergy := finiteStoppedScheduledEnergyBounds attempt hK path recursion
    hbudget hcoefficient
  have hC : 0 ≤ LALM.stochasticResidualConstant h' params'.delta params'.beta
      params'.rho params'.multiplierBound :=
    stochasticResidualConstant_nonneg_of_parameters h' params'
  calc
    (∫ omega, canonicalPathwiseResidualEnergy attempt omega ∂P') ≤
        2 * LALM.stochasticResidualConstant h' params'.delta params'.beta
            params'.rho params'.multiplierBound *
          (stoppedBaseStepEnergy attempt + stoppedGradientErrorEnergy attempt) := hresidual
    _ ≤ 2 * LALM.stochasticResidualConstant h' params'.delta params'.beta
          params'.rho params'.multiplierBound *
        (LALM.StochasticRun.stepAverageConstant h' oracle' params' +
          LALM.StochasticRun.errorAverageConstant h' oracle' params') := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add henergy.2 henergy.1
      · exact (mul_nonneg (by norm_num) hC)
    _ = LALM.StochasticRun.complexityConstant h' oracle' params' := by
      rw [LALM.StochasticRun.complexityConstant_def]

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
