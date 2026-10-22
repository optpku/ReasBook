/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorActiveState
public import TR_LALM_theory.Corollary_4_2.StochasticEnergy
public import TR_LALM_theory.Corollary_4_2.StochasticMultiplier
public import TR_LALM_theory.Corollary_4_2.FixedPathEnergy
public import TR_LALM_theory.Theorem_2_10
import all TR_LALM_theory.Corollary_4_2.LocalizedEstimatorActiveState
import all TR_LALM_theory.Corollary_4_2.StochasticEnergy
import all TR_LALM_theory.Corollary_4_2.StochasticMultiplier

public section

open MeasureTheory
open scoped InnerProductSpace LALM NNReal

namespace LALM.Correction

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+} {confidence : ℝ}

/-- Helper for Corollary 4.2: the inverse-defined canonical base step is a
global minimizer of its explicit-gradient quadratic model. -/
theorem canonicalBaseStep_minimizesStepModelWithGradient
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    IsMinOn (LALM.stepModelWithGradient c g rho beta x multiplier) Set.univ
      (StochasticRun.canonicalBaseStep c rho beta x g multiplier) := by
  let linearObjective : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y ↦ inner ℝ g y
  have hlinearDerivative :
      HasFDerivAt linearObjective (innerSL ℝ g) x := by
    simpa only [linearObjective, coe_innerSL_apply] using
      (innerSL ℝ g).hasFDerivAt
  have hlinearGradient : HasGradientAt linearObjective g x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hlinearDerivative
  have hgradient : gradient linearObjective x = g := hlinearGradient.gradient
  have hmodels :
      stepModel linearObjective c rho beta x multiplier =
        stepModelWithGradient c g rho beta x multiplier := by
    funext q
    rw [stepModel_eq_stepModelWithGradient, hgradient]
  obtain ⟨p, hp, _⟩ := LALM.Run.existsUniqueStepModelMinimizer
    linearObjective c rho beta x multiplier hrho hbeta
  have hpExplicit :
      IsMinOn (stepModelWithGradient c g rho beta x multiplier) Set.univ p := by
    simpa only [← hmodels] using hp
  have hcanonical : StochasticRun.canonicalBaseStep c rho beta x g multiplier = p :=
    StochasticRun.canonicalBaseStep_eq_of_minimizes c rho beta x g multiplier p
      hrho hbeta hpExplicit
  simpa only [hcanonical] using hpExplicit

/-- Helper for Corollary 4.2: explicit model optimality and local transition
bounds give fixed-multiplier augmented-Lagrangian descent without a run. -/
theorem augmentedLagrangianDescent_of_transitionBounds
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (g p : EuclideanSpace ℝ (Fin n))
    (hminimizes : IsMinOn
      (LALM.stepModelWithGradient c g params.rho params.beta x multiplier)
        Set.univ p)
    (hadmissible : IsAdmissible h x p)
    (hstep : ‖p‖ ≤ params.delta)
    (heffective :
      ‖multiplier + (params.rho : ℝ) • c x‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](nextPoint c x p, multiplier) ≤
      ℒ[f, c; params.rho](x, multiplier) -
        (params.beta / 2) * ‖p‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
  have hchange := augmentedLagrangianChangeAlongCorrectedStep_le h params
    x multiplier p hadmissible hstep heffective
  have hlinearized :=
    linearizedAugmentedLagrangianChange_eq_of_minimizesStepModelWithGradient
      g params.rho params.beta x multiplier p hminimizes
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hquarterBeta : 0 < (params.beta : ℝ) / 4 := by
    positivity
  have hinverseQuarterBeta : ((params.beta : ℝ) / 4)⁻¹ = 4 / params.beta := by
    field_simp [hbeta.ne']
  have htwoProduct := two_mul_le_add_mul_sq
    (a := ‖p‖) (b := ‖g - gradient f x‖) hquarterBeta
  rw [hinverseQuarterBeta] at htwoProduct
  have htwoNonneg : (0 : ℝ) ≤ 2 := by
    norm_num
  have hyoung :
      ‖p‖ * ‖g - gradient f x‖ ≤
        (params.beta / 8) * ‖p‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
    calc
      ‖p‖ * ‖g - gradient f x‖ =
          (2 * ‖p‖ * ‖g - gradient f x‖) / 2 := by
        ring
      _ ≤ ((params.beta / 4) * ‖p‖ ^ 2 +
          (4 / params.beta) * ‖g - gradient f x‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right htwoProduct htwoNonneg
      _ = (params.beta / 8) * ‖p‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
        ring
  have hinnerNorm := real_inner_le_norm (-(g - gradient f x)) p
  simp only [inner_neg_left, norm_neg] at hinnerNorm
  have hinner :
      -⟪g - gradient f x, p⟫_ℝ ≤
        (params.beta / 8) * ‖p‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
    have hyoungCommuted :
        ‖g - gradient f x‖ * ‖p‖ ≤
          (params.beta / 8) * ‖p‖ ^ 2 +
            (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
      simpa only [mul_comm] using hyoung
    exact hinnerNorm.trans hyoungCommuted
  have hmodelTerm :
      modelConstant h params.delta params.rho params.multiplierBound * ‖p‖ ^ 2 ≤
        (3 * (params.beta : ℝ) / 8) * ‖p‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) * ‖fderiv ℝ c x p‖ ^ 2 := by
    positivity
  have hgradientIdentity : gradient f x = g - (g - gradient f x) := by
    module
  rw [hgradientIdentity, inner_sub_left] at hchange
  have hchangeFinal :
      ℒ[f, c; params.rho](nextPoint c x p, multiplier) -
          ℒ[f, c; params.rho](x, multiplier) ≤
        -(params.beta / 2) * ‖p‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
    nlinarith
  linarith

/-- Helper for Corollary 4.2: subtracting two adjacent explicit-gradient
optimality identities exposes the corrected multiplier increment. -/
theorem constraintGradientNextMultiplierSub_of_adjacentTransitions
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ)
    (previousPoint currentPoint previousGradient currentGradient
      previousStep currentStep : EuclideanSpace ℝ (Fin n))
    (previousMultiplier currentMultiplier : EuclideanSpace ℝ (Fin m))
    (hpreviousMinimizes : IsMinOn
      (LALM.stepModelWithGradient c previousGradient rho beta previousPoint
        previousMultiplier) Set.univ previousStep)
    (hcurrentMinimizes : IsMinOn
      (LALM.stepModelWithGradient c currentGradient rho beta currentPoint
        currentMultiplier) Set.univ currentStep)
    (hmultiplier : currentMultiplier =
      nextMultiplier c rho previousPoint previousMultiplier previousStep) :
    EqualityConstrained.constraintGradient c currentPoint
        (nextMultiplier c rho currentPoint currentMultiplier currentStep -
          currentMultiplier) =
      (-beta • currentStep + rho • EqualityConstrained.constraintGradient c
          currentPoint (error c currentPoint currentStep)) +
        (beta • previousStep - rho • EqualityConstrained.constraintGradient c
          previousPoint (error c previousPoint previousStep)) +
        (gradient f previousPoint - gradient f currentPoint) +
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier +
        ((previousGradient - gradient f previousPoint) -
          (currentGradient - gradient f currentPoint)) := by
  have hcurrent := perturbedMultiplierIdentityWithGradient currentGradient rho beta
    currentPoint currentMultiplier currentStep hcurrentMinimizes
  have hprevious := perturbedMultiplierIdentityWithGradient previousGradient rho beta
    previousPoint previousMultiplier previousStep hpreviousMinimizes
  rw [← hmultiplier] at hprevious
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Corollary 4.2: local admissibility and two adjacent model
minimizers control the constraint-gradient image of a multiplier increment. -/
theorem normConstraintGradientNextMultiplierSub_le_of_adjacentTransitions
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
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
    (hpoint : currentPoint = nextPoint c previousPoint previousStep)
    (hmultiplier : currentMultiplier =
      nextMultiplier c params.rho previousPoint previousMultiplier previousStep)
    (hadmPrevious : IsAdmissible h previousPoint previousStep)
    (hadmCurrent : IsAdmissible h currentPoint currentStep)
    (hstepPrevious : ‖previousStep‖ ≤ params.delta)
    (hstepCurrent : ‖currentStep‖ ≤ params.delta)
    (hmultiplierBound : ‖currentMultiplier‖ ≤ params.multiplierBound) :
    ‖EqualityConstrained.constraintGradient c currentPoint
        (nextMultiplier c params.rho currentPoint currentMultiplier currentStep -
          currentMultiplier)‖ ≤
      primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖previousStep‖ +
        ‖currentGradient - gradient f currentPoint‖ +
        ‖previousGradient - gradient f previousPoint‖ := by
  have hxCurrent := base_mem_region h currentPoint currentStep hadmCurrent
  have hxPrevious := base_mem_region h previousPoint previousStep hadmPrevious
  have herrorCurrent := normScaledConstraintGradientError_le_mul_norm h params
    currentPoint currentStep hadmCurrent hstepCurrent
  have herrorPrevious := normScaledConstraintGradientError_le_mul_norm h params
    previousPoint previousStep hadmPrevious hstepPrevious
  have hpointDisplacement :
      ‖currentPoint - previousPoint‖ ≤
        displacementFactor h params.delta * ‖previousStep‖ := by
    have hdisplacement := displacement_le h params.delta previousPoint previousStep
      hadmPrevious hstepPrevious
    rw [← hpoint] at hdisplacement
    exact hdisplacement
  have hgradientDifference :
      ‖gradient f previousPoint - gradient f currentPoint‖ ≤
        h.gradientLipschitz * displacementFactor h params.delta *
          ‖previousStep‖ := by
    have hlipschitz :
        ‖gradient f previousPoint - gradient f currentPoint‖ ≤
          h.gradientLipschitz * ‖currentPoint - previousPoint‖ := by
      calc
        ‖gradient f previousPoint - gradient f currentPoint‖ =
            dist (gradient f previousPoint) (gradient f currentPoint) :=
          (dist_eq_norm _ _).symm
        _ ≤ h.gradientLipschitz *
            dist previousPoint currentPoint :=
          h.lipschitzOn_gradient.dist_le_mul previousPoint hxPrevious
            currentPoint hxCurrent
        _ = h.gradientLipschitz * ‖currentPoint - previousPoint‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖gradient f previousPoint - gradient f currentPoint‖ ≤
          h.gradientLipschitz * ‖currentPoint - previousPoint‖ := hlipschitz
      _ ≤ h.gradientLipschitz *
          (displacementFactor h params.delta * ‖previousStep‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.gradientLipschitz * displacementFactor h params.delta *
          ‖previousStep‖ := by
        ring
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint‖ ≤
        h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖previousStep‖ := by
    have hlipschitz :
        ‖EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint‖ ≤
          h.constraintGradientLipschitz * ‖currentPoint - previousPoint‖ := by
      calc
        ‖EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint‖ =
            dist (EqualityConstrained.constraintGradient c previousPoint)
              (EqualityConstrained.constraintGradient c currentPoint) :=
          (dist_eq_norm _ _).symm
        _ ≤ h.constraintGradientLipschitz *
            dist previousPoint currentPoint :=
          h.lipschitzOn_constraintGradient.dist_le_mul previousPoint hxPrevious
            currentPoint hxCurrent
        _ = h.constraintGradientLipschitz * ‖currentPoint - previousPoint‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint‖ ≤
          h.constraintGradientLipschitz * ‖currentPoint - previousPoint‖ :=
        hlipschitz
      _ ≤ h.constraintGradientLipschitz *
          (displacementFactor h params.delta * ‖previousStep‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖previousStep‖ := by
        ring
  have hdisplacementFactorNonneg :
      0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint)
            currentMultiplier‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖previousStep‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint)
            currentMultiplier‖ ≤
          ‖EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint‖ *
              ‖currentMultiplier‖ :=
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint).le_opNorm
            currentMultiplier
      _ ≤ (h.constraintGradientLipschitz * displacementFactor h params.delta *
            ‖previousStep‖) * params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplierBound (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (NNReal.coe_nonneg _) hdisplacementFactorNonneg)
            (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖previousStep‖ := by
        ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hcurrentPair :
      ‖-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (error c currentPoint currentStep)‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖currentStep‖ := by
    calc
      ‖-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (error c currentPoint currentStep)‖ ≤
          ‖-(params.beta : ℝ) • currentStep‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (error c currentPoint currentStep)‖ := norm_add_le _ _
      _ = params.beta * ‖currentStep‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (error c currentPoint currentStep)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hbeta]
      _ ≤ params.beta * ‖currentStep‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖currentStep‖ := add_le_add_right herrorCurrent _
      _ = primalConstant h params.delta params.beta params.rho * ‖currentStep‖ := by
        rw [primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (error c previousPoint previousStep)‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖previousStep‖ := by
    calc
      ‖(params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (error c previousPoint previousStep)‖ ≤
          ‖(params.beta : ℝ) • previousStep‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (error c previousPoint previousStep)‖ := norm_sub_le _ _
      _ = params.beta * ‖previousStep‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (error c previousPoint previousStep)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ params.beta * ‖previousStep‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖previousStep‖ := add_le_add_right herrorPrevious _
      _ = primalConstant h params.delta params.beta params.rho * ‖previousStep‖ := by
        rw [primalConstant_def]
        ring
  have hdeterministicCore :
      ‖((-(params.beta : ℝ) • currentStep +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (error c currentPoint currentStep)) +
          ((params.beta : ℝ) • previousStep -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (error c previousPoint previousStep)) +
          (gradient f previousPoint - gradient f currentPoint) +
          (EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ := by
    calc
      ‖((-(params.beta : ℝ) • currentStep +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (error c currentPoint currentStep)) +
          ((params.beta : ℝ) • previousStep -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (error c previousPoint previousStep)) +
          (gradient f previousPoint - gradient f currentPoint) +
          (EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)‖ ≤
          ‖-(params.beta : ℝ) • currentStep +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (error c currentPoint currentStep)‖ +
          ‖(params.beta : ℝ) • previousStep -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (error c previousPoint previousStep)‖ +
          ‖gradient f previousPoint - gradient f currentPoint‖ +
          ‖(EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint) currentMultiplier‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • currentStep +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (error c currentPoint currentStep))
          ((params.beta : ℝ) • previousStep -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (error c previousPoint previousStep))
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • currentStep +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
                (error c currentPoint currentStep)) +
            ((params.beta : ℝ) • previousStep -
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
                (error c previousPoint previousStep)))
          (gradient f previousPoint - gradient f currentPoint)
        have hthird := norm_add_le
          (((-(params.beta : ℝ) • currentStep +
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
                  (error c currentPoint currentStep)) +
              ((params.beta : ℝ) • previousStep -
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
                  (error c previousPoint previousStep))) +
            (gradient f previousPoint - gradient f currentPoint))
          ((EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)
        linarith
      _ ≤ primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          primalConstant h params.delta params.beta params.rho * ‖previousStep‖ +
          h.gradientLipschitz * displacementFactor h params.delta * ‖previousStep‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            displacementFactor h params.delta * ‖previousStep‖ :=
        add_le_add (add_le_add (add_le_add hcurrentPair hpreviousPair)
          hgradientDifference) hoperatorApplied
      _ = primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ := by
        rw [primalComparisonConstant_def]
        ring
  have hidentity := constraintGradientNextMultiplierSub_of_adjacentTransitions
    (f := f) c params.rho params.beta previousPoint currentPoint previousGradient
    currentGradient previousStep currentStep previousMultiplier currentMultiplier
    hpreviousMinimizes hcurrentMinimizes hmultiplier
  rw [hidentity]
  have herrorDifference :
      ‖(previousGradient - gradient f previousPoint) -
          (currentGradient - gradient f currentPoint)‖ ≤
        ‖currentGradient - gradient f currentPoint‖ +
          ‖previousGradient - gradient f previousPoint‖ := by
    calc
      ‖(previousGradient - gradient f previousPoint) -
          (currentGradient - gradient f currentPoint)‖ ≤
          ‖previousGradient - gradient f previousPoint‖ +
            ‖currentGradient - gradient f currentPoint‖ := norm_sub_le _ _
      _ = ‖currentGradient - gradient f currentPoint‖ +
          ‖previousGradient - gradient f previousPoint‖ := by
        ring
  calc
    ‖((-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (error c currentPoint currentStep)) +
        ((params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (error c previousPoint previousStep)) +
        (gradient f previousPoint - gradient f currentPoint) +
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier) +
        ((previousGradient - gradient f previousPoint) -
          (currentGradient - gradient f currentPoint))‖ ≤
        ‖((-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (error c currentPoint currentStep)) +
        ((params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (error c previousPoint previousStep)) +
        (gradient f previousPoint - gradient f currentPoint) +
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)‖ +
          ‖(previousGradient - gradient f previousPoint) -
            (currentGradient - gradient f currentPoint)‖ := norm_add_le _ _
    _ ≤ primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentGradient - gradient f currentPoint‖ +
          ‖previousGradient - gradient f previousPoint‖ :=
      by
        simpa only [add_assoc] using
          (add_le_add hdeterministicCore herrorDifference)

/-- Helper for Corollary 4.2: four scalar terms are controlled by the larger
weighted square and the two unweighted squares. -/
theorem weightedFourTermSquare_le
    (A B x y e₀ e₁ : ℝ) :
    (A * x + B * y + e₀ + e₁) ^ 2 ≤
      4 * (max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) +
        (e₀ ^ 2 + e₁ ^ 2)) := by
  let a := A * x
  let d := B * y
  have had : (a + d) ^ 2 ≤ 2 * (a ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - d)]
  have he : (e₀ + e₁) ^ 2 ≤ 2 * (e₀ ^ 2 + e₁ ^ 2) := by
    nlinarith [sq_nonneg (e₀ - e₁)]
  have htwoNonneg : (0 : ℝ) ≤ 2 := by
    norm_num
  have hfourNonneg : (0 : ℝ) ≤ 4 := by
    norm_num
  have hfour :
      (a + d + e₀ + e₁) ^ 2 ≤
        4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by
    calc
      (a + d + e₀ + e₁) ^ 2 = ((a + d) + (e₀ + e₁)) ^ 2 := by
        ring
      _ ≤ 2 * ((a + d) ^ 2 + (e₀ + e₁) ^ 2) := by
        nlinarith [sq_nonneg ((a + d) - (e₀ + e₁))]
      _ ≤ 2 * (2 * (a ^ 2 + d ^ 2) + 2 * (e₀ ^ 2 + e₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add had he) htwoNonneg
      _ = 4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by
        ring
  have ha : a ^ 2 ≤ max (A ^ 2) (B ^ 2) * x ^ 2 := by
    dsimp only [a]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hd : d ^ 2 ≤ max (A ^ 2) (B ^ 2) * y ^ 2 := by
    dsimp only [d]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hsquares :
      a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2 ≤
        max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) +
          (e₀ ^ 2 + e₁ ^ 2) := by
    calc
      a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2 ≤
          (max (A ^ 2) (B ^ 2) * x ^ 2 +
            max (A ^ 2) (B ^ 2) * y ^ 2) + e₀ ^ 2 + e₁ ^ 2 :=
        add_le_add (add_le_add (add_le_add ha hd) (le_refl _)) (le_refl _)
      _ = max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) +
          (e₀ ^ 2 + e₁ ^ 2) := by
        ring
  calc
    (A * x + B * y + e₀ + e₁) ^ 2 = (a + d + e₀ + e₁) ^ 2 := by
      simp only [a, d]
    _ ≤ 4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := hfour
    _ ≤ 4 * (max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) +
        (e₀ ^ 2 + e₁ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsquares hfourNonneg

/-- Helper for Corollary 4.2: a constraint-gradient increment bound at a
regular point yields the corrected squared multiplier estimate. -/
theorem normMultiplierIncrementSquare_le_of_constraintGradientBound
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (increment : EuclideanSpace ℝ (Fin m))
    (currentStep previousStep currentError previousError :
      EuclideanSpace ℝ (Fin n))
    (hx : x ∈ h.region)
    (hcomparison :
      ‖EqualityConstrained.constraintGradient c x increment‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentError‖ + ‖previousError‖) :
    ‖increment‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2) := by
  have hlicq := h.licqLowerBound x hx increment
  have hscaled := hlicq.trans hcomparison
  have herrorFactorNonneg : 0 ≤ errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  have hdisplacementFactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hprimalNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho := by
    rw [primalConstant_def]
    exact add_nonneg params.spec.1.2.1.le
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg params.spec.1.2.2.1.le (NNReal.coe_nonneg _))
            herrorFactorNonneg)
        (NNReal.coe_nonneg _))
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def]
    exact add_nonneg hprimalNonneg
      (mul_nonneg
        (add_nonneg (NNReal.coe_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)))
        hdisplacementFactorNonneg)
  have hrightNonneg :
      0 ≤ primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖previousStep‖ +
        ‖currentError‖ + ‖previousError‖ := by
    positivity
  have hleftNonneg :
      0 ≤ (h.licqModulus : ℝ) * ‖increment‖ := by
    positivity
  have hscaledSquare :
      ((h.licqModulus : ℝ) * ‖increment‖) ^ 2 ≤
        (primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentError‖ + ‖previousError‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  have hfour := weightedFourTermSquare_le
    (primalConstant h params.delta params.beta params.rho)
    (primalComparisonConstant h params.delta params.beta params.rho
      params.multiplierBound)
    ‖currentStep‖ ‖previousStep‖ ‖currentError‖ ‖previousError‖
  have hscaledExpanded :
      (h.licqModulus : ℝ) ^ 2 * ‖increment‖ ^ 2 ≤
        4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2)) := by
    calc
      (h.licqModulus : ℝ) ^ 2 * ‖increment‖ ^ 2 =
          ((h.licqModulus : ℝ) * ‖increment‖) ^ 2 := by
        ring
      _ ≤ (primalConstant h params.delta params.beta params.rho *
            ‖currentStep‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentError‖ + ‖previousError‖) ^ 2 := hscaledSquare
      _ ≤ 4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2)) := hfour
  have hsigmaSq : 0 < (h.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos h.licqModulus_pos
  have hscaledCommuted :
      ‖increment‖ ^ 2 * (h.licqModulus : ℝ) ^ 2 ≤
        4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2)) := by
    simpa only [mul_comm] using hscaledExpanded
  calc
    ‖increment‖ ^ 2 ≤
        (4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2))) /
          (h.licqModulus : ℝ) ^ 2 :=
      (le_div_iff₀ hsigmaSq).2 hscaledCommuted
    _ = multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2) := by
      rw [multiplierPrimalConstant_def, LALM.multiplierErrorConstant_def]
      ring

namespace StochasticRun.Localization

/-- Helper for Corollary 4.2: the clipped estimate error attached to a finite
active state and its fresh batch. -/
noncomputable def canonicalActiveGradientErrorAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    {X : Set (EuclideanSpace ℝ (Fin n))} (k : ℕ)
    (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  canonicalClippedEstimateAt h oracle Q B b k (activeNumericalInput z) -
    gradient f z.1.1.1

/-- Corollary 4.2: every finite active canonical transition satisfies the
fixed-multiplier augmented-Lagrangian descent inequality. -/
theorem canonicalActiveAugmentedLagrangianDescent
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (z : ActivePreBatchState h params X × (ℕ → Ξ)) :
    ℒ[f, c; params.rho](canonicalActiveNextPointAt h oracle params Q B b k z,
        z.1.1.2.2.1) ≤
      ℒ[f, c; params.rho](z.1.1.1, z.1.1.2.2.1) -
        (params.beta / 2) *
          ‖canonicalActiveBaseStepAt h oracle params Q B b k z‖ ^ 2 +
        (2 / params.beta) *
          ‖canonicalActiveGradientErrorAt h oracle params Q B b k z‖ ^ 2 := by
  rcases z with ⟨s, batch⟩
  have hminimizesCanonical :=
    canonicalBaseStep_minimizesStepModelWithGradient c params.rho params.beta
      s.1.1
      (canonicalClippedEstimateAt h oracle Q B b k
        (activeNumericalInput (s, batch)))
      s.1.2.2.1 params.spec.1.2.2.1 params.spec.1.2.1
  have hminimizes : IsMinOn
      (LALM.stepModelWithGradient c
        (canonicalClippedEstimateAt h oracle Q B b k
          (activeNumericalInput (s, batch)))
        params.rho params.beta s.1.1 s.1.2.2.1) Set.univ
      (canonicalActiveBaseStepAt h oracle params Q B b k (s, batch)) := by
    simpa only [canonicalActiveBaseStepAt_apply, canonicalClippedEstimateAt,
      activeNumericalInput] using hminimizesCanonical
  have hdescent := augmentedLagrangianDescent_of_transitionBounds h params
    s.1.1 s.1.2.2.1
    (canonicalClippedEstimateAt h oracle Q B b k
      (activeNumericalInput (s, batch)))
    (canonicalActiveBaseStepAt h oracle params Q B b k (s, batch)) hminimizes
    (canonicalActiveBaseStepAt_isAdmissible h_region k (s, batch))
    (norm_canonicalActiveBaseStepAt_le h_region k (s, batch))
    s.norm_effectiveMultiplier_le
  simpa only [canonicalActiveNextPointAt_apply, canonicalActiveGradientErrorAt] using
    hdescent

/-- Corollary 4.2: two compatible finite active canonical transitions satisfy
the corrected squared multiplier-increment estimate. -/
theorem canonicalActiveMultiplierIncrementSquare_le
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ)
    (previous : ActivePreBatchState h params X × (ℕ → Ξ))
    (current : ActivePreBatchState h params X × (ℕ → Ξ))
    (hcurrentData : current.1.1 =
      canonicalActiveNextDataAt h oracle params Q B b k previous) :
    ‖canonicalActiveNextMultiplierAt h oracle params Q B b (k + 1) current -
        current.1.1.2.2.1‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 +
          ‖canonicalActiveBaseStepAt h oracle params Q B b k previous‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖canonicalActiveGradientErrorAt h oracle params Q B b (k + 1) current‖ ^ 2 +
          ‖canonicalActiveGradientErrorAt h oracle params Q B b k previous‖ ^ 2) := by
  rcases previous with ⟨sPrevious, batchPrevious⟩
  rcases current with ⟨sCurrent, batchCurrent⟩
  have hpreviousPoint :
      sCurrent.1.1 = canonicalActiveNextPointAt h oracle params Q B b k
        (sPrevious, batchPrevious) := by
    rw [hcurrentData, canonicalActiveNextDataAt_current]
  have hcurrentMultiplier :
      sCurrent.1.2.2.1 = canonicalActiveNextMultiplierAt h oracle params Q B b k
        (sPrevious, batchPrevious) := by
    rw [hcurrentData, canonicalActiveNextDataAt_multiplier]
  have hpreviousMinimizes :=
    canonicalBaseStep_minimizesStepModelWithGradient c params.rho params.beta
      sPrevious.1.1
      (canonicalClippedEstimateAt h oracle Q B b k
        (activeNumericalInput (sPrevious, batchPrevious)))
      sPrevious.1.2.2.1 params.spec.1.2.2.1 params.spec.1.2.1
  have hcurrentMinimizes :=
    canonicalBaseStep_minimizesStepModelWithGradient c params.rho params.beta
      sCurrent.1.1
      (canonicalClippedEstimateAt h oracle Q B b (k + 1)
        (activeNumericalInput (sCurrent, batchCurrent)))
      sCurrent.1.2.2.1 params.spec.1.2.2.1 params.spec.1.2.1
  have hpreviousMinimizes' : IsMinOn
      (LALM.stepModelWithGradient c
        (canonicalClippedEstimateAt h oracle Q B b k
          (activeNumericalInput (sPrevious, batchPrevious)))
        params.rho params.beta sPrevious.1.1 sPrevious.1.2.2.1) Set.univ
      (canonicalActiveBaseStepAt h oracle params Q B b k
        (sPrevious, batchPrevious)) := by
    simpa only [canonicalActiveBaseStepAt_apply, canonicalClippedEstimateAt,
      activeNumericalInput] using hpreviousMinimizes
  have hcurrentMinimizes' : IsMinOn
      (LALM.stepModelWithGradient c
        (canonicalClippedEstimateAt h oracle Q B b (k + 1)
          (activeNumericalInput (sCurrent, batchCurrent)))
        params.rho params.beta sCurrent.1.1 sCurrent.1.2.2.1) Set.univ
      (canonicalActiveBaseStepAt h oracle params Q B b (k + 1)
        (sCurrent, batchCurrent)) := by
    simpa only [canonicalActiveBaseStepAt_apply, canonicalClippedEstimateAt,
      activeNumericalInput] using hcurrentMinimizes
  have hcomparison := normConstraintGradientNextMultiplierSub_le_of_adjacentTransitions
    (f := f) (c := c) h params sPrevious.1.1 sCurrent.1.1
    sPrevious.1.2.2.1 sCurrent.1.2.2.1
    (canonicalClippedEstimateAt h oracle Q B b k
      (activeNumericalInput (sPrevious, batchPrevious)))
    (canonicalClippedEstimateAt h oracle Q B b (k + 1)
      (activeNumericalInput (sCurrent, batchCurrent)))
    (canonicalActiveBaseStepAt h oracle params Q B b k
      (sPrevious, batchPrevious))
    (canonicalActiveBaseStepAt h oracle params Q B b (k + 1)
      (sCurrent, batchCurrent))
    hpreviousMinimizes' hcurrentMinimizes'
    hpreviousPoint hcurrentMultiplier
    (canonicalActiveBaseStepAt_isAdmissible h_region k (sPrevious, batchPrevious))
    (canonicalActiveBaseStepAt_isAdmissible h_region (k + 1)
      (sCurrent, batchCurrent))
    (norm_canonicalActiveBaseStepAt_le h_region k (sPrevious, batchPrevious))
    (norm_canonicalActiveBaseStepAt_le h_region (k + 1) (sCurrent, batchCurrent))
    sCurrent.norm_multiplier_le
  have hcomparison' :
      ‖EqualityConstrained.constraintGradient c sCurrent.1.1
          (canonicalActiveNextMultiplierAt h oracle params Q B b (k + 1)
            (sCurrent, batchCurrent) - sCurrent.1.2.2.1)‖ ≤
        primalConstant h params.delta params.beta params.rho *
            ‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1)
              (sCurrent, batchCurrent)‖ +
          primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound *
            ‖canonicalActiveBaseStepAt h oracle params Q B b k
              (sPrevious, batchPrevious)‖ +
          ‖canonicalActiveGradientErrorAt h oracle params Q B b (k + 1)
              (sCurrent, batchCurrent)‖ +
          ‖canonicalActiveGradientErrorAt h oracle params Q B b k
              (sPrevious, batchPrevious)‖ := by
    simpa only [canonicalActiveNextMultiplierAt_apply,
      canonicalActiveGradientErrorAt] using hcomparison
  have hsq := normMultiplierIncrementSquare_le_of_constraintGradientBound
    (f := f) (c := c) h params sCurrent.1.1
    (canonicalActiveNextMultiplierAt h oracle params Q B b (k + 1)
      (sCurrent, batchCurrent) - sCurrent.1.2.2.1)
    (canonicalActiveBaseStepAt h oracle params Q B b (k + 1)
      (sCurrent, batchCurrent))
    (canonicalActiveBaseStepAt h oracle params Q B b k (sPrevious, batchPrevious))
    (canonicalActiveGradientErrorAt h oracle params Q B b (k + 1)
      (sCurrent, batchCurrent))
    (canonicalActiveGradientErrorAt h oracle params Q B b k
      (sPrevious, batchPrevious))
    (canonicalActivePoint_mem_region h_region (sCurrent, batchCurrent))
    hcomparison'
  simpa only [canonicalActiveGradientErrorAt] using hsq

end StochasticRun.Localization

/-- Helper for Corollary 4.2: the corrected multiplier update changes the
augmented Lagrangian by the penalty-scaled squared multiplier increment. -/
theorem augmentedLagrangian_nextMultiplier_eq
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    ℒ[f, c; params.rho](nextPoint c x p,
        nextMultiplier c params.rho x multiplier p) =
      ℒ[f, c; params.rho](nextPoint c x p, multiplier) +
        ‖nextMultiplier c params.rho x multiplier p - multiplier‖ ^ 2 /
          params.rho := by
  have hupdate :
      nextMultiplier c params.rho x multiplier p =
        multiplier + (params.rho : ℝ) • c (nextPoint c x p) := by
    rw [nextMultiplier_def]
  rw [augmentedLagrangian_def, augmentedLagrangian_def, hupdate,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  field_simp [params.spec.1.2.2.1.ne']
  ring

/-- Helper for Corollary 4.2: the finite active Lyapunov value stores the
augmented Lagrangian and the preceding base-step square. -/
noncomputable def finiteActiveLyapunov
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (previousStep : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ℒ[f, c; params.rho](x, multiplier) +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * ‖previousStep‖ ^ 2

/-- Helper for Corollary 4.2: the finite active Lyapunov value exposes its two
stable components without unfolding the transition. -/
theorem finiteActiveLyapunov_def
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (previousStep : EuclideanSpace ℝ (Fin n)) :
    finiteActiveLyapunov h params x multiplier previousStep =
      ℒ[f, c; params.rho](x, multiplier) +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖previousStep‖ ^ 2 := by
  rfl

namespace StochasticRun.Localization

/-- Corollary 4.2: a positive-index finite active transition decreases the
corrected Lyapunov value up to the two adjacent clipped-estimate errors. -/
theorem canonicalActiveFiniteLyapunovDescent
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ)
    (previous : ActivePreBatchState h params X × (ℕ → Ξ))
    (current : ActivePreBatchState h params X × (ℕ → Ξ))
    (hcurrentData : current.1.1 =
      canonicalActiveNextDataAt h oracle params Q B b k previous) :
    finiteActiveLyapunov h params
        (canonicalActiveNextPointAt h oracle params Q B b (k + 1) current)
        (canonicalActiveNextMultiplierAt h oracle params Q B b (k + 1) current)
        (canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current) ≤
      finiteActiveLyapunov h params current.1.1.1 current.1.1.2.2.1
        (canonicalActiveBaseStepAt h oracle params Q B b k previous) -
        (params.beta / 4) *
          ‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 +
        lyapunovErrorConstant h params *
          (‖canonicalActiveGradientErrorAt h oracle params Q B b (k + 1) current‖ ^ 2 +
            ‖canonicalActiveGradientErrorAt h oracle params Q B b k previous‖ ^ 2) := by
  have hlagrangian := canonicalActiveAugmentedLagrangianDescent
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b)
    h_region (k + 1) current
  have hmultiplier := canonicalActiveMultiplierIncrementSquare_le
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b)
    h_region k previous current hcurrentData
  have hlagrangian' := hlagrangian
  simp only [canonicalActiveNextPointAt] at hlagrangian'
  have hmultiplierDivided :=
    (div_le_div_iff_of_pos_right params.spec.1.2.2.1).2 hmultiplier
  have hmultiplierDiv :
      ‖canonicalActiveNextMultiplierAt h oracle params Q B b (k + 1) current -
          current.1.1.2.2.1‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 +
            ‖canonicalActiveBaseStepAt h oracle params Q B b k previous‖ ^ 2) +
        (LALM.multiplierErrorConstant h / params.rho) *
          (‖canonicalActiveGradientErrorAt h oracle params Q B b (k + 1) current‖ ^ 2 +
            ‖canonicalActiveGradientErrorAt h oracle params Q B b k previous‖ ^ 2) := by
    calc
      ‖canonicalActiveNextMultiplierAt h oracle params Q B b (k + 1) current -
          current.1.1.2.2.1‖ ^ 2 / params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
                (‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 +
                  ‖canonicalActiveBaseStepAt h oracle params Q B b k previous‖ ^ 2) +
            LALM.multiplierErrorConstant h *
              (‖canonicalActiveGradientErrorAt h oracle params Q B b (k + 1) current‖ ^ 2 +
                ‖canonicalActiveGradientErrorAt h oracle params Q B b k previous‖ ^ 2)) /
            params.rho := hmultiplierDivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 +
            ‖canonicalActiveBaseStepAt h oracle params Q B b k previous‖ ^ 2) +
          (LALM.multiplierErrorConstant h / params.rho) *
            (‖canonicalActiveGradientErrorAt h oracle params Q B b (k + 1) current‖ ^ 2 +
              ‖canonicalActiveGradientErrorAt h oracle params Q B b k previous‖ ^ 2) := by
        ring
  have hcoefficient :=
    StochasticRun.BoundedAdmissiblePath.multiplierPrimalConstant_div_rho_le_beta_div_eight
      h params
  simp only [canonicalActiveNextMultiplierAt] at hmultiplierDiv
  have htwiceCoefficient :
      2 * (multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.rho) ≤ params.beta / 4 := by
    linarith
  have hcurrentCoefficient :
      2 * (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
          ‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 ≤
        (params.beta / 4) *
          ‖canonicalActiveBaseStepAt h oracle params Q B b (k + 1) current‖ ^ 2 :=
    mul_le_mul_of_nonneg_right htwiceCoefficient (sq_nonneg _)
  have hpreviousErrorNonneg :
      (0 : ℝ) ≤ (2 / params.beta) *
        ‖canonicalActiveGradientErrorAt h oracle params Q B b k previous‖ ^ 2 := by
    positivity
  rw [finiteActiveLyapunov, finiteActiveLyapunov]
  simp only [canonicalActiveNextPointAt, canonicalActiveNextMultiplierAt]
  rw [augmentedLagrangian_nextMultiplier_eq]
  rw [lyapunovErrorConstant_def]
  have hsum := add_le_add hlagrangian' hmultiplierDiv
  linarith [hsum, hcurrentCoefficient, hpreviousErrorNonneg]

end StochasticRun.Localization

end LALM.Correction

end
