/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedTransition
public import TR_LALM_theory.Theorem_2_10
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedTransition

public section

open MeasureTheory
open scoped InnerProductSpace LALM NNReal

namespace LALM.FiniteStopped

universe u

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {params : LALM.Parameters h x₀ multiplier₀}

/-- Helper for Theorem 3.7: a minimizer of the explicit-gradient quadratic model
satisfies its base first-order normal equation. -/
theorem stepModelWithGradientOptimality
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g rho beta x multiplier)
      Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p = 0 := by
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
      LALM.stepModel linearObjective c rho beta x multiplier =
        LALM.stepModelWithGradient c g rho beta x multiplier := by
    funext q
    rw [LALM.stepModel_eq_stepModelWithGradient, hgradient]
  have hp' : IsMinOn (LALM.stepModel linearObjective c rho beta x multiplier)
      Set.univ p := by
    simpa only [hmodels] using hp
  have hzero := LALM.stepModelGradient_eq_zero_of_minimizes
    linearObjective c rho beta x multiplier p hp'
  change gradient linearObjective x +
      EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p = 0 at hzero
  rw [hgradient] at hzero
  exact hzero

/-- Helper for Theorem 3.7: regularity and an effective-multiplier bound
control any minimizer of the explicit-gradient base model. -/
theorem normBaseStep_le_of_minimizes
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ h.region)
    (hgradient : ‖g‖ ≤ h.gradientBound)
    (heffective :
      ‖multiplier + (params.rho : ℝ) • c x‖ ≤
        3 * params.multiplierBound)
    (hp : IsMinOn
      (LALM.stepModelWithGradient c g params.rho params.beta x multiplier)
        Set.univ p) :
    ‖p‖ ≤ params.delta := by
  have hoptimality := stepModelWithGradientOptimality c g params.rho params.beta
    x multiplier p hp
  have hequation :
      (params.beta : ℝ) • p +
          (params.rho : ℝ) • (fderiv ℝ c x).adjoint (fderiv ℝ c x p) =
        -g - (fderiv ℝ c x).adjoint
          (multiplier + (params.rho : ℝ) • c x) := by
    simp only [EqualityConstrained.constraintGradient_def, map_add, map_smul]
      at hoptimality ⊢
    linear_combination (norm := module) hoptimality
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 ≤ (params.rho : ℝ) := params.spec.1.2.2.1.le
  have hestimate := LALM.Run.normDampedNormalEquation_le
    (fderiv ℝ c x) hbeta hrho h.licqModulus_pos
    (h.licqLowerBound x hx) p g
    (multiplier + params.rho • c x) hequation
  have hoperator :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le x hx
  have hdenom :
      0 < (params.beta : ℝ) + params.rho * (h.licqModulus : ℝ) ^ 2 :=
    add_pos_of_pos_of_nonneg hbeta
      (mul_nonneg hrho (sq_nonneg (h.licqModulus : ℝ)))
  have hgradientTerm :
      ‖g‖ / params.beta ≤ h.gradientBound / params.beta :=
    (div_le_div_iff_of_pos_right hbeta).2 hgradient
  have hproduct :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ *
          ‖multiplier + params.rho • c x‖ ≤
        h.constraintGradientBound * (3 * params.multiplierBound) :=
    mul_le_mul hoperator heffective (norm_nonneg _)
      (NNReal.coe_nonneg h.constraintGradientBound)
  have hconstraintTerm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ *
          ‖multiplier + params.rho • c x‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) ≤
        3 * h.constraintGradientBound * params.multiplierBound /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
    rw [div_le_div_iff_of_pos_right hdenom]
    nlinarith
  calc
    ‖p‖ ≤ ‖g‖ / params.beta +
        ‖ContinuousLinearMap.adjoint (fderiv ℝ c x)‖ *
          ‖multiplier + params.rho • c x‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Theorem 3.7: the inverse-defined finite base step satisfies the
explicit-gradient model optimality equation. -/
theorem canonicalModelStep_optimality
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + rho •
          (c x + fderiv ℝ c x (canonicalModelStep c rho beta x g multiplier))) +
        beta • canonicalModelStep c rho beta x g multiplier = 0 := by
  let p := canonicalModelStep c rho beta x g multiplier
  have hoperator :
      modelStepOperator c rho beta x p =
        -(g + EqualityConstrained.constraintGradient c x
          (multiplier + rho • c x)) := by
    have hinverse :=
      ((modelStepOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).1
        (rfl : p = p)
    exact hinverse.symm
  simp only [modelStepOperator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add,
    map_smul] at hoperator ⊢
  linear_combination (norm := module) hoperator

/-- Helper for Theorem 3.7: the canonical finite base step is a global
minimizer of the explicit-gradient quadratic model. -/
theorem canonicalModelStep_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    IsMinOn (LALM.stepModelWithGradient c g rho beta x multiplier) Set.univ
      (canonicalModelStep c rho beta x g multiplier) := by
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
      LALM.stepModel linearObjective c rho beta x multiplier =
        LALM.stepModelWithGradient c g rho beta x multiplier := by
    funext q
    rw [LALM.stepModel_eq_stepModelWithGradient, hgradient]
  obtain ⟨p, hp, _⟩ := LALM.Run.existsUniqueStepModelMinimizer
    linearObjective c rho beta x multiplier hrho hbeta
  have hp' : IsMinOn (LALM.stepModelWithGradient c g rho beta x multiplier)
      Set.univ p := by
    simpa only [← hmodels] using hp
  have hcanonical : canonicalModelStep c rho beta x g multiplier = p := by
    have hoptimal := stepModelWithGradientOptimality c g rho beta x multiplier p hp'
    have hsum :
        (g + EqualityConstrained.constraintGradient c x
          (multiplier + rho • c x)) + modelStepOperator c rho beta x p = 0 := by
      simp only [modelStepOperator, add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add,
        map_smul] at hoptimal ⊢
      linear_combination (norm := module) hoptimal
    have hoperator : modelStepOperator c rho beta x p =
        -(g + EqualityConstrained.constraintGradient c x
          (multiplier + rho • c x)) :=
      eq_neg_of_add_eq_zero_right hsum
    unfold canonicalModelStep
    exact ((modelStepOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).2
      hoperator.symm
  simpa only [hcanonical] using hp'

/-- Helper for Theorem 3.7: the finite base optimality equation exposes the
constraint linearization error after the actual multiplier update. -/
@[expose] noncomputable def baseNextMultiplier
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  multiplier + rho • c (x + p)

/-- Helper for Theorem 3.7: the nonlinear constraint remainder of a base
transition is measured relative to the uncorrected endpoint `x + p`. -/
@[expose] noncomputable def baseLinearizationError
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  c (x + p) - c x - fderiv ℝ c x p

/-- Helper for Theorem 3.7: the base multiplier update and linearization error
have their defining formulas. -/
theorem baseNextMultiplier_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    baseNextMultiplier c rho x multiplier p = multiplier + rho • c (x + p) := rfl

/-- Helper for Theorem 3.7: the base linearization error has its Taylor
remainder spelling. -/
theorem baseLinearizationError_def
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) :
    baseLinearizationError c x p = c (x + p) - c x - fderiv ℝ c x p := rfl

/-- Helper for Theorem 3.7: the finite base optimality equation exposes the
constraint linearization error after the actual multiplier update. -/
theorem canonicalModelStep_perturbedMultiplierIdentity
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    g + EqualityConstrained.constraintGradient c x
        (baseNextMultiplier c rho x multiplier
          (canonicalModelStep c rho beta x g multiplier)) +
        beta • canonicalModelStep c rho beta x g multiplier =
      rho • EqualityConstrained.constraintGradient c x
        (baseLinearizationError c x
          (canonicalModelStep c rho beta x g multiplier)) := by
  rw [baseNextMultiplier_def, baseLinearizationError_def]
  simp only [map_add, map_sub, map_smul]
  have hstationary := canonicalModelStep_optimality c rho beta x g multiplier hrho hbeta
  simp only [map_add, map_smul] at hstationary
  linear_combination (norm := module) hstationary

/- A base transition is intentionally described by its current point and raw
step.  These local identities form the proof interface used by the finite
stopped path, without unfolding the absorbing state construction. -/

/-- Helper for Theorem 3.7: a regular segment gives the quadratic constraint
Taylor remainder bound for a base transition. -/
theorem baseLinearizationError_norm_le_of_segment
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x (x + p) ⊆ h.region) :
    ‖baseLinearizationError c x p‖ ≤
      LALM.linearizationConstant h * ‖p‖ ^ 2 := by
  have hremainder := norm_sub_sub_fderiv_le c h.constraintGradientLipschitz
    h.region x (x + p)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hsegment
  simpa only [baseLinearizationError, add_sub_cancel_left,
    LALM.linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using
    hremainder

/-- Helper for Theorem 3.7: a regular segment gives the quadratic objective
Taylor upper estimate for a base transition. -/
theorem baseObjectiveChange_le_of_segment
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x (x + p) ⊆ h.region) :
    f (x + p) - f x ≤
      ⟪gradient f x, p⟫_ℝ + (h.gradientLipschitz : ℝ) / 2 * ‖p‖ ^ 2 := by
  have hremainder := norm_sub_sub_fderiv_le f h.gradientLipschitz h.region
    x (x + p)
    (fun _ hz ↦ h.differentiableAt_objective hz)
    h.lipschitzOn_objectiveFDeriv hsegment
  have hsigned :
      f (x + p) - f x - fderiv ℝ f x p ≤
        ‖f (x + p) - f x - fderiv ℝ f x p‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (x + p) - f x - fderiv ℝ f x p)
  rw [← inner_gradient_left] at hremainder hsigned
  simp only [add_sub_cancel_left] at hremainder
  nlinarith [hremainder]

/-- Helper for Theorem 3.7: explicit-gradient model optimality identifies the
linearized augmented-Lagrangian change of a base step. -/
theorem baseLinearizedAugmentedLagrangianChange_eq_of_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g rho beta x multiplier)
      Set.univ p) :
    ⟪g, p⟫_ℝ + ⟪multiplier, fderiv ℝ c x p⟫_ℝ +
        (rho / 2) *
          (‖c x + fderiv ℝ c x p‖ ^ 2 - ‖c x‖ ^ 2) =
      -beta * ‖p‖ ^ 2 - (rho / 2) * ‖fderiv ℝ c x p‖ ^ 2 := by
  have hfirstOrder := stepModelWithGradientOptimality c g rho beta x multiplier p hp
  have hoptimal := congrArg (fun v ↦ ⟪v, p⟫_ℝ) hfirstOrder
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    inner_zero_left] at hoptimal
  rw [norm_add_sq_real]
  nlinarith

/-- Helper for Theorem 3.7: the endpoint constraint equals its linearization
plus the named base Taylor remainder. -/
theorem baseConstraintValue_eq_linearization_add_error
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x p : EuclideanSpace ℝ (Fin n)) :
    c (x + p) = c x + fderiv ℝ c x p + baseLinearizationError c x p := by
  rw [baseLinearizationError]
  module

/-- Helper for Theorem 3.7: the augmented-Lagrangian change of a base step
splits into its linearized part and the two Taylor-remainder terms. -/
theorem baseAugmentedLagrangianChange_eq_linearized
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    ℒ[f, c; params.rho](x + p, multiplier) -
        ℒ[f, c; params.rho](x, multiplier) =
      (f (x + p) - f x) +
        ⟪multiplier, fderiv ℝ c x p⟫_ℝ +
        (params.rho / 2) *
          (‖c x + fderiv ℝ c x p‖ ^ 2 - ‖c x‖ ^ 2) +
        ⟪multiplier + (params.rho : ℝ) •
            (c x + fderiv ℝ c x p), baseLinearizationError c x p⟫_ℝ +
        (params.rho / 2) * ‖baseLinearizationError c x p‖ ^ 2 := by
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    baseConstraintValue_eq_linearization_add_error c x p, norm_add_sq_real]
  simp only [inner_add_right, inner_add_left, inner_smul_left,
    starRingEnd_apply, star_trivial]
  ring

/-- Helper for Theorem 3.7: the constraint Taylor remainder contributes at most
the constraint part of the base model constant. -/
theorem baseConstraintRemainderContribution_le
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x p : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hsegment : segment ℝ x (x + p) ⊆ h.region)
    (hstep : ‖p‖ ≤ params.delta)
    (heffective :
      ‖multiplier + (params.rho : ℝ) • c x‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ⟪multiplier + (params.rho : ℝ) •
          (c x + fderiv ℝ c x p), baseLinearizationError c x p⟫_ℝ +
        (params.rho / 2) * ‖baseLinearizationError c x p‖ ^ 2 ≤
      (LALM.linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) +
        (params.rho / 2) * LALM.linearizationConstant h ^ 2 * params.delta ^ 2) *
          ‖p‖ ^ 2 := by
  have hx : x ∈ h.region := hsegment (left_mem_segment ℝ _ _)
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
      ‖multiplier + (params.rho : ℝ) •
          (c x + fderiv ℝ c x p)‖ ≤
        3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
    have hdecomposition :
        multiplier + (params.rho : ℝ) • (c x + fderiv ℝ c x p) =
          (multiplier + (params.rho : ℝ) • c x) +
            (params.rho : ℝ) • fderiv ℝ c x p := by
      module
    rw [hdecomposition]
    have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
    calc
      ‖(multiplier + (params.rho : ℝ) • c x) +
          (params.rho : ℝ) • fderiv ℝ c x p‖ ≤
          ‖multiplier + (params.rho : ℝ) • c x‖ +
            ‖(params.rho : ℝ) • fderiv ℝ c x p‖ := norm_add_le _ _
      _ ≤ 3 * params.multiplierBound +
          params.rho * (h.constraintGradientBound * ‖p‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
        exact add_le_add heffective
          (mul_le_mul_of_nonneg_left hlinearizedStep hrho.le)
      _ ≤ 3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
        have hcoefficient :
            (0 : ℝ) ≤ params.rho * h.constraintGradientBound := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hstep hcoefficient]
  have herror := baseLinearizationError_norm_le_of_segment h x p hsegment
  have hlinearizedBoundNonneg :
      (0 : ℝ) ≤ 3 * params.multiplierBound +
        params.rho * h.constraintGradientBound * params.delta :=
    (norm_nonneg _).trans heffectiveLinearized
  have hinnerContribution :
      ⟪multiplier + (params.rho : ℝ) •
            (c x + fderiv ℝ c x p), baseLinearizationError c x p⟫_ℝ ≤
        LALM.linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖p‖ ^ 2 := by
    calc
      ⟪multiplier + (params.rho : ℝ) •
            (c x + fderiv ℝ c x p), baseLinearizationError c x p⟫_ℝ ≤
          ‖multiplier + (params.rho : ℝ) •
            (c x + fderiv ℝ c x p)‖ * ‖baseLinearizationError c x p‖ :=
        real_inner_le_norm _ _
      _ ≤ (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
          (LALM.linearizationConstant h * ‖p‖ ^ 2) :=
        mul_le_mul heffectiveLinearized herror (norm_nonneg _)
          hlinearizedBoundNonneg
      _ = LALM.linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖p‖ ^ 2 := by ring
  have hstepSq : ‖p‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herrorSq :
      ‖baseLinearizationError c x p‖ ^ 2 ≤
        LALM.linearizationConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := by
    have herrorBoundNonneg :
        (0 : ℝ) ≤ LALM.linearizationConstant h * ‖p‖ ^ 2 := by positivity
    have hsquaredError :
        ‖baseLinearizationError c x p‖ ^ 2 ≤
          (LALM.linearizationConstant h * ‖p‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herrorBoundNonneg).2 herror
    calc
      ‖baseLinearizationError c x p‖ ^ 2 ≤
          (LALM.linearizationConstant h * ‖p‖ ^ 2) ^ 2 := hsquaredError
      _ = LALM.linearizationConstant h ^ 2 * ‖p‖ ^ 2 * ‖p‖ ^ 2 := by ring
      _ ≤ LALM.linearizationConstant h ^ 2 *
          (params.delta : ℝ) ^ 2 * ‖p‖ ^ 2 := by gcongr
      _ = LALM.linearizationConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2 := by ring
  have hpenaltyContribution :
      (params.rho / 2) * ‖baseLinearizationError c x p‖ ^ 2 ≤
        (params.rho / 2) * LALM.linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖p‖ ^ 2 := by
    have hrhoHalf : (0 : ℝ) ≤ params.rho / 2 := by positivity
    calc
      (params.rho / 2) * ‖baseLinearizationError c x p‖ ^ 2 ≤
          (params.rho / 2) *
            (LALM.linearizationConstant h ^ 2 * params.delta ^ 2 * ‖p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herrorSq hrhoHalf
      _ = (params.rho / 2) * LALM.linearizationConstant h ^ 2 *
          params.delta ^ 2 * ‖p‖ ^ 2 := by ring
  nlinarith

/-- Helper for Theorem 3.7: a bounded base transition satisfies the fixed-
multiplier augmented-Lagrangian model estimate. -/
theorem baseAugmentedLagrangianChange_le_modelConstant
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (step : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x (x + step) ⊆ h.region)
    (hstep : ‖step‖ ≤ params.delta)
    (heffective :
      ‖multiplier + (params.rho : ℝ) • c x‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](x + step, multiplier) -
        ℒ[f, c; params.rho](x, multiplier) ≤
      (⟪gradient f x, step⟫_ℝ +
          ⟪multiplier, fderiv ℝ c x step⟫_ℝ +
        (params.rho / 2) *
          (‖c x + fderiv ℝ c x step‖ ^ 2 - ‖c x‖ ^ 2)) +
        LALM.modelConstant h params.delta params.rho params.multiplierBound *
          ‖step‖ ^ 2 := by
  have hobjective := baseObjectiveChange_le_of_segment h x step hsegment
  have hconstraint := baseConstraintRemainderContribution_le h params x step
    multiplier hsegment hstep heffective
  rw [baseAugmentedLagrangianChange_eq_linearized h params x multiplier step,
    LALM.modelConstant_def]
  nlinarith

/-- Helper for Theorem 3.7: model minimization and transition bounds imply
one-step augmented-Lagrangian descent for a base transition. -/
theorem baseAugmentedLagrangianDescent_of_transitionBounds
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (g step : EuclideanSpace ℝ (Fin n))
    (hminimizes : IsMinOn
      (LALM.stepModelWithGradient c g params.rho params.beta x multiplier)
        Set.univ step)
    (hsegment : segment ℝ x (x + step) ⊆ h.region)
    (hstep : ‖step‖ ≤ params.delta)
    (heffective :
      ‖multiplier + (params.rho : ℝ) • c x‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](x + step, multiplier) ≤
      ℒ[f, c; params.rho](x, multiplier) -
        (params.beta / 2) * ‖step‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
  have hchange := baseAugmentedLagrangianChange_le_modelConstant h params
    x multiplier step hsegment hstep heffective
  have hlinearized := baseLinearizedAugmentedLagrangianChange_eq_of_minimizes
    c g params.rho params.beta x multiplier step hminimizes
  have hgradientIdentity : gradient f x = g - (g - gradient f x) := by module
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hquarterBeta : 0 < (params.beta : ℝ) / 4 := by positivity
  have hinverseQuarterBeta : ((params.beta : ℝ) / 4)⁻¹ = 4 / params.beta := by
    field_simp [hbeta.ne']
  have htwoProduct := two_mul_le_add_mul_sq
    (a := ‖step‖) (b := ‖g - gradient f x‖) hquarterBeta
  rw [hinverseQuarterBeta] at htwoProduct
  have hyoung :
      ‖step‖ * ‖g - gradient f x‖ ≤
        (params.beta / 8) * ‖step‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
    have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ‖step‖ * ‖g - gradient f x‖ =
          (2 * ‖step‖ * ‖g - gradient f x‖) / 2 := by ring
      _ ≤ ((params.beta / 4) * ‖step‖ ^ 2 +
          (4 / params.beta) * ‖g - gradient f x‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right htwoProduct htwoNonneg
      _ = (params.beta / 8) * ‖step‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by ring
  have hinnerNorm := real_inner_le_norm (-(g - gradient f x)) step
  simp only [inner_neg_left, norm_neg] at hinnerNorm
  have hinner :
      -⟪g - gradient f x, step⟫_ℝ ≤
        (params.beta / 8) * ‖step‖ ^ 2 +
          (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
    have hyoungCommuted :
        ‖g - gradient f x‖ * ‖step‖ ≤
          (params.beta / 8) * ‖step‖ ^ 2 +
            (2 / params.beta) * ‖g - gradient f x‖ ^ 2 := by
      simpa only [mul_comm] using hyoung
    exact hinnerNorm.trans hyoungCommuted
  have hmodelTerm :
      LALM.modelConstant h params.delta params.rho params.multiplierBound *
          ‖step‖ ^ 2 ≤ (3 * (params.beta : ℝ) / 8) * ‖step‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) * ‖fderiv ℝ c x step‖ ^ 2 := by positivity
  rw [hgradientIdentity, inner_sub_left] at hchange
  nlinarith

/-- Helper for Theorem 3.7: a minimizing base step satisfies the perturbed
normal equation after the actual multiplier update. -/
theorem basePerturbedMultiplierIdentity_of_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g rho beta x multiplier)
      Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (baseNextMultiplier c rho x multiplier p) + beta • p =
      rho • EqualityConstrained.constraintGradient c x
        (baseLinearizationError c x p) := by
  rw [baseNextMultiplier_def, baseLinearizationError_def]
  simp only [map_add, map_sub, map_smul]
  have hstationary := stepModelWithGradientOptimality c g rho beta x multiplier p hp
  simp only [map_add, map_smul] at hstationary
  linear_combination (norm := module) hstationary

/-- Helper for Theorem 3.7: subtracting adjacent base normal equations exposes
the multiplier increment and the two estimator errors. -/
theorem baseConstraintGradientMultiplierIncrement_eq_of_adjacentTransitions
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
      baseNextMultiplier c rho previousPoint previousMultiplier previousStep) :
    EqualityConstrained.constraintGradient c currentPoint
        (baseNextMultiplier c rho currentPoint currentMultiplier currentStep -
          currentMultiplier) =
      (-beta • currentStep + rho • EqualityConstrained.constraintGradient c
          currentPoint (baseLinearizationError c currentPoint currentStep)) +
        (beta • previousStep - rho • EqualityConstrained.constraintGradient c
          previousPoint (baseLinearizationError c previousPoint previousStep)) +
        (gradient f previousPoint - gradient f currentPoint) +
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier +
        ((previousGradient - gradient f previousPoint) -
          (currentGradient - gradient f currentPoint)) := by
  have hcurrent := basePerturbedMultiplierIdentity_of_minimizes c currentGradient
    rho beta currentPoint currentMultiplier currentStep hcurrentMinimizes
  have hprevious := basePerturbedMultiplierIdentity_of_minimizes c previousGradient
    rho beta previousPoint previousMultiplier previousStep hpreviousMinimizes
  rw [← hmultiplier] at hprevious
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Theorem 3.7: four scalar summands are controlled by two weighted
step squares and two estimator-error squares. -/
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
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hfourNonneg : (0 : ℝ) ≤ 4 := by norm_num
  have hfour :
      (a + d + e₀ + e₁) ^ 2 ≤
        4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by
    calc
      (a + d + e₀ + e₁) ^ 2 = ((a + d) + (e₀ + e₁)) ^ 2 := by ring
      _ ≤ 2 * ((a + d) ^ 2 + (e₀ + e₁) ^ 2) := by
        nlinarith [sq_nonneg ((a + d) - (e₀ + e₁))]
      _ ≤ 2 * (2 * (a ^ 2 + d ^ 2) + 2 * (e₀ ^ 2 + e₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add had he) htwoNonneg
      _ = 4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by ring
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
          (e₀ ^ 2 + e₁ ^ 2) := by ring
  calc
    (A * x + B * y + e₀ + e₁) ^ 2 = (a + d + e₀ + e₁) ^ 2 := by
      simp only [a, d]
    _ ≤ 4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := hfour
    _ ≤ 4 * (max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) +
        (e₀ ^ 2 + e₁ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsquares hfourNonneg

/-- Helper for Theorem 3.7: a constraint-gradient increment estimate yields the
standard squared multiplier-increment bound through LICQ. -/
theorem normBaseMultiplierIncrementSquare_le_of_constraintGradientBound
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (increment : EuclideanSpace ℝ (Fin m))
    (currentStep previousStep currentError previousError :
      EuclideanSpace ℝ (Fin n))
    (hx : x ∈ h.region)
    (hcomparison :
      ‖EqualityConstrained.constraintGradient c x increment‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho *
            ‖currentStep‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentError‖ + ‖previousError‖) :
    ‖increment‖ ^ 2 ≤
      LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2) := by
  have hlicq := h.licqLowerBound x hx increment
  have hscaled := hlicq.trans hcomparison
  have hprimalNonneg :
      0 ≤ LALM.primalConstant h params.delta params.beta params.rho := by
    rw [LALM.primalConstant_def]
    positivity
  have hcomparisonNonneg :
      0 ≤ LALM.primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.primalComparisonConstant_def]
    positivity
  have hrightNonneg :
      0 ≤ LALM.primalConstant h params.delta params.beta params.rho *
          ‖currentStep‖ +
        LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖previousStep‖ +
        ‖currentError‖ + ‖previousError‖ := by positivity
  have hleftNonneg : 0 ≤ (h.licqModulus : ℝ) * ‖increment‖ := by positivity
  have hscaledSquare :
      ((h.licqModulus : ℝ) * ‖increment‖) ^ 2 ≤
        (LALM.primalConstant h params.delta params.beta params.rho *
            ‖currentStep‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentError‖ + ‖previousError‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  have hfour := weightedFourTermSquare_le
    (LALM.primalConstant h params.delta params.beta params.rho)
    (LALM.primalComparisonConstant h params.delta params.beta params.rho
      params.multiplierBound)
    ‖currentStep‖ ‖previousStep‖ ‖currentError‖ ‖previousError‖
  have hscaledExpanded :
      (h.licqModulus : ℝ) ^ 2 * ‖increment‖ ^ 2 ≤
        4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2)) := by
    calc
      (h.licqModulus : ℝ) ^ 2 * ‖increment‖ ^ 2 =
          ((h.licqModulus : ℝ) * ‖increment‖) ^ 2 := by ring
      _ ≤ (LALM.primalConstant h params.delta params.beta params.rho *
            ‖currentStep‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentError‖ + ‖previousError‖) ^ 2 := hscaledSquare
      _ ≤ 4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2)) := hfour
  have hsigmaSq : 0 < (h.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos h.licqModulus_pos
  have hscaledCommuted :
      ‖increment‖ ^ 2 * (h.licqModulus : ℝ) ^ 2 ≤
        4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2)) := by
    simpa only [mul_comm] using hscaledExpanded
  calc
    ‖increment‖ ^ 2 ≤
        (4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2))) /
          (h.licqModulus : ℝ) ^ 2 :=
      (le_div_iff₀ hsigmaSq).2 hscaledCommuted
    _ = LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖currentError‖ ^ 2 + ‖previousError‖ ^ 2) := by
      rw [LALM.multiplierPrimalConstant_def, LALM.multiplierErrorConstant_def]
      ring

/-- Helper for Theorem 3.7: a bounded base step controls the penalty-scaled
constraint Taylor remainder. -/
theorem normScaledBaseConstraintGradientError_le
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x p : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x (x + p) ⊆ h.region)
    (hstep : ‖p‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
        (baseLinearizationError c x p)‖ ≤
      params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
        params.delta * ‖p‖ := by
  have hx : x ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hoperator := h.norm_constraintGradient_le x hx
  have herror := baseLinearizationError_norm_le_of_segment h x p hsegment
  have happlication :
      ‖EqualityConstrained.constraintGradient c x
          (baseLinearizationError c x p)‖ ≤
        h.constraintGradientBound * ‖baseLinearizationError c x p‖ :=
    (EqualityConstrained.constraintGradient c x).le_opNorm
      (baseLinearizationError c x p) |>.trans
        (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have hlinearized :
      ‖EqualityConstrained.constraintGradient c x
          (baseLinearizationError c x p)‖ ≤
        h.constraintGradientBound *
          (LALM.linearizationConstant h * ‖p‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror
        (NNReal.coe_nonneg h.constraintGradientBound))
  have hstepProduct : ‖p‖ * ‖p‖ ≤ params.delta * ‖p‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound *
        LALM.linearizationConstant h := by positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c x
        (baseLinearizationError c x p)‖ ≤
        params.rho * (h.constraintGradientBound *
          (LALM.linearizationConstant h * ‖p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlinearized hrho.le
    _ = (params.rho * h.constraintGradientBound *
        LALM.linearizationConstant h) * (‖p‖ * ‖p‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound *
        LALM.linearizationConstant h) * (params.delta * ‖p‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
        params.delta * ‖p‖ := by ring

/-- Helper for Theorem 3.7: a regular bounded model minimizer propagates the
uniform multiplier bound through the nonlinear base update. -/
theorem normBaseNextMultiplier_le_of_minimizes
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x g p : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hsegment : segment ℝ x (x + p) ⊆ h.region)
    (hstep : ‖p‖ ≤ params.delta)
    (hgradient : ‖g‖ ≤ h.gradientBound)
    (hp : IsMinOn
      (LALM.stepModelWithGradient c g params.rho params.beta x multiplier)
        Set.univ p) :
    ‖baseNextMultiplier c params.rho x multiplier p‖ ≤
      params.multiplierBound := by
  have hperturbed := basePerturbedMultiplierIdentity_of_minimizes c g
    params.rho params.beta x multiplier p hp
  have hidentity :
      EqualityConstrained.constraintGradient c x
          (baseNextMultiplier c params.rho x multiplier p) =
        -g - (params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p) := by
    linear_combination (norm := module) hperturbed
  have hperturbation := normScaledBaseConstraintGradientError_le h params x p
    hsegment hstep
  have hperturbationBound :
      ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
          (baseLinearizationError c x p)‖ ≤
        params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
          (params.delta : ℝ) ^ 2 := by
    calc
      ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
          (baseLinearizationError c x p)‖ ≤
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖p‖ := hperturbation
      _ ≤ params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
          params.delta * params.delta :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
          (params.delta : ℝ) ^ 2 := by ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hnormalBound :
      ‖EqualityConstrained.constraintGradient c x
          (baseNextMultiplier c params.rho x multiplier p)‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            (params.delta : ℝ) ^ 2 := by
    rw [hidentity]
    calc
      ‖-g - params.beta • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)‖ ≤
          ‖-g - params.beta • p‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
              (baseLinearizationError c x p)‖ := norm_add_le _ _
      _ ≤ (‖g‖ + params.beta * ‖p‖) +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (baseLinearizationError c x p)‖ := by
        gcongr
        calc
          ‖-g - (params.beta : ℝ) • p‖ ≤
              ‖-g‖ + ‖(params.beta : ℝ) • p‖ := norm_sub_le _ _
          _ = ‖g‖ + params.beta * ‖p‖ := by
            rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            (params.delta : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hstep hbeta.le,
          hperturbationBound]
  have hx : x ∈ h.region := hsegment (left_mem_segment ℝ _ _)
  have hlicq := h.licqLowerBound x hx
    (baseNextMultiplier c params.rho x multiplier p)
  have hscaled :
      (h.licqModulus : ℝ) *
          ‖baseNextMultiplier c params.rho x multiplier p‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            (params.delta : ℝ) ^ 2 :=
    hlicq.trans hnormalBound
  have hquotient :
      ‖baseNextMultiplier c params.rho x multiplier p‖ ≤
        (h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            (params.delta : ℝ) ^ 2) / h.licqModulus := by
    rw [le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)]
    simpa only [mul_comm] using hscaled
  exact hquotient.trans params.parameterBound_le

/-- Helper for Theorem 3.7: adjacent bounded base transitions control the
constraint-gradient image of the next multiplier increment. -/
theorem normBaseConstraintGradientMultiplierIncrement_le_of_adjacentTransitions
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
    (hmultiplierBound : ‖currentMultiplier‖ ≤ params.multiplierBound) :
    ‖EqualityConstrained.constraintGradient c currentPoint
        (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep -
          currentMultiplier)‖ ≤
      LALM.primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
        LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖previousStep‖ +
        ‖currentGradient - gradient f currentPoint‖ +
        ‖previousGradient - gradient f previousPoint‖ := by
  have hxCurrent : currentPoint ∈ h.region :=
    hsegmentCurrent (left_mem_segment ℝ _ _)
  have hxPrevious : previousPoint ∈ h.region :=
    hsegmentPrevious (left_mem_segment ℝ _ _)
  have herrorCurrent := normScaledBaseConstraintGradientError_le h params
    currentPoint currentStep hsegmentCurrent hstepCurrent
  have herrorPrevious := normScaledBaseConstraintGradientError_le h params
    previousPoint previousStep hsegmentPrevious hstepPrevious
  have hpointDistance : ‖currentPoint - previousPoint‖ = ‖previousStep‖ := by
    rw [hpoint, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f previousPoint - gradient f currentPoint‖ ≤
        h.gradientLipschitz * ‖previousStep‖ := by
    calc
      ‖gradient f previousPoint - gradient f currentPoint‖ =
          dist (gradient f previousPoint) (gradient f currentPoint) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz * dist previousPoint currentPoint :=
        h.lipschitzOn_gradient.dist_le_mul previousPoint hxPrevious
          currentPoint hxCurrent
      _ = h.gradientLipschitz * ‖previousStep‖ := by
        rw [dist_eq_norm, norm_sub_rev, hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint‖ ≤
        h.constraintGradientLipschitz * ‖previousStep‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint‖ =
          dist (EqualityConstrained.constraintGradient c previousPoint)
            (EqualityConstrained.constraintGradient c currentPoint) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz * dist previousPoint currentPoint :=
        h.lipschitzOn_constraintGradient.dist_le_mul previousPoint hxPrevious
          currentPoint hxCurrent
      _ = h.constraintGradientLipschitz * ‖previousStep‖ := by
        rw [dist_eq_norm, norm_sub_rev, hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound * ‖previousStep‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier‖ ≤
          ‖EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint‖ *
              ‖currentMultiplier‖ :=
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint).le_opNorm currentMultiplier
      _ ≤ (h.constraintGradientLipschitz * ‖previousStep‖) *
          params.multiplierBound := by
        have hupperNonneg :
            0 ≤ h.constraintGradientLipschitz * ‖previousStep‖ := by positivity
        exact mul_le_mul hoperatorDifference hmultiplierBound
          (norm_nonneg _) hupperNonneg
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖previousStep‖ := by ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hcurrentPair :
      ‖-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho * ‖currentStep‖ := by
    calc
      ‖-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)‖ ≤
          ‖-(params.beta : ℝ) • currentStep‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (baseLinearizationError c currentPoint currentStep)‖ := norm_add_le _ _
      _ = params.beta * ‖currentStep‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hbeta]
      _ ≤ params.beta * ‖currentStep‖ +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖currentStep‖ := add_le_add_right herrorCurrent _
      _ = LALM.primalConstant h params.delta params.beta params.rho *
          ‖currentStep‖ := by
        rw [LALM.primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho * ‖previousStep‖ := by
    calc
      ‖(params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep)‖ ≤
          ‖(params.beta : ℝ) • previousStep‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (baseLinearizationError c previousPoint previousStep)‖ := norm_sub_le _ _
      _ = params.beta * ‖previousStep‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ params.beta * ‖previousStep‖ +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖previousStep‖ := add_le_add_right herrorPrevious _
      _ = LALM.primalConstant h params.delta params.beta params.rho *
          ‖previousStep‖ := by
        rw [LALM.primalConstant_def]
        ring
  have hcore :
      ‖((-(params.beta : ℝ) • currentStep +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
              (baseLinearizationError c currentPoint currentStep)) +
          ((params.beta : ℝ) • previousStep -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
              (baseLinearizationError c previousPoint previousStep)) +
          (gradient f previousPoint - gradient f currentPoint) +
          (EqualityConstrained.constraintGradient c previousPoint -
            EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ := by
    have hfirst := norm_add_le
      (-(params.beta : ℝ) • currentStep +
        (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
          (baseLinearizationError c currentPoint currentStep))
      ((params.beta : ℝ) • previousStep -
        (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
          (baseLinearizationError c previousPoint previousStep))
    have hsecond := norm_add_le
      ((-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)) +
        ((params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep)))
      (gradient f previousPoint - gradient f currentPoint)
    have hthird := norm_add_le
      (((-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)) +
        ((params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep))) +
        (gradient f previousPoint - gradient f currentPoint))
      ((EqualityConstrained.constraintGradient c previousPoint -
        EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)
    have hcomparisonDef := LALM.primalComparisonConstant_def h params.delta
      params.beta params.rho params.multiplierBound
    rw [hcomparisonDef]
    nlinarith [hfirst, hsecond, hthird, hgradientDifference, hoperatorApplied,
      hcurrentPair, hpreviousPair]
  have hidentity := baseConstraintGradientMultiplierIncrement_eq_of_adjacentTransitions
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
          ‖previousGradient - gradient f previousPoint‖ := by ring
  calc
    ‖((-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)) +
        ((params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep)) +
        (gradient f previousPoint - gradient f currentPoint) +
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier) +
        ((previousGradient - gradient f previousPoint) -
          (currentGradient - gradient f currentPoint))‖ ≤
        ‖((-(params.beta : ℝ) • currentStep +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c currentPoint
            (baseLinearizationError c currentPoint currentStep)) +
        ((params.beta : ℝ) • previousStep -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c previousPoint
            (baseLinearizationError c previousPoint previousStep)) +
        (gradient f previousPoint - gradient f currentPoint) +
        (EqualityConstrained.constraintGradient c previousPoint -
          EqualityConstrained.constraintGradient c currentPoint) currentMultiplier)‖ +
          ‖(previousGradient - gradient f previousPoint) -
            (currentGradient - gradient f currentPoint)‖ := norm_add_le _ _
    _ ≤ LALM.primalConstant h params.delta params.beta params.rho * ‖currentStep‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖previousStep‖ +
          ‖currentGradient - gradient f currentPoint‖ +
          ‖previousGradient - gradient f previousPoint‖ := by
      simpa only [add_assoc] using add_le_add hcore herrorDifference

/-- Helper for Theorem 3.7: the base multiplier update changes the augmented
Lagrangian by the squared multiplier increment divided by the penalty. -/
theorem baseAugmentedLagrangian_nextMultiplier_eq
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    ℒ[f, c; params.rho](x + p,
        baseNextMultiplier c params.rho x multiplier p) =
      ℒ[f, c; params.rho](x + p, multiplier) +
        ‖baseNextMultiplier c params.rho x multiplier p - multiplier‖ ^ 2 /
          params.rho := by
  have hupdate :
      baseNextMultiplier c params.rho x multiplier p =
        multiplier + (params.rho : ℝ) • c (x + p) := by
    rw [baseNextMultiplier_def]
  rw [augmentedLagrangian_def, augmentedLagrangian_def, hupdate,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  field_simp [params.spec.1.2.2.1.ne']
  ring

/-- Helper for Theorem 3.7: the parameter certificate bounds the scaled
multiplier-primal coefficient by one eighth of the proximal coefficient. -/
theorem multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  have hscaled :
      8 * LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Theorem 3.7: adjacent bounded base transitions satisfy the
finite stopped Lyapunov descent inequality. -/
theorem baseFiniteLyapunovDescent_of_adjacentTransitions
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
    (hpreviousMultiplierBound : ‖previousMultiplier‖ ≤ params.multiplierBound)
    (hcurrentMultiplierBound : ‖currentMultiplier‖ ≤ params.multiplierBound) :
    ℒ[f, c; params.rho](currentPoint + currentStep,
        baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep) +
        (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖currentStep‖ ^ 2 ≤
      ℒ[f, c; params.rho](currentPoint, currentMultiplier) +
        (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖previousStep‖ ^ 2 -
        (params.beta / 4) * ‖currentStep‖ ^ 2 +
        LALM.StochasticRun.lyapunovErrorConstant h params *
          (‖currentGradient - gradient f currentPoint‖ ^ 2 +
            ‖previousGradient - gradient f previousPoint‖ ^ 2) := by
  have hupdate :
      (params.rho : ℝ) • c currentPoint = currentMultiplier - previousMultiplier := by
    rw [hmultiplier, baseNextMultiplier_def, hpoint]
    module
  have heffective :
      ‖currentMultiplier + (params.rho : ℝ) • c currentPoint‖ ≤
        3 * (params.multiplierBound : ℝ) := by
    rw [hupdate]
    have hadd := norm_add_le currentMultiplier (currentMultiplier - previousMultiplier)
    have hdiff : ‖currentMultiplier - previousMultiplier‖ ≤
        ‖currentMultiplier‖ + ‖previousMultiplier‖ := norm_sub_le _ _
    nlinarith [hadd, hdiff]
  have hlagrangian := baseAugmentedLagrangianDescent_of_transitionBounds h params
    currentPoint currentMultiplier currentGradient currentStep hcurrentMinimizes
    hsegmentCurrent hstepCurrent heffective
  have hcomparison := normBaseConstraintGradientMultiplierIncrement_le_of_adjacentTransitions
    (f := f) (c := c) h params previousPoint currentPoint previousMultiplier
    currentMultiplier previousGradient currentGradient previousStep currentStep
    hpreviousMinimizes hcurrentMinimizes hpoint hmultiplier hsegmentPrevious
    hsegmentCurrent hstepPrevious hstepCurrent hcurrentMultiplierBound
  have hsq := normBaseMultiplierIncrementSquare_le_of_constraintGradientBound
    (f := f) (c := c) h params currentPoint
    (baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep -
      currentMultiplier)
    currentStep previousStep (currentGradient - gradient f currentPoint)
    (previousGradient - gradient f previousPoint)
    (hsegmentCurrent (left_mem_segment ℝ _ _)) hcomparison
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierDivided := (div_le_div_iff_of_pos_right hrho).2 hsq
  have hmultiplierDiv :
      ‖baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep -
          currentMultiplier‖ ^ 2 / params.rho ≤
        (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
        (LALM.multiplierErrorConstant h / params.rho) *
          (‖currentGradient - gradient f currentPoint‖ ^ 2 +
            ‖previousGradient - gradient f previousPoint‖ ^ 2) := by
    calc
      ‖baseNextMultiplier c params.rho currentPoint currentMultiplier currentStep -
          currentMultiplier‖ ^ 2 / params.rho ≤
          (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
                (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
            LALM.multiplierErrorConstant h *
              (‖currentGradient - gradient f currentPoint‖ ^ 2 +
                ‖previousGradient - gradient f previousPoint‖ ^ 2)) /
            params.rho := hmultiplierDivided
      _ = (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖currentStep‖ ^ 2 + ‖previousStep‖ ^ 2) +
          (LALM.multiplierErrorConstant h / params.rho) *
            (‖currentGradient - gradient f currentPoint‖ ^ 2 +
              ‖previousGradient - gradient f previousPoint‖ ^ 2) := by ring
  have hcoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have htwiceCoefficient :
      2 * (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.rho) ≤ params.beta / 4 := by
    linarith
  have hcurrentCoefficient :
      2 * (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖currentStep‖ ^ 2 ≤
        (params.beta / 4) * ‖currentStep‖ ^ 2 :=
    mul_le_mul_of_nonneg_right htwiceCoefficient (sq_nonneg _)
  have hpreviousErrorNonneg :
      (0 : ℝ) ≤ (2 / params.beta) *
        ‖previousGradient - gradient f previousPoint‖ ^ 2 := by positivity
  rw [baseAugmentedLagrangian_nextMultiplier_eq h params currentPoint
      currentMultiplier currentStep,
    LALM.StochasticRun.lyapunovErrorConstant_def]
  have hsum := add_le_add hlagrangian hmultiplierDiv
  nlinarith [hsum, hcurrentCoefficient, hpreviousErrorNonneg]

end LALM.FiniteStopped

end
