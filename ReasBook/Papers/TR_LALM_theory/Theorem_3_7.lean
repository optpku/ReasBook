/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Theorem_3_6.Schedule
public import TR_LALM_theory.Theorem_3_7.Localization
public import TR_LALM_theory.Theorem_3_7.ConditionalOutput
public import TR_LALM_theory.Theorem_3_7.StoppedProcess
import TR_LALM_theory.Theorem_3_6
import TR_LALM_theory.Lemma_3_4
import Mathlib.Probability.Independence.Integration

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace LALM NNReal

namespace LALM.StochasticRun

universe u v w x

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}
variable {confidence : ℝ}

-- Route correction: the unrestricted Lemmas 3.4 and 3.5 require admissibility
-- on every sample path.  Localization supplies the required bounds only on the
-- chosen surviving path, so the deterministic core is exposed with explicit
-- segment, step, and multiplier hypotheses below.

/-- Helper for Theorem 3.7: the derivative of the explicit-gradient model is
represented by its canonical first-order vector. -/
private lemma hasFDerivAtExplicitGradientModel
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (stepModelWithGradient c g rho beta x multiplier)
      (innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p)) p := by
  -- Differentiate the affine constraint model once and reuse it in every term.
  have haffine : HasFDerivAt
      (fun q ↦ c x + fderiv ℝ c x q) (fderiv ℝ c x) p := by
    fun_prop
  have hobjective : HasFDerivAt
      (fun q ↦ ⟪g, q⟫_ℝ) (innerSL ℝ g) p := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ g).hasFDerivAt
  have hmultiplier : HasFDerivAt
      (fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ)
      (innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) p := by
    simpa only [Function.comp_def, innerSL_apply_apply,
      EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        (innerSL ℝ multiplier).hasFDerivAt.comp p haffine
  have hpenalty : HasFDerivAt
      (fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((rho / 2) • 2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))) p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        haffine.norm_sq.const_mul (rho / 2)
  have hproximal : HasFDerivAt (fun q ↦ (beta / 2) * ‖q‖ ^ 2)
      ((beta / 2) • 2 • innerSL ℝ p) p := by
    simpa only [id_eq, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id p).norm_sq.const_mul (beta / 2)
  let modelDerivative : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((innerSL ℝ g +
        innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
      ((rho / 2) • (2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))))) + ((beta / 2) • (2 • innerSL ℝ p))
  have hsum : HasFDerivAt
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2) modelDerivative p := by
    simpa only [modelDerivative] using
      ((hobjective.add hmultiplier).add hpenalty).add hproximal
  have hderivativeEq : modelDerivative =
      innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p) := by
    ext v
    simp only [map_add, map_smul, innerSL_apply_apply, add_apply, smul_apply,
      EqualityConstrained.constraintGradient_def, modelDerivative]
    ring
  have hfunctions : stepModelWithGradient c g rho beta x multiplier =ᶠ[nhds p]
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (rho / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (beta / 2) * ‖q‖ ^ 2) := by
    filter_upwards with q
    exact stepModelWithGradient_def c g rho beta x multiplier q
  exact (hsum.congr_of_eventuallyEq hfunctions).congr_fderiv hderivativeEq

/-- Helper for Theorem 3.7: a minimizer of the explicit-gradient step model
satisfies its first-order normal equation. -/
private lemma explicitGradientModelOptimality
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (stepModelWithGradient c g rho beta x multiplier) Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p = 0 := by
  -- Fermat's rule annihilates the explicit derivative computed above.
  have hderiv : innerSL ℝ (g + EqualityConstrained.constraintGradient c x
      (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p) = 0 :=
    (hp.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
      (hasFDerivAtExplicitGradientModel c g rho beta x multiplier p)
  have hnormSq :
      ‖g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p‖ ^ 2 = 0 := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq, zero_apply] using
      congrArg (fun A ↦ A (g + EqualityConstrained.constraintGradient c x
        (multiplier + rho • (c x + fderiv ℝ c x p)) + beta • p)) hderiv
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- Helper for Theorem 3.7: the constraint linearization remainder along one
stochastic sample path. -/
private noncomputable def pathLinearizationError
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin m) :=
  c (run.point (k + 1) ω) - c (run.point k ω) -
    fderiv ℝ c (run.point k ω) (run.step k ω)

/-- Helper for Theorem 3.7: an admissible path segment has quadratically small
constraint linearization remainder. -/
private lemma normPathLinearizationError_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region) :
    ‖pathLinearizationError run k ω‖ ≤
      LALM.linearizationConstant h * ‖run.step k ω‖ ^ 2 := by
  -- Apply the segmentwise Taylor remainder estimate to the point update.
  have hremainder := norm_sub_sub_fderiv_le c h.constraintGradientLipschitz
    h.region (run.point k ω) (run.point (k + 1) ω)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hsegment
  simpa only [pathLinearizationError, run.point_succ, add_sub_cancel_left,
    LALM.linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using
    hremainder

/-- Helper for Theorem 3.7: stochastic model optimality and the multiplier
update give the perturbed normal equation on a fixed path. -/
private lemma pathPerturbedMultiplierIdentity
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.gradientEstimate k ω +
        EqualityConstrained.constraintGradient c (run.point k ω)
          (run.multiplier (k + 1) ω) +
        (params.beta : ℝ) • run.step k ω =
      (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k ω)
        (pathLinearizationError run k ω) := by
  -- Rewrite the first-order equation using the exact multiplier update.
  have hoptimal := explicitGradientModelOptimality c
    (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
    params.rho params.beta (run.point k ω) (run.multiplier k ω)
    (run.step k ω) (run.minimizes_step k ω)
  rw [← run.gradientEstimate_apply] at hoptimal
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) :=
    run.multiplier_succ k ω
  have hdecomposition :
      run.multiplier (k + 1) ω =
        run.multiplier k ω + (params.rho : ℝ) •
          (c (run.point k ω) + fderiv ℝ c (run.point k ω) (run.step k ω)) +
        (params.rho : ℝ) • pathLinearizationError run k ω := by
    rw [hupdate, pathLinearizationError]
    module
  rw [hdecomposition, map_add, map_smul]
  linear_combination (norm := module) hoptimal

/-- Helper for Theorem 3.7: a bounded step controls the penalty-scaled image
of its pathwise linearization remainder. -/
private lemma normScaledPathLinearizationError_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (j : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point j ω) (run.point (j + 1) ω) ⊆ h.region)
    (hstep : ‖run.step j ω‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point j ω)
        (pathLinearizationError run j ω)‖ ≤
      params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
        params.delta * ‖run.step j ω‖ := by
  -- Bound the operator, insert the quadratic Taylor estimate, and use the
  -- prescribed step radius to linearize one factor of the step norm.
  have hx : run.point j ω ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hoperator := h.norm_constraintGradient_le (run.point j ω) hx
  have herror := normPathLinearizationError_le run j ω hsegment
  have happlication :
      ‖EqualityConstrained.constraintGradient c (run.point j ω)
          (pathLinearizationError run j ω)‖ ≤
        h.constraintGradientBound * ‖pathLinearizationError run j ω‖ :=
    (EqualityConstrained.constraintGradient c (run.point j ω)).le_opNorm
      (pathLinearizationError run j ω) |>.trans
        (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have hlinearized :
      ‖EqualityConstrained.constraintGradient c (run.point j ω)
          (pathLinearizationError run j ω)‖ ≤
        h.constraintGradientBound *
          (LALM.linearizationConstant h * ‖run.step j ω‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror
        (NNReal.coe_nonneg h.constraintGradientBound))
  have hstepProduct :
      ‖run.step j ω‖ * ‖run.step j ω‖ ≤
        params.delta * ‖run.step j ω‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound *
        LALM.linearizationConstant h := by
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c (run.point j ω)
        (pathLinearizationError run j ω)‖ ≤
        params.rho * (h.constraintGradientBound *
          (LALM.linearizationConstant h * ‖run.step j ω‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlinearized hrho.le
    _ = (params.rho * h.constraintGradientBound *
        LALM.linearizationConstant h) *
          (‖run.step j ω‖ * ‖run.step j ω‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound *
        LALM.linearizationConstant h) *
          (params.delta * ‖run.step j ω‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
        params.delta * ‖run.step j ω‖ := by ring

/-- Helper for Theorem 3.7: subtracting consecutive perturbed normal equations
expresses the multiplier increment through two steps and two estimator errors. -/
private lemma pathConstraintGradientMultiplierIncrement
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω) :
    EqualityConstrained.constraintGradient c (run.point k ω)
        (run.multiplier (k + 1) ω - run.multiplier k ω) =
      (-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)) +
        ((params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω)
            (pathLinearizationError run (k - 1) ω)) +
        (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω) +
        (run.gradientError (k - 1) ω - run.gradientError k ω) := by
  -- Normalize the predecessor index, expand the two estimator errors, and
  -- subtract the consecutive first-order identities.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hcurrent := pathPerturbedMultiplierIdentity run k ω
  have hprevious := pathPerturbedMultiplierIdentity run (k - 1) ω
  rw [hpred] at hprevious
  rw [run.gradientError_apply, run.gradientError_apply]
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Theorem 3.7: explicit segment, step, and multiplier bounds
control the constraint-gradient image of one multiplier increment. -/
private lemma normPathConstraintGradientMultiplierIncrement_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω)
    (hsegmentCurrent :
      segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hsegmentPrevious :
      segment ℝ (run.point (k - 1) ω) (run.point k ω) ⊆ h.region)
    (hstepCurrent : ‖run.step k ω‖ ≤ params.delta)
    (hstepPrevious : ‖run.step (k - 1) ω‖ ≤ params.delta)
    (hmultiplier : ‖run.multiplier k ω‖ ≤ params.multiplierBound) :
    ‖EqualityConstrained.constraintGradient c (run.point k ω)
        (run.multiplier (k + 1) ω - run.multiplier k ω)‖ ≤
      LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ +
        LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1) ω‖ +
        ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖ := by
  -- Record the two regular endpoints and their Taylor remainder bounds.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hxCurrent : run.point k ω ∈ h.region :=
    hsegmentCurrent (left_mem_segment ℝ _ _)
  have hxPrevious : run.point (k - 1) ω ∈ h.region :=
    hsegmentPrevious (left_mem_segment ℝ _ _)
  have hsegmentPrevious' :
      segment ℝ (run.point (k - 1) ω) (run.point (k - 1 + 1) ω) ⊆
        h.region := by
    simpa only [hpred] using hsegmentPrevious
  have herrorCurrent := normScaledPathLinearizationError_le run k ω
    hsegmentCurrent hstepCurrent
  have herrorPrevious := normScaledPathLinearizationError_le run (k - 1) ω
    hsegmentPrevious' hstepPrevious
  have hpointDistance :
      dist (run.point (k - 1) ω) (run.point k ω) =
        ‖run.step (k - 1) ω‖ := by
    calc
      dist (run.point (k - 1) ω) (run.point k ω) =
          dist (run.point (k - 1) ω) (run.point (k - 1 + 1) ω) := by
        rw [hpred]
      _ = ‖run.step (k - 1) ω‖ := by
        rw [run.point_succ, dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)‖ ≤
        h.gradientLipschitz * ‖run.step (k - 1) ω‖ := by
    calc
      ‖gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)‖ =
          dist (gradient f (run.point (k - 1) ω))
            (gradient f (run.point k ω)) := (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz *
          dist (run.point (k - 1) ω) (run.point k ω) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k - 1) ω) hxPrevious (run.point k ω) hxCurrent
      _ = h.gradientLipschitz * ‖run.step (k - 1) ω‖ := by
        rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ ≤
        h.constraintGradientLipschitz * ‖run.step (k - 1) ω‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k - 1) ω))
            (EqualityConstrained.constraintGradient c (run.point k ω)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k - 1) ω) (run.point k ω) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k - 1) ω) hxPrevious (run.point k ω) hxCurrent
      _ = h.constraintGradientLipschitz * ‖run.step (k - 1) ω‖ := by
        rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1) ω‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω)‖ *
              ‖run.multiplier k ω‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)).le_opNorm
            (run.multiplier k ω)
      _ ≤ (h.constraintGradientLipschitz * ‖run.step (k - 1) ω‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step (k - 1) ω‖ := by ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  -- Combine each proximal/Taylor pair into the canonical primal coefficient.
  have hcurrentPair :
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ := by
    calc
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)‖ :=
        norm_add_le _ _
      _ = params.beta * ‖run.step k ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hbeta]
      _ ≤ params.beta * ‖run.step k ω‖ +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖run.step k ω‖ :=
        add_le_add_right herrorCurrent _
      _ = LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ := by
        rw [LALM.primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω)
            (pathLinearizationError run (k - 1) ω)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step (k - 1) ω‖ := by
    calc
      ‖(params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω)
            (pathLinearizationError run (k - 1) ω)‖ ≤
          ‖(params.beta : ℝ) • run.step (k - 1) ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω)
              (pathLinearizationError run (k - 1) ω)‖ :=
        norm_sub_le _ _
      _ = params.beta * ‖run.step (k - 1) ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω)
            (pathLinearizationError run (k - 1) ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ params.beta * ‖run.step (k - 1) ω‖ +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖run.step (k - 1) ω‖ :=
        add_le_add_right herrorPrevious _
      _ = LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step (k - 1) ω‖ := by
        rw [LALM.primalConstant_def]
        ring
  have hdeterministicCore :
      ‖(-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)) +
        ((params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω)
            (pathLinearizationError run (k - 1) ω)) +
        (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho *
            ‖run.step k ω‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖ := by
    calc
      ‖(-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)) +
          ((params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω)
              (pathLinearizationError run (k - 1) ω)) +
          (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)‖ +
          ‖(params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω)
              (pathLinearizationError run (k - 1) ω)‖ +
          ‖gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)‖ +
          ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω)‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω))
          ((params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω)
              (pathLinearizationError run (k - 1) ω))
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • run.step k ω +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k ω) (pathLinearizationError run k ω)) +
            ((params.beta : ℝ) • run.step (k - 1) ω -
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point (k - 1) ω)
                (pathLinearizationError run (k - 1) ω)))
          (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω))
        have hthird := norm_add_le
          (((-(params.beta : ℝ) • run.step k ω +
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point k ω) (pathLinearizationError run k ω)) +
              ((params.beta : ℝ) • run.step (k - 1) ω -
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point (k - 1) ω)
                  (pathLinearizationError run (k - 1) ω))) +
            (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)))
          ((EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω))
        linarith
      _ ≤ LALM.primalConstant h params.delta params.beta params.rho *
            ‖run.step k ω‖ +
          LALM.primalConstant h params.delta params.beta params.rho *
            ‖run.step (k - 1) ω‖ +
          h.gradientLipschitz * ‖run.step (k - 1) ω‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            ‖run.step (k - 1) ω‖ :=
        add_le_add (add_le_add (add_le_add hcurrentPair hpreviousPair)
          hgradientDifference) hoperatorApplied
      _ = LALM.primalConstant h params.delta params.beta params.rho *
            ‖run.step k ω‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖ := by
        rw [LALM.primalComparisonConstant_def]
        ring
  -- Add the estimator-error difference after controlling the deterministic core.
  rw [pathConstraintGradientMultiplierIncrement run k hk_pos ω]
  calc
    ‖((-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)) +
        ((params.beta : ℝ) • run.step (k - 1) ω -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) ω)
            (pathLinearizationError run (k - 1) ω)) +
        (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier k ω)) +
        (run.gradientError (k - 1) ω - run.gradientError k ω)‖ ≤
        ‖(-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)) +
          ((params.beta : ℝ) • run.step (k - 1) ω -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) ω)
              (pathLinearizationError run (k - 1) ω)) +
          (gradient f (run.point (k - 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier k ω)‖ +
        ‖run.gradientError (k - 1) ω - run.gradientError k ω‖ :=
      norm_add_le _ _
    _ ≤ (LALM.primalConstant h params.delta params.beta params.rho *
            ‖run.step k ω‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖) +
        (‖run.gradientError (k - 1) ω‖ + ‖run.gradientError k ω‖) :=
      add_le_add hdeterministicCore (norm_sub_le _ _)
    _ = LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ +
        LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1) ω‖ +
        ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖ := by ring

/-- Helper for Theorem 3.7: fixed-path segment, step, and multiplier bounds
control the squared multiplier increment. -/
private lemma normPathMultiplierIncrementSq_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω)
    (hsegmentCurrent :
      segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hsegmentPrevious :
      segment ℝ (run.point (k - 1) ω) (run.point k ω) ⊆ h.region)
    (hstepCurrent : ‖run.step k ω‖ ≤ params.delta)
    (hstepPrevious : ‖run.step (k - 1) ω‖ ≤ params.delta)
    (hmultiplier : ‖run.multiplier k ω‖ ≤ params.multiplierBound) :
    ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
      LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- LICQ transfers the preceding constraint-gradient estimate to the
  -- multiplier increment itself.
  have hx : run.point k ω ∈ h.region :=
    hsegmentCurrent (left_mem_segment ℝ _ _)
  have hcomparison := normPathConstraintGradientMultiplierIncrement_le run k
    hk_pos ω hsegmentCurrent hsegmentPrevious hstepCurrent hstepPrevious
    hmultiplier
  have hlicq := h.licqLowerBound (run.point k ω) hx
    (run.multiplier (k + 1) ω - run.multiplier k ω)
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
          ‖run.step k ω‖ +
        LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step (k - 1) ω‖ +
        ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖ := by
    positivity
  have hleftNonneg :
      0 ≤ (h.licqModulus : ℝ) *
        ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ := by
    positivity
  have hscaledSquare :
      ((h.licqModulus : ℝ) *
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖) ^ 2 ≤
        (LALM.primalConstant h params.delta params.beta params.rho *
            ‖run.step k ω‖ +
          LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step (k - 1) ω‖ +
          ‖run.gradientError k ω‖ + ‖run.gradientError (k - 1) ω‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  -- A four-term square estimate separates step and estimator contributions.
  let a := LALM.primalConstant h params.delta params.beta params.rho *
    ‖run.step k ω‖
  let d := LALM.primalComparisonConstant h params.delta params.beta params.rho
    params.multiplierBound * ‖run.step (k - 1) ω‖
  let e₀ := ‖run.gradientError k ω‖
  let e₁ := ‖run.gradientError (k - 1) ω‖
  have had : (a + d) ^ 2 ≤ 2 * (a ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - d)]
  have he : (e₀ + e₁) ^ 2 ≤ 2 * (e₀ ^ 2 + e₁ ^ 2) := by
    nlinarith [sq_nonneg (e₀ - e₁)]
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hfourNonneg : (0 : ℝ) ≤ 4 := by norm_num
  have hfour :
      (a + d + e₀ + e₁) ^ 2 ≤
        4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by
    calc
      (a + d + e₀ + e₁) ^ 2 = ((a + d) + (e₀ + e₁)) ^ 2 := by ring
      _ ≤ 2 * ((a + d) ^ 2 + (e₀ + e₁) ^ 2) := by
        nlinarith [sq_nonneg ((a + d) - (e₀ + e₁))]
      _ ≤ 2 * (2 * (a ^ 2 + d ^ 2) + 2 * (e₀ ^ 2 + e₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add had he) htwo
      _ = 4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by ring
  have hprimalMax :
      LALM.primalConstant h params.delta params.beta params.rho ^ 2 ≤
        max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) := le_max_left _ _
  have hcomparisonMax :
      LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 ≤
        max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) := le_max_right _ _
  have haSquare :
      a ^ 2 ≤
        max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) * ‖run.step k ω‖ ^ 2 := by
    dsimp only [a]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hprimalMax (sq_nonneg _)
  have hdSquare :
      d ^ 2 ≤
        max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2) * ‖run.step (k - 1) ω‖ ^ 2 := by
    dsimp only [d]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hcomparisonMax (sq_nonneg _)
  have hsquares :
      a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2 ≤
        max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
            (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    dsimp only [e₀, e₁]
    calc
      a ^ 2 + d ^ 2 + ‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2 ≤
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) * ‖run.step k ω‖ ^ 2 +
            max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) * ‖run.step (k - 1) ω‖ ^ 2) +
            ‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2 := by
        exact add_le_add
          (add_le_add (add_le_add haSquare hdSquare) (le_refl _)) (le_refl _)
      _ = max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
            (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  have hscaledExpanded :
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
        4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    calc
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 =
          ((h.licqModulus : ℝ) *
            ‖run.multiplier (k + 1) ω - run.multiplier k ω‖) ^ 2 := by ring
      _ ≤ (a + d + e₀ + e₁) ^ 2 := by
        simpa only [a, d, e₀, e₁] using hscaledSquare
      _ ≤ 4 * (a ^ 2 + d ^ 2 + e₀ ^ 2 + e₁ ^ 2) := hfour
      _ ≤ 4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsquares hfourNonneg
  -- Divide by the positive LICQ modulus and identify the named constants.
  have hsigmaSq : 0 < (h.licqModulus : ℝ) ^ 2 :=
    sq_pos_of_pos h.licqModulus_pos
  have hscaledCommuted :
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 *
          (h.licqModulus : ℝ) ^ 2 ≤
        4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    simpa only [mul_comm] using hscaledExpanded
  calc
    ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 ≤
        (4 *
          (max (LALM.primalConstant h params.delta params.beta params.rho ^ 2)
              (LALM.primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2))) /
          (h.licqModulus : ℝ) ^ 2 :=
      (le_div_iff₀ hsigmaSq).2 hscaledCommuted
    _ = LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
      rw [LALM.multiplierPrimalConstant_def, LALM.multiplierErrorConstant_def]
      ring

/-- Helper for Theorem 3.7: explicit segment, step, and multiplier bounds
control stationarity at the next point of a fixed stochastic path. -/
private lemma normPathStationaritySucc_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment :
      segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta)
    (hmultiplier : ‖run.multiplier (k + 1) ω‖ ≤ params.multiplierBound) :
    ‖KKT.stationarity f c (run.point (k + 1) ω)
        (run.multiplier (k + 1) ω)‖ ≤
      LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ +
        ‖run.gradientError k ω‖ := by
  -- Rewrite stationarity through the pathwise perturbed normal equation.
  have hxCurrent : run.point k ω ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hxNext : run.point (k + 1) ω ∈ h.region :=
    hsegment (right_mem_segment ℝ _ _)
  have herror := normScaledPathLinearizationError_le run k ω hsegment hstep
  have hstationarityIdentity :
      KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω) =
        ((-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)) +
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)) - run.gradientError k ω := by
    rw [KKT.stationarity_def, run.gradientError_apply]
    simp only [sub_apply]
    linear_combination (norm := module) pathPerturbedMultiplierIdentity run k ω
  -- Lipschitz continuity converts both point differences to the current step.
  have hpointDistance :
      dist (run.point (k + 1) ω) (run.point k ω) = ‖run.step k ω‖ := by
    rw [run.point_succ, dist_eq_norm, add_sub_cancel_left]
  have hgradientDifference :
      ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ ≤
        h.gradientLipschitz * ‖run.step k ω‖ := by
    calc
      ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ =
          dist (gradient f (run.point (k + 1) ω))
            (gradient f (run.point k ω)) := (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz *
          dist (run.point (k + 1) ω) (run.point k ω) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k + 1) ω) hxNext (run.point k ω) hxCurrent
      _ = h.gradientLipschitz * ‖run.step k ω‖ := by rw [hpointDistance]
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ ≤
        h.constraintGradientLipschitz * ‖run.step k ω‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k + 1) ω))
            (EqualityConstrained.constraintGradient c (run.point k ω)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k + 1) ω) (run.point k ω) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k + 1) ω) hxNext (run.point k ω) hxCurrent
      _ = h.constraintGradientLipschitz * ‖run.step k ω‖ := by
        rw [hpointDistance]
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step k ω‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω)‖ *
              ‖run.multiplier (k + 1) ω‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)).le_opNorm
            (run.multiplier (k + 1) ω)
      _ ≤ (h.constraintGradientLipschitz * ‖run.step k ω‖) *
          params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          ‖run.step k ω‖ := by ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hproximalError :
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)‖ ≤
        LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ := by
    calc
      ‖-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)‖ :=
        norm_add_le _ _
      _ = params.beta * ‖run.step k ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hbeta]
      _ ≤ params.beta * ‖run.step k ω‖ +
          params.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            params.delta * ‖run.step k ω‖ := add_le_add_right herror _
      _ = LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ := by
        rw [LALM.primalConstant_def]
        ring
  -- Collect the deterministic terms before adding the estimator error once.
  have hdeterministic :
      ‖(-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
        LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ := by
    calc
      ‖(-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
          ‖-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)‖ +
          ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ +
          ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω))
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω))
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • run.step k ω +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k ω) (pathLinearizationError run k ω)) +
            (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)))
          ((EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω))
        linarith
      _ ≤ LALM.primalConstant h params.delta params.beta params.rho *
          ‖run.step k ω‖ + h.gradientLipschitz * ‖run.step k ω‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            ‖run.step k ω‖ :=
        add_le_add (add_le_add hproximalError hgradientDifference) hoperatorApplied
      _ = LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ := by
        rw [LALM.primalComparisonConstant_def]
        ring
  rw [hstationarityIdentity]
  calc
    ‖((-(params.beta : ℝ) • run.step k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (pathLinearizationError run k ω)) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)) - run.gradientError k ω‖ ≤
        ‖(-(params.beta : ℝ) • run.step k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (pathLinearizationError run k ω)) +
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)‖ + ‖run.gradientError k ω‖ :=
      norm_sub_le _ _
    _ ≤ LALM.primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.step k ω‖ + ‖run.gradientError k ω‖ :=
      add_le_add hdeterministic (le_refl _)

/-- Helper for Theorem 3.7: the multiplier update identifies fixed-path
feasibility with the squared multiplier increment divided by `params.rho ^ 2`. -/
private lemma pathConstraintNormSq_eq_multiplierIncrementNormSqDiv
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ‖c (run.point (k + 1) ω)‖ ^ 2 =
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 /
        (params.rho : ℝ) ^ 2 := by
  -- Cancel the positive penalty scalar in the exact multiplier update.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) :=
    run.multiplier_succ k ω
  rw [hupdate, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
  field_simp [hrho.ne']

/-- Helper for Theorem 3.7: fixed-path localization bounds imply the squared
KKT residual comparison used at one positive iteration. -/
private lemma residualSq_le_of_pathBounds
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω)
    (hsegmentCurrent :
      segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hsegmentPrevious :
      segment ℝ (run.point (k - 1) ω) (run.point k ω) ⊆ h.region)
    (hstepCurrent : ‖run.step k ω‖ ≤ params.delta)
    (hstepPrevious : ‖run.step (k - 1) ω‖ ≤ params.delta)
    (hmultiplierCurrent : ‖run.multiplier k ω‖ ≤ params.multiplierBound)
    (hmultiplierNext : ‖run.multiplier (k + 1) ω‖ ≤ params.multiplierBound) :
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 ≤
      LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- Square the fixed-path stationarity estimate and add harmless adjacent terms.
  have hstationarity := normPathStationaritySucc_le run k ω hsegmentCurrent
    hstepCurrent hmultiplierNext
  have hcomparisonNonneg :
      0 ≤ LALM.primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.primalComparisonConstant_def, LALM.primalConstant_def]
    positivity
  have hstationarityRightNonneg :
      0 ≤ LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.step k ω‖ +
        ‖run.gradientError k ω‖ := by
    positivity
  have hstationaritySquared :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        (LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.step k ω‖ +
          ‖run.gradientError k ω‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hstationarityRightNonneg).2 hstationarity
  have hstationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 * ‖run.step k ω‖ ^ 2 +
          2 * ‖run.gradientError k ω‖ ^ 2 := by
    calc
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step k ω‖ +
            ‖run.gradientError k ω‖) ^ 2 := hstationaritySquared
      _ ≤ 2 *
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step k ω‖) ^ 2 +
            2 * ‖run.gradientError k ω‖ ^ 2 := by
        nlinarith [sq_nonneg
          (LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.step k ω‖ -
            ‖run.gradientError k ω‖)]
      _ = 2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 * ‖run.step k ω‖ ^ 2 +
        2 * ‖run.gradientError k ω‖ ^ 2 := by ring
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hstationarityExpanded :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        2 * (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
          2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 * ‖run.step k ω‖ ^ 2 +
            2 * ‖run.gradientError k ω‖ ^ 2 := hstationaritySquare
      _ ≤ 2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          2 * (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
        have hstepCoefficientNonneg :
            0 ≤ 2 * LALM.primalComparisonConstant h params.delta params.beta
              params.rho params.multiplierBound ^ 2 :=
          mul_nonneg htwo (sq_nonneg _)
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) hstepCoefficientNonneg)
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) htwo)
  -- Transport the fixed-path multiplier-increment estimate to feasibility.
  have hmultiplier := normPathMultiplierIncrementSq_le run k hk_pos ω
    hsegmentCurrent hsegmentPrevious hstepCurrent hstepPrevious
    hmultiplierCurrent
  have hfeasibility :
      ‖c (run.point (k + 1) ω)‖ ^ 2 ≤
        LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖c (run.point (k + 1) ω)‖ ^ 2 =
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 /
            (params.rho : ℝ) ^ 2 :=
        pathConstraintNormSq_eq_multiplierIncrementNormSqDiv run k ω
      _ ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          LALM.multiplierErrorConstant h *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2)) /
            (params.rho : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmultiplier (sq_nonneg _)
      _ = LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2 *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  -- The defining maximum dominates the step and error coefficients separately.
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
      0 ≤ ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 := by positivity
  have herrorSumNonneg :
      0 ≤ ‖run.gradientError k ω‖ ^ 2 +
        ‖run.gradientError (k - 1) ω‖ ^ 2 := by positivity
  calc
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 =
        ‖KKT.stationarity f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω)‖ ^ 2 +
          ‖c (run.point (k + 1) ω)‖ ^ 2 := by
      rw [KKT.residual_def,
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ (2 * LALM.primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 +
            LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
      calc
        ‖KKT.stationarity f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω)‖ ^ 2 +
            ‖c (run.point (k + 1) ω)‖ ^ 2 ≤
            (2 * LALM.primalComparisonConstant h params.delta params.beta
                params.rho params.multiplierBound ^ 2 *
              (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
            2 * (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2)) +
            (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2 *
              (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
            LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) :=
          add_le_add hstationarityExpanded hfeasibility
        _ = (2 * LALM.primalComparisonConstant h params.delta params.beta
                params.rho params.multiplierBound ^ 2 +
              LALM.multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
    _ ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
      LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hprimalCoefficient hstepSumNonneg)
        (mul_le_mul_of_nonneg_right herrorCoefficient herrorSumNonneg)
    _ = LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring

/-- Helper for Theorem 3.7: a segment in the regularity region gives the
quadratic upper Taylor estimate for the objective. -/
private lemma pathObjectiveChange_le
    (x y : EuclideanSpace ℝ (Fin n))
    (hsegment : segment ℝ x y ⊆ h.region) :
    f y - f x ≤
      ⟪gradient f x, y - x⟫_ℝ +
        (h.gradientLipschitz : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  -- Apply the quadratic remainder estimate along the admissible segment.
  have hremainder := norm_sub_sub_fderiv_le f h.gradientLipschitz h.region x y
    (fun _ hz ↦ h.differentiableAt_objective hz) h.lipschitzOn_objectiveFDeriv hsegment
  have hsigned :
      f y - f x - fderiv ℝ f x (y - x) ≤
        ‖f y - f x - fderiv ℝ f x (y - x)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f y - f x - fderiv ℝ f x (y - x))
  rw [← inner_gradient_left] at hremainder hsigned
  linarith

/-- Helper for Theorem 3.7: stochastic model optimality identifies the exact
change of the linearized augmented-Lagrangian terms on one path. -/
private lemma pathLinearizedAugmentedLagrangianChange_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ⟪run.gradientEstimate k ω, run.step k ω⟫_ℝ +
          ⟪run.multiplier k ω,
            fderiv ℝ c (run.point k ω) (run.step k ω)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 -
            ‖c (run.point k ω)‖ ^ 2) =
      -params.beta * ‖run.step k ω‖ ^ 2 -
        (params.rho / 2) *
          ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 := by
  -- Pair the pathwise normal equation with the chosen step.
  have hminimizes : IsMinOn
      (stepModelWithGradient c (run.gradientEstimate k ω) params.rho params.beta
        (run.point k ω) (run.multiplier k ω)) Set.univ (run.step k ω) := by
    simpa only [run.gradientEstimate_apply, positivePenaltyParameters_rho,
      positivePenaltyParameters_beta] using run.minimizes_step k ω
  have hfirstOrder := explicitGradientModelOptimality c
    (run.gradientEstimate k ω) params.rho params.beta
    (run.point k ω) (run.multiplier k ω) (run.step k ω)
    hminimizes
  have hoptimal := congrArg (fun v ↦ ⟪v, run.step k ω⟫_ℝ) hfirstOrder
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    inner_zero_left] at hoptimal
  rw [norm_add_sq_real]
  nlinarith

/-- Helper for Theorem 3.7: the next constraint value is its linearization plus
the pathwise Taylor remainder. -/
private lemma pathConstraintValue_eq_linearization_add_error
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    c (run.point (k + 1) ω) =
      c (run.point k ω) + fderiv ℝ c (run.point k ω) (run.step k ω) +
        pathLinearizationError run k ω := by
  rw [pathLinearizationError]
  module

/-- Helper for Theorem 3.7: one pathwise augmented-Lagrangian difference
splits into its linearized part and two Taylor-remainder terms. -/
private lemma pathAugmentedLagrangianChange_eq_linearized
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) -
        ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) =
      (f (run.point (k + 1) ω) - f (run.point k ω)) +
        ⟪run.multiplier k ω,
          fderiv ℝ c (run.point k ω) (run.step k ω)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 -
            ‖c (run.point k ω)‖ ^ 2) +
        ⟪run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)),
          pathLinearizationError run k ω⟫_ℝ +
        (params.rho / 2) * ‖pathLinearizationError run k ω‖ ^ 2 := by
  rw [augmentedLagrangian_def, augmentedLagrangian_def,
    pathConstraintValue_eq_linearization_add_error run k ω, norm_add_sq_real]
  simp only [inner_add_right, inner_add_left, inner_smul_left,
    starRingEnd_apply, star_trivial]
  ring

/-- Helper for Theorem 3.7: the constraint Taylor remainder contributes at
most the constraint part of the stochastic model constant. -/
private lemma pathConstraintRemainderContribution_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ⟪run.multiplier k ω + (params.rho : ℝ) •
          (c (run.point k ω) +
            fderiv ℝ c (run.point k ω) (run.step k ω)),
        pathLinearizationError run k ω⟫_ℝ +
        (params.rho / 2) * ‖pathLinearizationError run k ω‖ ^ 2 ≤
      (LALM.linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) +
        (params.rho / 2) * LALM.linearizationConstant h ^ 2 * params.delta ^ 2) *
          ‖run.step k ω‖ ^ 2 := by
  -- Bound the effective multiplier, derivative image, and Taylor remainder.
  have hx : run.point k ω ∈ h.region :=
    hsegment (left_mem_segment ℝ _ _)
  have hderivativeNorm :
      ‖fderiv ℝ c (run.point k ω)‖ ≤ h.constraintGradientBound := by
    rw [← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint]
    exact h.norm_constraintGradient_le (run.point k ω) hx
  have hlinearizedStep :
      ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ≤
        h.constraintGradientBound * ‖run.step k ω‖ := by
    calc
      ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ≤
          ‖fderiv ℝ c (run.point k ω)‖ * ‖run.step k ω‖ :=
        (fderiv ℝ c (run.point k ω)).le_opNorm (run.step k ω)
      _ ≤ h.constraintGradientBound * ‖run.step k ω‖ :=
        mul_le_mul_of_nonneg_right hderivativeNorm (norm_nonneg _)
  have heffectiveLinearized :
      ‖run.multiplier k ω + (params.rho : ℝ) •
          (c (run.point k ω) +
            fderiv ℝ c (run.point k ω) (run.step k ω))‖ ≤
        3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
    have hdecomposition :
        run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)) =
          (run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)) +
            (params.rho : ℝ) •
              fderiv ℝ c (run.point k ω) (run.step k ω) := by
      module
    rw [hdecomposition]
    have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
    calc
      ‖(run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)) +
          (params.rho : ℝ) •
            fderiv ℝ c (run.point k ω) (run.step k ω)‖ ≤
          ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ +
            ‖(params.rho : ℝ) •
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ := norm_add_le _ _
      _ ≤ 3 * params.multiplierBound +
          params.rho * (h.constraintGradientBound * ‖run.step k ω‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
        exact add_le_add heffective
          (mul_le_mul_of_nonneg_left hlinearizedStep hrho.le)
      _ ≤ 3 * params.multiplierBound +
          params.rho * h.constraintGradientBound * params.delta := by
        have hcoefficient :
            (0 : ℝ) ≤ params.rho * h.constraintGradientBound := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hstep hcoefficient]
  have herror := normPathLinearizationError_le run k ω hsegment
  have hlinearizedBoundNonneg :
      (0 : ℝ) ≤ 3 * params.multiplierBound +
        params.rho * h.constraintGradientBound * params.delta :=
    (norm_nonneg _).trans heffectiveLinearized
  have hinnerContribution :
      ⟪run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)),
          pathLinearizationError run k ω⟫_ℝ ≤
        LALM.linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.step k ω‖ ^ 2 := by
    calc
      ⟪run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)),
          pathLinearizationError run k ω⟫_ℝ ≤
          ‖run.multiplier k ω + (params.rho : ℝ) •
            (c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω))‖ *
              ‖pathLinearizationError run k ω‖ := real_inner_le_norm _ _
      _ ≤ (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
          (LALM.linearizationConstant h * ‖run.step k ω‖ ^ 2) :=
        mul_le_mul heffectiveLinearized herror (norm_nonneg _)
          hlinearizedBoundNonneg
      _ = LALM.linearizationConstant h *
          (3 * params.multiplierBound +
            params.rho * h.constraintGradientBound * params.delta) *
              ‖run.step k ω‖ ^ 2 := by ring
  have hstepSq :
      ‖run.step k ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herrorSq :
      ‖pathLinearizationError run k ω‖ ^ 2 ≤
        LALM.linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by
    have herrorBoundNonneg :
        (0 : ℝ) ≤ LALM.linearizationConstant h * ‖run.step k ω‖ ^ 2 := by
      positivity
    have hsquaredError :
        ‖pathLinearizationError run k ω‖ ^ 2 ≤
          (LALM.linearizationConstant h * ‖run.step k ω‖ ^ 2) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herrorBoundNonneg).2 herror
    calc
      ‖pathLinearizationError run k ω‖ ^ 2 ≤
          (LALM.linearizationConstant h * ‖run.step k ω‖ ^ 2) ^ 2 :=
        hsquaredError
      _ = LALM.linearizationConstant h ^ 2 *
          ‖run.step k ω‖ ^ 2 * ‖run.step k ω‖ ^ 2 := by ring
      _ ≤ LALM.linearizationConstant h ^ 2 *
          (params.delta : ℝ) ^ 2 * ‖run.step k ω‖ ^ 2 := by
        gcongr
      _ = LALM.linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by ring
  have hpenaltyContribution :
      (params.rho / 2) * ‖pathLinearizationError run k ω‖ ^ 2 ≤
        (params.rho / 2) * LALM.linearizationConstant h ^ 2 * params.delta ^ 2 *
          ‖run.step k ω‖ ^ 2 := by
    have hrhoHalf : (0 : ℝ) ≤ params.rho / 2 := by positivity
    calc
      (params.rho / 2) * ‖pathLinearizationError run k ω‖ ^ 2 ≤
          (params.rho / 2) *
            (LALM.linearizationConstant h ^ 2 * params.delta ^ 2 *
              ‖run.step k ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herrorSq hrhoHalf
      _ = (params.rho / 2) * LALM.linearizationConstant h ^ 2 *
          params.delta ^ 2 * ‖run.step k ω‖ ^ 2 := by ring
  nlinarith

/-- Helper for Theorem 3.7: the pathwise augmented-Lagrangian change is
bounded by its linearized change plus the model remainder. -/
private lemma pathAugmentedLagrangianChange_le_modelConstant
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta)
    (heffective :
      ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
        3 * (params.multiplierBound : ℝ)) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) -
        ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) ≤
      (⟪gradient f (run.point k ω), run.step k ω⟫_ℝ +
          ⟪run.multiplier k ω,
            fderiv ℝ c (run.point k ω) (run.step k ω)⟫_ℝ +
        (params.rho / 2) *
          (‖c (run.point k ω) +
              fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 -
            ‖c (run.point k ω)‖ ^ 2)) +
        LALM.modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.step k ω‖ ^ 2 := by
  -- Combine the objective Taylor estimate with the constraint remainder bound.
  have hobjective :
      f (run.point (k + 1) ω) - f (run.point k ω) ≤
        ⟪gradient f (run.point k ω), run.step k ω⟫_ℝ +
          (h.gradientLipschitz : ℝ) / 2 * ‖run.step k ω‖ ^ 2 := by
    have htaylor := pathObjectiveChange_le (h := h)
      (run.point k ω) (run.point (k + 1) ω) hsegment
    rw [run.point_succ, add_sub_cancel_left] at htaylor
    rw [run.point_succ]
    exact htaylor
  have hconstraint := pathConstraintRemainderContribution_le run k ω
    hsegment hstep heffective
  rw [pathAugmentedLagrangianChange_eq_linearized run k ω,
    LALM.modelConstant_def]
  nlinarith

/-- Helper for Theorem 3.7: explicit pathwise segment, step, and multiplier
bounds give one-step augmented-Lagrangian descent. -/
private lemma pathAugmentedLagrangianDescent
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hsegment : segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hstep : ‖run.step k ω‖ ≤ params.delta)
    (hmultiplier : ∀ j ≤ k, ‖run.multiplier j ω‖ ≤ params.multiplierBound) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) ≤
      ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) -
        (params.beta / 2) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
  -- The deterministic model decrease absorbs the pathwise Taylor remainder.
  have heffective := normEffectiveMultiplier_le run k ω hmultiplier
  have hchange := pathAugmentedLagrangianChange_le_modelConstant run k ω
    hsegment hstep heffective
  have hlinearized := pathLinearizedAugmentedLagrangianChange_eq run k ω
  have hgradientIdentity :
      gradient f (run.point k ω) =
        run.gradientEstimate k ω - run.gradientError k ω := by
    rw [run.gradientError_apply]
    module
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hquarterBeta : 0 < (params.beta : ℝ) / 4 := by positivity
  have hinverseQuarterBeta :
      ((params.beta : ℝ) / 4)⁻¹ = 4 / params.beta := by
    field_simp [hbeta.ne']
  have htwoProduct := two_mul_le_add_mul_sq
    (a := ‖run.step k ω‖) (b := ‖run.gradientError k ω‖) hquarterBeta
  rw [hinverseQuarterBeta] at htwoProduct
  have hyoung :
      ‖run.step k ω‖ * ‖run.gradientError k ω‖ ≤
        (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
    have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ‖run.step k ω‖ * ‖run.gradientError k ω‖ =
          (2 * ‖run.step k ω‖ * ‖run.gradientError k ω‖) / 2 := by ring
      _ ≤ ((params.beta / 4) * ‖run.step k ω‖ ^ 2 +
          (4 / params.beta) * ‖run.gradientError k ω‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right htwoProduct htwoNonneg
      _ = (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by ring
  have hinnerNorm := real_inner_le_norm
    (-run.gradientError k ω) (run.step k ω)
  simp only [inner_neg_left, norm_neg] at hinnerNorm
  have hyoungCommuted :
      ‖run.gradientError k ω‖ * ‖run.step k ω‖ ≤
        (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 := by
    simpa only [mul_comm] using hyoung
  have hinner :
      -⟪run.gradientError k ω, run.step k ω⟫_ℝ ≤
        (params.beta / 8) * ‖run.step k ω‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k ω‖ ^ 2 :=
    hinnerNorm.trans hyoungCommuted
  have hmodelTerm :
      LALM.modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.step k ω‖ ^ 2 ≤
        (3 * (params.beta : ℝ) / 8) * ‖run.step k ω‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) *
        ‖fderiv ℝ c (run.point k ω) (run.step k ω)‖ ^ 2 := by
    positivity
  rw [hgradientIdentity, inner_sub_left] at hchange
  nlinarith

/-- Helper for Theorem 3.7: a multiplier update increases the augmented
Lagrangian by the squared multiplier increment divided by the penalty. -/
private lemma pathAugmentedLagrangianMultiplierSucc_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier (k + 1) ω) =
      ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) +
        ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho := by
  -- Substitute the exact multiplier update and cancel the positive penalty.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) :=
    run.multiplier_succ k ω
  rw [augmentedLagrangian_def, augmentedLagrangian_def, hupdate,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos hrho, real_inner_self_eq_norm_sq,
    starRingEnd_apply, star_trivial]
  field_simp [hrho.ne']
  ring

/-- Helper for Theorem 3.7: the admissible parameter inequality bounds the
multiplier-primal coefficient after division by the penalty. -/
private lemma pathMultiplierPrimalConstant_div_rho_le_beta_div_eight :
    LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  -- Normalize the parameter certificate by the positive penalty.
  have hscaled :
      8 * LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Theorem 3.7: explicit fixed-path bounds imply the stochastic
Lyapunov descent inequality at a positive iteration. -/
private lemma pathLyapunovDescent
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω)
    (hsegmentCurrent :
      segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region)
    (hsegmentPrevious :
      segment ℝ (run.point (k - 1) ω) (run.point k ω) ⊆ h.region)
    (hstepCurrent : ‖run.step k ω‖ ≤ params.delta)
    (hstepPrevious : ‖run.step (k - 1) ω‖ ≤ params.delta)
    (hmultipliers : ∀ j ≤ k + 1,
      ‖run.multiplier j ω‖ ≤ params.multiplierBound) :
    run.lyapunov (k + 1) ω ≤
      run.lyapunov k ω - (params.beta / 4) * ‖run.step k ω‖ ^ 2 +
        lyapunovErrorConstant h params *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- Combine augmented-Lagrangian descent with the multiplier increment bound.
  have hmultiplierPrefix : ∀ j ≤ k,
      ‖run.multiplier j ω‖ ≤ params.multiplierBound := by
    intro j hj
    exact hmultipliers j (by omega)
  have hlagrangian := pathAugmentedLagrangianDescent run k ω
    hsegmentCurrent hstepCurrent hmultiplierPrefix
  have hmultiplier := normPathMultiplierIncrementSq_le run k hk_pos ω
    hsegmentCurrent hsegmentPrevious hstepCurrent hstepPrevious
    (hmultipliers k (by omega))
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierDivided :=
    (div_le_div_iff_of_pos_right hrho).2 hmultiplier
  have hmultiplierDiv :
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho ≤
        (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
        (LALM.multiplierErrorConstant h / params.rho) *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho ≤
          (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
                (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
            LALM.multiplierErrorConstant h *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) / params.rho :=
        hmultiplierDivided
      _ = (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / params.rho) *
            (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2) +
          (LALM.multiplierErrorConstant h / params.rho) *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  have hcoefficient :=
    pathMultiplierPrimalConstant_div_rho_le_beta_div_eight
      (h := h) (params := params)
  have hcurrent :
      2 * (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step k ω‖ ^ 2 ≤
        (params.beta / 4) * ‖run.step k ω‖ ^ 2 := by
    have htwiceCoefficient :
        2 * (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) ≤ params.beta / 4 := by
      linarith
    exact mul_le_mul_of_nonneg_right htwiceCoefficient (sq_nonneg _)
  have herrorPreviousNonneg :
      (0 : ℝ) ≤ (2 / params.beta) *
        ‖run.gradientError (k - 1) ω‖ ^ 2 := by
    positivity
  rw [run.lyapunov_def, run.lyapunov_def,
    pathAugmentedLagrangianMultiplierSucc_eq run, Nat.add_sub_cancel,
    lyapunovErrorConstant_def]
  nlinarith

/-- Helper for Theorem 3.7: a bounded multiplier gives the standard uniform
lower bound for the augmented Lagrangian on the regularity region. -/
private lemma pathAugmentedLagrangianLowerBound
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (hx : x ∈ h.region) (hmultiplier : ‖multiplier‖ ≤ params.multiplierBound) :
    h.objectiveLower - params.multiplierBound ^ 2 / (2 * params.rho) ≤
      ℒ[f, c; params.rho](x, multiplier) := by
  -- Complete the square in the constraint and multiplier terms.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinner : -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        params.rho * ‖c x‖ ^ 2 + (params.rho : ℝ)⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have hyoungDivided :=
    div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        params.rho / 2 * ‖c x‖ ^ 2 +
          ‖multiplier‖ ^ 2 / (2 * params.rho) := by
    calc
      ‖multiplier‖ * ‖c x‖ = (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (params.rho * ‖c x‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖multiplier‖ ^ 2) / 2 := hyoungDivided
      _ = params.rho / 2 * ‖c x‖ ^ 2 +
          ‖multiplier‖ ^ 2 / (2 * params.rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq :
      ‖multiplier‖ ^ 2 ≤ (params.multiplierBound : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hboundNonneg).2 hmultiplier
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * (params.rho : ℝ)) ≤
        (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) :=
    (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hrho)).2 hmultiplierSq
  have hobjective := h.objectiveLower_le x hx
  rw [augmentedLagrangian_def]
  linarith

/-- Helper for Theorem 3.7: fixed-path regularity and multiplier bounds put a
positive-index Lyapunov value above its uniform lower bound. -/
private lemma pathLyapunovLowerBound_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (ω : Ω)
    (hsegmentPrevious :
      segment ℝ (run.point (k - 1) ω) (run.point k ω) ⊆ h.region)
    (hmultiplier : ‖run.multiplier k ω‖ ≤ params.multiplierBound) :
    LALM.lyapunovLowerBound h params ≤ run.lyapunov k ω := by
  -- The segment endpoint is regular, and the Lyapunov correction is nonnegative.
  have hx : run.point k ω ∈ h.region := by
    have hindex : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
    simpa only [hindex] using
      hsegmentPrevious (right_mem_segment ℝ _ _)
  have hlower := pathAugmentedLagrangianLowerBound
    (h := h) (params := params) (run.point k ω) (run.multiplier k ω)
    hx hmultiplier
  have hconstantNonneg :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hcorrectionNonneg :
      0 ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
        ‖run.step (k - 1) ω‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg hrho.le) (sq_nonneg _)
  rw [LALM.lyapunovLowerBound_def, run.lyapunov_def]
  linarith

/-- Helper for Theorem 3.7: fixed-path bounds at the initial step put the first
Lyapunov value below the deterministic initial potential. -/
private lemma pathLyapunovOne_le_initialPotentialBound
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (ω : Ω)
    (hsegment : segment ℝ (run.point 0 ω) (run.point 1 ω) ⊆ h.region)
    (hstep : ‖run.step 0 ω‖ ≤ params.delta)
    (hmultiplierZero : ‖run.multiplier 0 ω‖ ≤ params.multiplierBound)
    (hmultiplierOne : ‖run.multiplier 1 ω‖ ≤ params.multiplierBound) :
    run.lyapunov 1 ω ≤ LALM.initialPotentialBound h params := by
  -- Bound the objective increment and the initial constraint contribution.
  have hobjectiveIncrement :
      ‖f (run.point 1 ω) - f (run.point 0 ω)‖ ≤
        h.gradientBound * ‖run.point 1 ω - run.point 0 ω‖ := by
    apply (convex_segment (run.point 0 ω) (run.point 1 ω)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ)
    · intro u hu
      exact h.differentiableAt_objective (hsegment hu)
    · intro u hu
      simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
        h.norm_gradient_le u (hsegment hu)
    · exact left_mem_segment ℝ (run.point 0 ω) (run.point 1 ω)
    · exact right_mem_segment ℝ (run.point 0 ω) (run.point 1 ω)
  have hdisplacement :
      ‖run.point 1 ω - run.point 0 ω‖ = ‖run.step 0 ω‖ := by
    rw [run.point_succ 0, add_sub_cancel_left]
  have hsignedObjective :
      f (run.point 1 ω) - f (run.point 0 ω) ≤
        ‖f (run.point 1 ω) - f (run.point 0 ω)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (run.point 1 ω) - f (run.point 0 ω))
  have hobjective :
      f (run.point 1 ω) ≤ f x₀ + h.gradientBound * params.delta := by
    have hgradientStep :
        (h.gradientBound : ℝ) * ‖run.step 0 ω‖ ≤
          h.gradientBound * params.delta :=
      mul_le_mul_of_nonneg_left hstep (NNReal.coe_nonneg h.gradientBound)
    rw [hdisplacement] at hobjectiveIncrement
    rw [run.point_zero] at hsignedObjective hobjectiveIncrement
    linarith
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point 1 ω) =
        run.multiplier 1 ω - run.multiplier 0 ω := by
    have hupdate :
        run.multiplier 1 ω = run.multiplier 0 ω +
          (params.rho : ℝ) • c (run.point 1 ω) :=
      run.multiplier_succ 0 ω
    rw [hupdate]
    module
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hscaledResidual :
      params.rho * ‖c (run.point 1 ω)‖ ≤ 2 * params.multiplierBound := by
    calc
      params.rho * ‖c (run.point 1 ω)‖ =
          ‖(params.rho : ℝ) • c (run.point 1 ω)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
      _ = ‖run.multiplier 1 ω - run.multiplier 0 ω‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier 1 ω‖ + ‖run.multiplier 0 ω‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinnerBound :
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ ≤
        params.multiplierBound * ‖c (run.point 1 ω)‖ := by
    calc
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ ≤
          ‖run.multiplier 1 ω‖ * ‖c (run.point 1 ω)‖ :=
        real_inner_le_norm _ _
      _ ≤ params.multiplierBound * ‖c (run.point 1 ω)‖ :=
        mul_le_mul_of_nonneg_right hmultiplierOne (norm_nonneg _)
  have hinnerScaled :
      params.rho * ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ ≤
        2 * params.multiplierBound ^ 2 := by
    have hinnerRho := mul_le_mul_of_nonneg_left hinnerBound hrho.le
    have hresidualBound := mul_le_mul_of_nonneg_left hscaledResidual hboundNonneg
    nlinarith
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hscaledResidualSq :
      (params.rho * ‖c (run.point 1 ω)‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hrho.le (norm_nonneg _))
      (mul_nonneg htwoNonneg hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ +
          params.rho / 2 * ‖c (run.point 1 ω)‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ hrho).2
    nlinarith
  have hconstantNonneg :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖run.step 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrection :
      (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step 0 ω‖ ^ 2 ≤
        (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq
      (div_nonneg hconstantNonneg hrho.le)
  rw [run.lyapunov_def, augmentedLagrangian_def,
    LALM.initialPotentialBound_def]
  norm_num only [Nat.reduceSub]
  linarith

/-- Helper for Theorem 3.7: a bounded multiplier lets the Lyapunov value
control the objective at the same stochastic iterate. -/
private lemma pathObjective_le_lyapunov
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hmultiplier : ‖run.multiplier k ω‖ ≤ params.multiplierBound) :
    f (run.point k ω) ≤ run.lyapunov k ω +
      params.multiplierBound ^ 2 / (2 * params.rho) := by
  -- Complete the square in the augmented-Lagrangian constraint terms.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinner :
      -(‖run.multiplier k ω‖ * ‖c (run.point k ω)‖) ≤
        ⟪run.multiplier k ω, c (run.point k ω)⟫_ℝ :=
    neg_le_of_abs_le
      (abs_real_inner_le_norm (run.multiplier k ω) (c (run.point k ω)))
  have hyoung :
      2 * ‖c (run.point k ω)‖ * ‖run.multiplier k ω‖ ≤
        params.rho * ‖c (run.point k ω)‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖run.multiplier k ω‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have hyoungHalf :
      ‖run.multiplier k ω‖ * ‖c (run.point k ω)‖ ≤
        params.rho / 2 * ‖c (run.point k ω)‖ ^ 2 +
          ‖run.multiplier k ω‖ ^ 2 / (2 * params.rho) := by
    have hdivided :=
      div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
    calc
      ‖run.multiplier k ω‖ * ‖c (run.point k ω)‖ =
          (2 * ‖c (run.point k ω)‖ * ‖run.multiplier k ω‖) / 2 := by ring
      _ ≤ (params.rho * ‖c (run.point k ω)‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖run.multiplier k ω‖ ^ 2) / 2 := hdivided
      _ = params.rho / 2 * ‖c (run.point k ω)‖ ^ 2 +
          ‖run.multiplier k ω‖ ^ 2 / (2 * params.rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq :
      ‖run.multiplier k ω‖ ^ 2 ≤ (params.multiplierBound : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hboundNonneg).2 hmultiplier
  have hmultiplierDiv :
      ‖run.multiplier k ω‖ ^ 2 / (2 * (params.rho : ℝ)) ≤
        (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) :=
    (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hrho)).2 hmultiplierSq
  have hconstraintLower :
      -(params.multiplierBound ^ 2 / (2 * (params.rho : ℝ))) ≤
        ⟪run.multiplier k ω, c (run.point k ω)⟫_ℝ +
          params.rho / 2 * ‖c (run.point k ω)‖ ^ 2 := by
    linarith
  -- The remaining Lyapunov correction is nonnegative.
  have hconstantNonneg :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
        ‖run.step (k - 1) ω‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg hrho.le) (sq_nonneg _)
  rw [run.lyapunov_def, augmentedLagrangian_def]
  linarith

namespace Localization

/-- Helper for Theorem 3.7: the active projected-gradient-error energy accumulated
through a finite horizon, with each term killed after localization exit. -/
private noncomputable def activeErrorEnergy
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range K,
    (survivalEvent run X k).indicator
      (fun ω' ↦ ENNReal.ofReal (‖run.gradientError k ω'‖ ^ 2)) ω

/-- Helper for Theorem 3.7: the real-valued active projected-gradient-error
energy accumulated through a finite localization horizon. -/
private noncomputable def activeErrorEnergyReal
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K,
    (survivalEvent run X k).indicator
      (fun ω' ↦ ‖run.gradientError k ω'‖ ^ 2) ω

/-- Helper for Theorem 3.7: the active `ℝ≥0∞` energy is the nonnegative
embedding of its real-valued counterpart. -/
private lemma activeErrorEnergy_eq_ofReal
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) :
    activeErrorEnergy run X K ω =
      ENNReal.ofReal (activeErrorEnergyReal run X K ω) := by
  -- Commute `ofReal` through the finite nonnegative indicator sum termwise.
  unfold activeErrorEnergy activeErrorEnergyReal
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hactive : ω ∈ survivalEvent run X k
    · simp only [Set.indicator_of_mem hactive]
    · simp [hactive]
  · intro k hk
    by_cases hactive : ω ∈ survivalEvent run X k
    · simp only [Set.indicator_of_mem hactive]
      exact sq_nonneg _
    · simp [hactive]

/-- Helper for Theorem 3.7: active projected-gradient-error energy is almost
everywhere measurable for a measurable localization set. -/
private lemma aemeasurable_activeErrorEnergy
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (K : ℕ) :
    AEMeasurable (activeErrorEnergy run X K) ℙ := by
  -- Each active term inherits measurability from its restricted integrability.
  unfold activeErrorEnergy
  have hsum : AEMeasurable
      (∑ k ∈ Finset.range K, fun ω ↦
        (survivalEvent run X k).indicator
          (fun ω' ↦ ENNReal.ofReal (‖run.gradientError k ω'‖ ^ 2)) ω) ℙ := by
    apply Finset.aemeasurable_sum
    intro k hk
    have hactive := nullMeasurableSet_survivalEvent run X hX k
    have hintegrable :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact (aemeasurable_indicator_iff₀ hactive).mpr
      hintegrable.aemeasurable.ennreal_ofReal
  have hfun :
      (fun ω ↦
        ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun ω' ↦ ENNReal.ofReal (‖run.gradientError k ω'‖ ^ 2)) ω) =
        ∑ k ∈ Finset.range K, fun ω ↦
          (survivalEvent run X k).indicator
            (fun ω' ↦ ENNReal.ofReal (‖run.gradientError k ω'‖ ^ 2)) ω := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hfun]
  exact hsum

/-- Helper for Theorem 3.7: integrating the active error-energy random variable
recovers exactly `stoppedErrorEnergy` after passage from `ℝ` to `ℝ≥0∞`. -/
private lemma lintegral_activeErrorEnergy
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (K : ℕ) :
    ∫⁻ ω, activeErrorEnergy run X K ω ∂ℙ =
      ENNReal.ofReal (stoppedErrorEnergy run X K) := by
  -- Expand the finite sum and convert every active set integral separately.
  unfold activeErrorEnergy
  rw [lintegral_finsetSum']
  · rw [stoppedErrorEnergy, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      have hactive := nullMeasurableSet_survivalEvent run X hX k
      have hintegrable :=
        integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
      rw [lintegral_indicator₀ hactive]
      exact (ofReal_integral_eq_lintegral_ofReal hintegrable
        (ae_of_all _ fun ω ↦ sq_nonneg ‖run.gradientError k ω‖)).symm
    · intro k hk
      exact integral_nonneg fun ω ↦ sq_nonneg ‖run.gradientError k ω‖
  · intro k hk
    have hactive := nullMeasurableSet_survivalEvent run X hX k
    have hintegrable :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact (aemeasurable_indicator_iff₀ hactive).mpr
      hintegrable.aemeasurable.ennreal_ofReal

/-- Helper for Theorem 3.7: Markov's inequality bounds a positive threshold
crossing of active error energy by its stopped expectation. -/
private lemma measure_activeErrorEnergy_ge_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (K : ℕ) (threshold : ℝ) (threshold_pos : 0 < threshold) :
    ℙ {ω | ENNReal.ofReal threshold ≤ activeErrorEnergy run X K ω} ≤
      ENNReal.ofReal (stoppedErrorEnergy run X K / threshold) := by
  -- Apply ENNReal-valued Markov, then identify both the integral and denominator.
  have hmarkov := meas_ge_le_lintegral_div
    (aemeasurable_activeErrorEnergy run X hX initial_mem h_region K)
    ((ENNReal.ofReal_ne_zero_iff).mpr threshold_pos) ENNReal.ofReal_ne_top
  rw [lintegral_activeErrorEnergy run X hX initial_mem h_region K] at hmarkov
  rw [ENNReal.ofReal_div_of_pos threshold_pos]
  exact hmarkov

/-- Helper for Theorem 3.7: localization of the initial point makes the gap
between the deterministic initial potential and Lyapunov lower bound nonnegative. -/
private lemma initialPotentialGap_nonneg
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    0 ≤ LALM.initialPotentialBound h params - LALM.lyapunovLowerBound h params := by
  -- The thickening condition places `x₀` in the regularity region.
  have hx₀ : x₀ ∈ h.region :=
    h_region.thickening_subset (Metric.self_subset_cthickening X initial_mem)
  have hobjective : h.objectiveLower ≤ f x₀ := h.objectiveLower_le x₀ hx₀
  have hmultiplierConstant :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hgradientTerm :
      0 ≤ (h.gradientBound : ℝ) * params.delta := by positivity
  have hmultiplierTerm :
      0 ≤ 4 * (params.multiplierBound : ℝ) ^ 2 / params.rho := by positivity
  have hcorrectionTerm :
      0 ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * (params.delta : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg hmultiplierConstant hrho.le) (sq_nonneg _)
  have hlowerCorrection :
      0 ≤ (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) := by positivity
  rw [LALM.initialPotentialBound_def, LALM.lyapunovLowerBound_def]
  linarith

/-- Helper for Theorem 3.7: the initial stochastic step allowance is strictly
positive under the localization hypotheses. -/
private lemma initialStepBound_pos
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    0 < initialStepBound h params := by
  -- The positive step radius and nonnegative potential gap make the sum positive.
  have hgap := initialPotentialGap_nonneg X initial_mem h_region
  have hdelta : 0 < (params.delta : ℝ) := params.spec.1.1
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  rw [initialStepBound_def]
  positivity

/-- Helper for Theorem 3.7: the coefficient multiplying adjacent stochastic
Lyapunov errors is strictly positive. -/
private lemma lyapunovErrorConstant_pos : 0 < lyapunovErrorConstant h params := by
  -- The positive `2 / beta` branch dominates the remaining nonnegative term.
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  rw [lyapunovErrorConstant_def]
  positivity

/-- Helper for Theorem 3.7: the coefficient transferring estimator error to
step energy is strictly positive. -/
private lemma errorStepConstant_pos : 0 < errorStepConstant h params := by
  -- The `2 / beta` summand already makes the Lyapunov error coefficient positive.
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hlyapunovError : 0 < lyapunovErrorConstant h params :=
    lyapunovErrorConstant_pos
  rw [errorStepConstant_def]
  positivity

/-- Helper for Theorem 3.7: the scheduled total estimator-error allowance is
strictly positive under the localization hypotheses. -/
private lemma errorAverageConstant_pos
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    0 < errorAverageConstant h oracle params := by
  -- Its initial-energy quotient is positive, independently of the oracle noise.
  have hinitial := initialStepBound_pos X initial_mem h_region
  have hcoefficient : 0 < errorStepConstant h params := errorStepConstant_pos
  rw [errorAverageConstant_def]
  positivity

/-- Helper for Theorem 3.7: the stochastic KKT comparison constant is
nonnegative. -/
private lemma stochasticResidualConstant_nonneg :
    0 ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
      params.multiplierBound := by
  -- The second branch of the defining maximum is nonnegative.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hsecond :
      (0 : ℝ) ≤ 2 + LALM.multiplierErrorConstant h / params.rho ^ 2 := by
    positivity
  rw [LALM.stochasticResidualConstant_def]
  exact hsecond.trans (le_max_right _ _)

/-- Helper for Theorem 3.7: the number of active iterations before the first
exit, truncated at the prescribed finite horizon. -/
private noncomputable def activePrefixLength
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) : ℕ :=
  min K ((exitTime run X ω).untopD K)

/-- Helper for Theorem 3.7: the truncated active-prefix length is positive,
bounded by the horizon, and characterizes every active index below it. -/
private lemma activePrefixLength_spec
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (hK : 1 ≤ K) (ω : Ω) :
    1 ≤ activePrefixLength run X K ω ∧
      activePrefixLength run X K ω ≤ K ∧
      ∀ k < K,
        (k < activePrefixLength run X K ω ↔
          ω ∈ survivalEvent run X k) := by
  -- The canonical hitting time starts at one; truncation preserves that lower
  -- bound and makes the upper bound immediate.
  have hexitLower : (1 : WithTop ℕ) ≤ exitTime run X ω := by
    exact MeasureTheory.le_hittingAfter (u := run.point) (s := Xᶜ) (n := 1) ω
  have hdefaultLower : 1 ≤ (exitTime run X ω).untopD K := by
    rw [WithTop.le_untopD_iff (fun _ ↦ hK)]
    exact hexitLower
  refine ⟨(Nat.le_min).2 ⟨hK, hdefaultLower⟩, min_le_left _ _, ?_⟩
  intro k hk
  -- Below `K`, comparison with the truncated natural length is exactly
  -- comparison with the `WithTop`-valued hitting time.
  have hdefault :
      k < (exitTime run X ω).untopD K ↔
        (k : WithTop ℕ) < exitTime run X ω := by
    apply WithTop.lt_untopD_iff
    intro hexitTop
    simpa only [hexitTop, WithTop.untopD_top] using hk
  have hsurvival :
      ω ∈ survivalEvent run X k ↔
        (k : WithTop ℕ) < exitTime run X ω := by
    rw [mem_survivalEvent, ← not_le, exitTime_le_iff]
    simp
  rw [activePrefixLength, lt_min_iff, hdefault, hsurvival]
  simp only [hk, true_and]

/-- Helper for Theorem 3.7: a survival-indicator sum is the ordinary sum over
the truncated active prefix. -/
private lemma activePrefixSum_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (hK : 1 ≤ K)
    (ω : Ω) (g : ℕ → Ω → ℝ) :
    (∑ k ∈ Finset.range K,
        (survivalEvent run X k).indicator (g k) ω) =
      ∑ k ∈ Finset.range (activePrefixLength run X K ω), g k ω := by
  -- First replace each indicator by the corresponding prefix-membership test.
  have hindicator :
      (∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator (g k) ω) =
        ∑ k ∈ Finset.range K,
          if k < activePrefixLength run X K ω then g k ω else 0 := by
    apply Finset.sum_congr rfl
    intro k hkRange
    have hk : k < K := Finset.mem_range.mp hkRange
    have hactive := (activePrefixLength_spec run X K hK ω).2.2 k hk
    by_cases hkPrefix : k < activePrefixLength run X K ω
    · rw [Set.indicator_of_mem (hactive.mp hkPrefix), if_pos hkPrefix]
    · rw [Set.indicator_of_notMem (fun hmem ↦ hkPrefix (hactive.mpr hmem)),
        if_neg hkPrefix]
  rw [hindicator]
  -- Terms outside the shorter range vanish, so `Finset.sum_subset` removes them.
  have hsubset :
      Finset.range (activePrefixLength run X K ω) ⊆ Finset.range K :=
    Finset.range_mono (activePrefixLength_spec run X K hK ω).2.1
  have htrimmed :
      (∑ k ∈ Finset.range (activePrefixLength run X K ω),
          if k < activePrefixLength run X K ω then g k ω else 0) =
        ∑ k ∈ Finset.range K,
          if k < activePrefixLength run X K ω then g k ω else 0 :=
    Finset.sum_subset hsubset
      (fun k _hkRange hkPrefix ↦ by
        have hkNotLt : ¬k < activePrefixLength run X K ω := by
          simpa only [Finset.mem_range] using hkPrefix
        simp only [if_neg hkNotLt])
  calc
    (∑ k ∈ Finset.range K,
        if k < activePrefixLength run X K ω then g k ω else 0) =
        ∑ k ∈ Finset.range (activePrefixLength run X K ω),
          if k < activePrefixLength run X K ω then g k ω else 0 := htrimmed.symm
    _ = ∑ k ∈ Finset.range (activePrefixLength run X K ω), g k ω := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [if_pos (Finset.mem_range.mp hk)]

/-- Helper for Theorem 3.7: survival through a positive prefix controls its
terminal objective by the deterministic potential and the prefix error energy. -/
private lemma objectiveAtPrefixEnd_le_of_survival
    (N : ℕ) (hN : 1 ≤ N)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (hω : ω ∈ survivalEvent run X (N - 1)) :
    f (run.point N ω) ≤ LALM.deterministicObjectiveBound h params +
      2 * lyapunovErrorConstant h params *
        ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
  -- Expose the localized path bounds once and keep the telescope independent
  -- of the hitting-time representation.
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hbounds := preExitPrefixBounds run X initial_mem h_region ω (N - 1) hω
  have hsegments : ∀ j < N,
      segment ℝ (run.point j ω) (run.point (j + 1) ω) ⊆ h.region := by
    intro j hj
    exact hbounds.1 j (by simpa only [hpred] using hj)
  have hsteps : ∀ j < N, ‖run.step j ω‖ ≤ params.delta := by
    intro j hj
    exact hbounds.2.1 j (by simpa only [hpred] using hj)
  have hmultipliers : ∀ j ≤ N,
      ‖run.multiplier j ω‖ ≤ params.multiplierBound := by
    intro j hj
    exact hbounds.2.2 j (by simpa only [hpred] using hj)
  have hdescent :
      (∑ k ∈ Finset.Ico 1 N,
          (params.beta / 4) * ‖run.step k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.Ico 1 N,
          ((run.lyapunov k ω - run.lyapunov (k + 1) ω) +
            lyapunovErrorConstant h params *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkBounds := Finset.mem_Ico.mp hk
    have hkPreviousLt : k - 1 < N := by omega
    have hkSuccLe : k + 1 ≤ N := by omega
    have hmultiplierPrefix : ∀ j ≤ k + 1,
        ‖run.multiplier j ω‖ ≤ params.multiplierBound := by
      intro j hj
      exact hmultipliers j (hj.trans hkSuccLe)
    have hpreviousEndpoint : k - 1 + 1 = k :=
      Nat.sub_add_cancel hkBounds.1
    have hone := pathLyapunovDescent run k hkBounds.1 ω
      (hsegments k hkBounds.2)
      (by simpa only [hpreviousEndpoint] using
        hsegments (k - 1) hkPreviousLt)
      (hsteps k hkBounds.2) (hsteps (k - 1) hkPreviousLt)
      hmultiplierPrefix
    linarith
  have htelescope :
      (∑ k ∈ Finset.Ico 1 N,
          (run.lyapunov k ω - run.lyapunov (k + 1) ω)) =
        run.lyapunov 1 ω - run.lyapunov N ω := by
    have hendpointLeft : 1 + (N - 1) = N := by omega
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hpred] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov (k + 1) ω) (N - 1))
  -- Each current and predecessor error occurs at most once in its respective
  -- sum, hence at most twice after both sums are combined.
  have hcurrentSubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) ω‖ ^ 2) =
        ∑ j ∈ Finset.range (N - 1), ‖run.gradientError j ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hindex : 1 + j - 1 = j := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (N - 1) ⊆ Finset.range N := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 N,
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) ≤
        2 * ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  have herrorCoefficientNonneg : 0 ≤ lyapunovErrorConstant h params :=
    (lyapunovErrorConstant_pos (h := h) (params := params)).le
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  have hstepContributionNonneg :
      0 ≤ (params.beta / 4) *
        ∑ k ∈ Finset.Ico 1 N, ‖run.step k ω‖ ^ 2 := by positivity
  have hterminalLyapunov :
      run.lyapunov N ω ≤ run.lyapunov 1 ω +
        2 * lyapunovErrorConstant h params *
          ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    nlinarith
  -- Finish with the initial-potential bound and the terminal completion square.
  have hzeroLt : 0 < N := Nat.zero_lt_of_lt hN
  have hinitial := pathLyapunovOne_le_initialPotentialBound run ω
    (hsegments 0 hzeroLt) (hsteps 0 hzeroLt)
    (hmultipliers 0 (Nat.zero_le N)) (hmultipliers 1 hN)
  have hterminal := pathObjective_le_lyapunov run N ω
    (hmultipliers N (Nat.le_refl N))
  rw [LALM.deterministicObjectiveBound_def]
  linarith

/-- Helper for Theorem 3.7: survival through a positive finite prefix bounds
its pathwise primal-step energy by the initial allowance and active errors. -/
private lemma sumStepSq_le_of_survival
    (N : ℕ) (hN : 2 ≤ N)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (hω : ω ∈ survivalEvent run X (N - 1)) :
    ∑ k ∈ Finset.range N, ‖run.step k ω‖ ^ 2 ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
  -- Expose the complete fixed-path interface supplied by pre-exit localization.
  have hpred : N - 1 + 1 = N := by omega
  have hbounds := preExitPrefixBounds run X initial_mem h_region ω (N - 1) hω
  have hsegments : ∀ j < N,
      segment ℝ (run.point j ω) (run.point (j + 1) ω) ⊆ h.region := by
    intro j hj
    exact hbounds.1 j (by simpa only [hpred] using hj)
  have hsteps : ∀ j < N, ‖run.step j ω‖ ≤ params.delta := by
    intro j hj
    exact hbounds.2.1 j (by simpa only [hpred] using hj)
  have hmultipliers : ∀ j ≤ N,
      ‖run.multiplier j ω‖ ≤ params.multiplierBound := by
    intro j hj
    exact hbounds.2.2 j (by simpa only [hpred] using hj)
  have hdescent :
      (∑ k ∈ Finset.Ico 1 N,
          (params.beta / 4) * ‖run.step k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.Ico 1 N,
          ((run.lyapunov k ω - run.lyapunov (k + 1) ω) +
            lyapunovErrorConstant h params *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkBounds := Finset.mem_Ico.mp hk
    have hkPreviousLt : k - 1 < N := by omega
    have hkSuccLe : k + 1 ≤ N := by omega
    have hmultiplierPrefix : ∀ j ≤ k + 1,
        ‖run.multiplier j ω‖ ≤ params.multiplierBound := by
      intro j hj
      exact hmultipliers j (hj.trans hkSuccLe)
    have hpreviousEndpoint : k - 1 + 1 = k :=
      Nat.sub_add_cancel hkBounds.1
    have hstepDescent := pathLyapunovDescent run k hkBounds.1 ω
      (hsegments k hkBounds.2)
      (by simpa only [hpreviousEndpoint] using
        hsegments (k - 1) hkPreviousLt)
      (hsteps k hkBounds.2) (hsteps (k - 1) hkPreviousLt)
      hmultiplierPrefix
    linarith
  have htelescope :
      (∑ k ∈ Finset.Ico 1 N,
          (run.lyapunov k ω - run.lyapunov (k + 1) ω)) =
        run.lyapunov 1 ω - run.lyapunov N ω := by
    have hendpointLeft : 1 + (N - 1) = N := by omega
    have hendpointRight : N - 1 + 1 = N := by omega
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov (k + 1) ω) (N - 1))
  have hcurrentSubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) ω‖ ^ 2) =
        ∑ j ∈ Finset.range (N - 1), ‖run.gradientError j ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hindex : 1 + j - 1 = j := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (N - 1) ⊆ Finset.range N := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 N,
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) ≤
        2 * ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  have hOne : 1 ≤ N := by omega
  have hzeroLt : 0 < N := by omega
  have hterminalPrevious : N - 1 < N := by omega
  have hterminalEndpoint : N - 1 + 1 = N := Nat.sub_add_cancel hOne
  have hlower := pathLyapunovLowerBound_le run N hOne ω
    (by simpa only [hterminalEndpoint] using
      hsegments (N - 1) hterminalPrevious)
    (hmultipliers N (Nat.le_refl N))
  have herrorCoefficientNonneg : 0 ≤ lyapunovErrorConstant h params :=
    (lyapunovErrorConstant_pos (h := h) (params := params)).le
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  have henergy :
      (params.beta / 4) *
          (∑ k ∈ Finset.Ico 1 N, ‖run.step k ω‖ ^ 2) ≤
        run.lyapunov 1 ω - LALM.lyapunovLowerBound h params +
          2 * lyapunovErrorConstant h params *
            ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    nlinarith
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hscalingNonneg : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  have hsumIco :
      (∑ k ∈ Finset.Ico 1 N, ‖run.step k ω‖ ^ 2) ≤
        4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) / params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by
    calc
      (∑ k ∈ Finset.Ico 1 N, ‖run.step k ω‖ ^ 2) =
          (4 / params.beta) *
            ((params.beta / 4) *
              ∑ k ∈ Finset.Ico 1 N, ‖run.step k ω‖ ^ 2) := by
        field_simp [hbeta.ne']
      _ ≤ (4 / params.beta) *
          (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params +
            2 * lyapunovErrorConstant h params *
              ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hscalingNonneg
      _ = 4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) /
            params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range N, ‖run.gradientError k ω‖ ^ 2 := by ring
  have hupper := pathLyapunovOne_le_initialPotentialBound run ω
    (hsegments 0 hzeroLt) (hsteps 0 hzeroLt)
    (hmultipliers 0 (Nat.zero_le N)) (hmultipliers 1 hOne)
  have hgap := sub_le_sub_right hupper (LALM.lyapunovLowerBound h params)
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hscalingNonneg
  have hgapScaledNormalized :
      4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) / params.beta ≤
        4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by
    calc
      4 * (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) / params.beta =
          (4 / params.beta) *
            (run.lyapunov 1 ω - LALM.lyapunovLowerBound h params) := by ring
      _ ≤ (4 / params.beta) *
          (LALM.initialPotentialBound h params -
            LALM.lyapunovLowerBound h params) := hgapScaled
      _ = 4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by ring
  have hstepZeroSq :
      ‖run.step 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 (hsteps 0 hzeroLt)
  have hdecomposition :
      (∑ k ∈ Finset.range N, ‖run.step k ω‖ ^ 2) =
        ‖run.step 0 ω‖ ^ 2 +
          ∑ k ∈ Finset.Ico 1 N, ‖run.step k ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hOne]
    simp
  rw [hdecomposition, initialStepBound_def, errorStepConstant_def]
  linarith

/-- Helper for Theorem 3.7: the real-valued active primal-step energy through a
finite localization horizon. -/
private noncomputable def activeStepEnergyReal
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K,
    (survivalEvent run X k).indicator
      (fun ω' ↦ ‖run.step k ω'‖ ^ 2) ω

/-- Helper for Theorem 3.7: every sample path's active step energy is controlled
by the initial allowance and its active projected-gradient errors. -/
private lemma activeStepEnergyReal_le
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) (ω : Ω) :
    activeStepEnergyReal run X K ω ≤
      initialStepBound h params +
        errorStepConstant h params * activeErrorEnergyReal run X K ω := by
  -- Normalize both indicator sums to the single active prefix selected by the
  -- hitting time interface.
  have hKone : 1 ≤ K := by omega
  have hprefix := activePrefixLength_spec run X K hKone ω
  rw [activeStepEnergyReal,
    activePrefixSum_eq run X K hKone ω (fun k ω' ↦ ‖run.step k ω'‖ ^ 2),
    activeErrorEnergyReal,
    activePrefixSum_eq run X K hKone ω
      (fun k ω' ↦ ‖run.gradientError k ω'‖ ^ 2)]
  by_cases hprefixTwo : 2 ≤ activePrefixLength run X K ω
  · have hlastLtK : activePrefixLength run X K ω - 1 < K := by omega
    have hsurvival :
        ω ∈ survivalEvent run X (activePrefixLength run X K ω - 1) :=
      (hprefix.2.2 _ hlastLtK).mp (by omega)
    exact sumStepSq_le_of_survival (activePrefixLength run X K ω)
      hprefixTwo X initial_mem run h_region ω hsurvival
  · have hprefixEq : activePrefixLength run X K ω = 1 := by omega
    rw [hprefixEq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hzeroActive : ω ∈ survivalEvent run X 0 :=
      (hprefix.2.2 0 (by omega)).mp (by omega)
    have hstep := preExitStepNorm_le run X initial_mem h_region ω 0 hzeroActive
    have hstepSq : ‖run.step 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
    have hgap := initialPotentialGap_nonneg X initial_mem h_region
    have hcoefficient : 0 ≤ errorStepConstant h params :=
      (errorStepConstant_pos (h := h) (params := params)).le
    have herrorNonneg : 0 ≤ ‖run.gradientError 0 ω‖ ^ 2 := sq_nonneg _
    have hgapContribution :
        0 ≤ 4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by
      positivity
    have herrorContribution :
        0 ≤ errorStepConstant h params * ‖run.gradientError 0 ω‖ ^ 2 :=
      mul_nonneg hcoefficient herrorNonneg
    rw [initialStepBound_def]
    linarith

/-- Helper for Theorem 3.7: integration of the active-prefix estimate gives the
first stopped step/error coupling inequality. -/
private lemma stoppedStepEnergy_le
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) :
    stoppedStepEnergy run X K ≤
      initialStepBound h params +
        errorStepConstant h params * stoppedErrorEnergy run X K := by
  -- Each indicator term is integrable on the null-measurable survival event.
  have hstepTerm (k : ℕ) : Integrable
      ((survivalEvent run X k).indicator
        (fun ω ↦ ‖run.step k ω‖ ^ 2)) ℙ :=
    (integrableOn_stepSquare_preExit run X hX initial_mem h_region k).integrable_indicator₀
      (nullMeasurableSet_survivalEvent run X hX k)
  have herrorTerm (k : ℕ) : Integrable
      ((survivalEvent run X k).indicator
        (fun ω ↦ ‖run.gradientError k ω‖ ^ 2)) ℙ :=
    (integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k).integrable_indicator₀
      (nullMeasurableSet_survivalEvent run X hX k)
  have hstepIntegrable : Integrable (activeStepEnergyReal run X K) ℙ := by
    unfold activeStepEnergyReal
    exact integrable_finsetSum (Finset.range K) fun k _hk ↦ hstepTerm k
  have herrorIntegrable : Integrable (activeErrorEnergyReal run X K) ℙ := by
    unfold activeErrorEnergyReal
    exact integrable_finsetSum (Finset.range K) fun k _hk ↦ herrorTerm k
  have hstepIntegral :
      (∫ ω, activeStepEnergyReal run X K ω ∂ℙ) =
        stoppedStepEnergy run X K := by
    unfold activeStepEnergyReal stoppedStepEnergy
    rw [integral_finsetSum (Finset.range K) (fun k _hk ↦ hstepTerm k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_indicator₀ (nullMeasurableSet_survivalEvent run X hX k)]
  have herrorIntegral :
      (∫ ω, activeErrorEnergyReal run X K ω ∂ℙ) =
        stoppedErrorEnergy run X K := by
    unfold activeErrorEnergyReal stoppedErrorEnergy
    rw [integral_finsetSum (Finset.range K) (fun k _hk ↦ herrorTerm k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_indicator₀ (nullMeasurableSet_survivalEvent run X hX k)]
  have hrhsIntegrable : Integrable
      (fun ω ↦ initialStepBound h params +
        errorStepConstant h params * activeErrorEnergyReal run X K ω) ℙ :=
    (integrable_const _).add
      (herrorIntegrable.const_mul (errorStepConstant h params))
  -- Integrate the pathwise inequality and identify the two finite sums.
  calc
    stoppedStepEnergy run X K =
        ∫ ω, activeStepEnergyReal run X K ω ∂ℙ := hstepIntegral.symm
    _ ≤ ∫ ω, (initialStepBound h params +
        errorStepConstant h params * activeErrorEnergyReal run X K ω) ∂ℙ :=
      integral_mono hstepIntegrable hrhsIntegrable
        (activeStepEnergyReal_le K hK X initial_mem run h_region)
    _ = initialStepBound h params +
        errorStepConstant h params * stoppedErrorEnergy run X K := by
      rw [integral_add (integrable_const _)
          (herrorIntegrable.const_mul (errorStepConstant h params)),
        integral_const_mul, integral_const, Measure.real, measure_univ,
        ENNReal.toReal_one, one_smul, herrorIntegral]

/-- Helper for Theorem 3.7: the positive-definite linear operator in the
quadratic stochastic step model. -/
private noncomputable def modelStepOperator
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  beta • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) +
    rho • (EqualityConstrained.constraintGradient c x).comp (fderiv ℝ c x)

/-- Helper for Theorem 3.7: positivity of the proximal coefficient makes the
quadratic model operator continuously invertible. -/
private lemma modelStepOperator_isInvertible
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    (modelStepOperator c rho beta x).IsInvertible := by
  -- Pairing the kernel equation with its argument exposes two nonnegative
  -- squared norms, one with the strictly positive proximal coefficient.
  have hinjective : Function.Injective (modelStepOperator c rho beta x) := by
    intro p q hpq
    let v : EuclideanSpace ℝ (Fin n) := p - q
    have hvKernel : modelStepOperator c rho beta x v = 0 := by
      dsimp only [v]
      rw [map_sub, hpq, sub_self]
    have hpair :
        inner ℝ (modelStepOperator c rho beta x v) v =
          beta * ‖v‖ ^ 2 + rho * ‖fderiv ℝ c x v‖ ^ 2 := by
      simp only [modelStepOperator, add_apply, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
        EqualityConstrained.constraintGradient_def]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
        ContinuousLinearMap.adjoint_inner_left,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have hsum : beta * ‖v‖ ^ 2 + rho * ‖fderiv ℝ c x v‖ ^ 2 = 0 := by
      rw [← hpair, hvKernel, inner_zero_left]
    have hfirstNonnegative : 0 ≤ beta * ‖v‖ ^ 2 :=
      mul_nonneg hbeta.le (sq_nonneg _)
    have hsecondNonnegative : 0 ≤ rho * ‖fderiv ℝ c x v‖ ^ 2 :=
      mul_nonneg hrho.le (sq_nonneg _)
    have hfirst : beta * ‖v‖ ^ 2 = 0 := by
      linarith
    have hvNorm : ‖v‖ = 0 := by
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hfirst).resolve_left hbeta.ne')
    exact sub_eq_zero.mp (norm_eq_zero.mp hvNorm)
  -- Finite dimensionality upgrades injectivity to bijectivity, hence to a
  -- continuous linear equivalence representing the same operator.
  have hsurjective : Function.Surjective
      (modelStepOperator c rho beta x).toLinearMap :=
    LinearMap.surjective_of_injective hinjective
  let modelEquiv : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofBijective (modelStepOperator c rho beta x).toLinearMap
      ⟨hinjective, hsurjective⟩
  refine ⟨modelEquiv.toContinuousLinearEquiv, ?_⟩
  ext p
  rfl

/-- Helper for Theorem 3.7: the canonical stochastic model step is obtained by
solving its positive-definite first-order equation. -/
private noncomputable def canonicalModelStep
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  (modelStepOperator c rho beta x).inverse
    (-(g + EqualityConstrained.constraintGradient c x
      (multiplier + rho • c x)))

/-- Helper for Theorem 3.7: every minimizing stochastic model step equals the
canonical inverse-based step. -/
private lemma canonicalModelStep_eq_of_minimizes
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (rho beta : ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) (hrho : 0 < rho) (hbeta : 0 < beta)
    (hp : IsMinOn (stepModelWithGradient c g rho beta x multiplier)
      Set.univ p) :
    canonicalModelStep c rho beta x g multiplier = p := by
  -- Reassociate the first-order equation into the canonical operator equation.
  have hoptimal := explicitGradientModelOptimality c g rho beta x multiplier p hp
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
  -- Invertibility turns that operator equation into equality with its solution.
  unfold canonicalModelStep
  exact ((modelStepOperator_isInvertible c rho beta x hrho hbeta).inverse_apply_eq).2
    hoperator.symm

/-- Helper for Theorem 3.7: model inputs whose current point lies in the
regularity region. -/
private def modelStepRegularityDomain (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))) :=
  {z | z.1 ∈ h.region}

/-- Helper for Theorem 3.7: the model-step regularity domain is open. -/
private lemma isOpen_modelStepRegularityDomain
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (modelStepRegularityDomain h) :=
  h.isOpen_region.preimage continuous_fst

/-- Helper for Theorem 3.7: the canonical stochastic model solver is continuous
while its current point remains in the regularity region. -/
private lemma continuousOn_canonicalModelStep
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      canonicalModelStep c rho beta z.1 z.2.1 z.2.2)
      (modelStepRegularityDomain h) := by
  intro z hz
  change z.1 ∈ h.region at hz
  have hConstraintFDeriv : ContinuousAt (fderiv ℝ c) z.1 :=
    h.continuousOn_constraintFDeriv.continuousAt
      (h.isOpen_region.mem_nhds hz)
  have hConstraintGradient :
      ContinuousAt (EqualityConstrained.constraintGradient c) z.1 :=
    h.continuousAt_constraintGradient hz
  have hConstraint : ContinuousAt c z.1 :=
    h.continuousAt_constraint hz
  have hOperator : ContinuousAt (fun x ↦ modelStepOperator c rho beta x) z.1 := by
    unfold modelStepOperator
    exact (ContinuousAt.const_smul continuousAt_const beta).add
      (ContinuousAt.const_smul
        (hConstraintGradient.clm_comp hConstraintFDeriv) rho)
  have hInverse : ContinuousAt
      (fun x ↦ (modelStepOperator c rho beta x).inverse) z.1 :=
    ((modelStepOperator_isInvertible c rho beta z.1 hrho hbeta
      |>.contDiffAt_map_inverse (n := 0)).continuousAt.comp hOperator)
  have hRight : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ↦
      -(z.2.1 + EqualityConstrained.constraintGradient c z.1
        (z.2.2 + rho • c z.1))) z := by
    exact (continuous_fst.continuousAt.comp continuous_snd.continuousAt).add
      ((hConstraintGradient.comp continuous_fst.continuousAt).clm_apply
        ((continuous_snd.continuousAt.comp continuous_snd.continuousAt).add
          (ContinuousAt.const_smul
            (hConstraint.comp continuous_fst.continuousAt) rho))) |>.neg
  unfold canonicalModelStep
  exact ((hInverse.comp continuous_fst.continuousAt).clm_apply hRight).continuousWithinAt

/-- Helper for Theorem 3.7: the canonical model solver extended by zero outside
the model-step regularity domain. -/
private noncomputable def canonicalModelStepExtension
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ) :
    EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →
      EuclideanSpace ℝ (Fin n) :=
  @Set.piecewise _ _ (modelStepRegularityDomain h)
    (fun z ↦ canonicalModelStep c rho beta z.1 z.2.1 z.2.2) (fun _ ↦ 0)
    (fun z ↦ Classical.propDecidable (z ∈ modelStepRegularityDomain h))

/-- Helper for Theorem 3.7: the extended solver agrees with the canonical
solver at every regular current point. -/
private lemma canonicalModelStepExtension_eq
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    {z : EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))}
    (hz : z.1 ∈ h.region) :
    canonicalModelStepExtension h rho beta z =
      canonicalModelStep c rho beta z.1 z.2.1 z.2.2 := by
  classical
  have hzDomain : z ∈ modelStepRegularityDomain h := hz
  simp only [canonicalModelStepExtension, Set.piecewise, if_pos hzDomain]

/-- Helper for Theorem 3.7: the zero extension of the canonical model solver is
globally measurable. -/
private lemma measurable_canonicalModelStepExtension
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    (hrho : 0 < rho) (hbeta : 0 < beta) :
    Measurable (canonicalModelStepExtension h rho beta) := by
  classical
  simpa only [canonicalModelStepExtension] using
    (continuousOn_canonicalModelStep h rho beta hrho hbeta).measurable_piecewise
      continuous_const.continuousOn
      (isOpen_modelStepRegularityDomain h).measurableSet

/-- Helper for Theorem 3.7: the state entering a localized batch consists of
its active flag, two consecutive points, multiplier, and preceding raw estimate. -/
private abbrev LocalizedPreBatchState :=
  ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

/-- Helper for Theorem 3.7: a batch and a pre-batch state determine the next
raw SPIDER estimate. -/
private noncomputable def canonicalRawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (point previousPoint previousRaw : EuclideanSpace ℝ (Fin n))
    (batch : ℕ → Ξ) : EuclideanSpace ℝ (Fin n) :=
  if k % Q = 0 then
    (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
      oracle.sampleGradient point (batch i)
  else
    previousRaw + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
      (oracle.sampleGradient point (batch i) -
        oracle.sampleGradient previousPoint (batch i))

/-- Helper for Theorem 3.7: radial clipping is a measurable operation on the
finite-dimensional gradient space. -/
private lemma measurable_spiderClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  -- Both branches are continuous, and the clipping branch is selected by a
  -- closed norm comparison.
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Theorem 3.7: the explicit raw-estimate update is measurable in
the numerical state and the fresh batch. -/
private lemma measurable_canonicalRawEstimateAt
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (fun z : LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
      canonicalRawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1
        z.1.2.2.2.2 z.2) := by
  -- Each finite sum is assembled from measurable evaluations of the oracle.
  have hpoint : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hpreviousPoint : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
        z.1.2.2.1) := by
    fun_prop
  have hpreviousRaw : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
        z.1.2.2.2.2) := by
    fun_prop
  have hsample (i : ℕ) : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  by_cases hrefresh : k % Q = 0
  · simp only [canonicalRawEstimateAt, if_pos hrefresh]
    exact (Finset.measurable_sum (Finset.range B) fun i _ ↦
      oracle.measurable_sampleGradient.comp
        (hpoint.prodMk (hsample i))).const_smul ((B : ℝ)⁻¹)
  · simp only [canonicalRawEstimateAt, if_neg hrefresh]
    exact hpreviousRaw.add
      ((Finset.measurable_sum (Finset.range b) fun i _ ↦
        (oracle.measurable_sampleGradient.comp
            (hpoint.prodMk (hsample i))).sub
          (oracle.measurable_sampleGradient.comp
            (hpreviousPoint.prodMk (hsample i)))).const_smul ((b : ℝ)⁻¹))

/-- Helper for Theorem 3.7: the next localization flag remains active exactly
when the preceding flag is active and the new point lies in the region. -/
private noncomputable def canonicalActiveFlag
    (X : Set (EuclideanSpace ℝ (Fin n))) (active : ℝ)
    (point : EuclideanSpace ℝ (Fin n)) : ℝ :=
  @ite ℝ (active = 1 ∧ point ∈ X) (Classical.propDecidable _) 1 0

/-- Helper for Theorem 3.7: the localization-flag update is measurable for a
measurable localization region. -/
private lemma measurable_canonicalActiveFlag (hX : MeasurableSet X) :
    Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦
      canonicalActiveFlag X z.1 z.2) := by
  -- Membership and equality define the measurable active branch.
  classical
  unfold canonicalActiveFlag
  apply Measurable.ite
  · exact ((measurableSet_singleton (1 : ℝ)).preimage measurable_fst).inter
      (hX.preimage measurable_snd)
  · exact measurable_const
  · exact measurable_const

/-- Helper for Theorem 3.7: the clipped estimate component is obtained from the
explicit raw-estimate transition. -/
private noncomputable def canonicalClippedEstimateAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  SPIDER.clip h.gradientBound
    (canonicalRawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1
      z.1.2.2.2.2 z.2)

/-- Helper for Theorem 3.7: the clipped-estimate component is measurable. -/
private lemma measurable_canonicalClippedEstimateAt (k : ℕ) :
    Measurable (canonicalClippedEstimateAt h oracle Q B b k) := by
  -- Measurable clipping follows the measurable raw-estimate transition.
  unfold canonicalClippedEstimateAt
  exact (measurable_spiderClip h.gradientBound).comp
    (measurable_canonicalRawEstimateAt oracle Q B b k)

/-- Helper for Theorem 3.7: the canonical model input groups the current point,
clipped estimate, and multiplier in the solver's argument order. -/
private noncomputable def canonicalModelInputAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (z.1.2.1, canonicalClippedEstimateAt h oracle Q B b k z,
    z.1.2.2.2.1)

/-- Helper for Theorem 3.7: the grouped canonical model input is measurable. -/
private lemma measurable_canonicalModelInputAt (k : ℕ) :
    Measurable (canonicalModelInputAt h oracle Q B b k) := by
  -- Assemble the three measurable model inputs in their canonical order.
  unfold canonicalModelInputAt
  have hpoint : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hmultiplier : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.2.1) := by
    fun_prop
  exact hpoint.prodMk
    ((measurable_canonicalClippedEstimateAt k).prodMk hmultiplier)

/-- Helper for Theorem 3.7: the canonical step component applies the explicit
model solver to the grouped pre-batch model input. -/
private noncomputable def canonicalStepAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ) :
    LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) →
      EuclideanSpace ℝ (Fin n) :=
  canonicalModelStepExtension h params.rho params.beta ∘
      canonicalModelInputAt h oracle Q B b k

/-- Helper for Theorem 3.7: the canonical step component is measurable in the
pre-batch state and current batch. -/
private lemma measurable_canonicalStepAt (k : ℕ) :
    Measurable (canonicalStepAt h oracle params Q B b k) := by
  -- The definition is deliberately a literal composition of the two
  -- measurable interfaces.
  unfold canonicalStepAt
  exact (measurable_canonicalModelStepExtension h params.rho params.beta
    params.spec.1.2.2.1 params.spec.1.2.1).comp
      (measurable_canonicalModelInputAt k)

/-- Helper for Theorem 3.7: the canonical next point adds the explicit model
step to the current point. -/
private noncomputable def canonicalNextPointAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin n) :=
  z.1.2.1 + canonicalStepAt h oracle params Q B b k z

/-- Helper for Theorem 3.7: the canonical next-point component is measurable. -/
private lemma measurable_canonicalNextPointAt (k : ℕ) :
    Measurable (canonicalNextPointAt h oracle params Q B b k) := by
  -- Addition combines the measurable current point and canonical step.
  unfold canonicalNextPointAt
  have hpoint : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  exact hpoint.add (measurable_canonicalStepAt k)

/-- Helper for Theorem 3.7: the canonical next multiplier applies the LALM
dual update at the canonical next point. -/
private noncomputable def canonicalNextMultiplierAt
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+) (k : ℕ)
    (z : LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    EuclideanSpace ℝ (Fin m) :=
  z.1.2.2.2.1 + (params.toAdmissibleParameters.rho : ℝ) •
    h.constraintExtension (canonicalNextPointAt h oracle params Q B b k z)

/-- Helper for Theorem 3.7: the canonical next-multiplier component is
measurable. -/
private lemma measurable_canonicalNextMultiplierAt (k : ℕ) :
    Measurable (canonicalNextMultiplierAt h oracle params Q B b k) := by
  -- Compose the measurable next point with the global measurable constraint
  -- extension and the dual affine update.
  unfold canonicalNextMultiplierAt
  have hmultiplier : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.2.1) := by
    fun_prop
  exact hmultiplier.add
    ((h.measurable_constraintExtension.comp
      (measurable_canonicalNextPointAt k)).const_smul (params.rho : ℝ))

/-- Helper for Theorem 3.7: one fresh batch advances the explicit numerical
state and its localization flag. -/
private noncomputable def canonicalLocalizedTransition
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (z : LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) :
    LocalizedPreBatchState (n := n) (m := m) :=
  let nextActive := canonicalActiveFlag X z.1.1
    (canonicalNextPointAt h oracle params Q B b k z)
  @ite (LocalizedPreBatchState (n := n) (m := m)) (nextActive = 1)
    (Classical.propDecidable _)
    (nextActive, canonicalNextPointAt h oracle params Q B b k z, z.1.2.1,
      canonicalNextMultiplierAt h oracle params Q B b k z,
      canonicalRawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1
        z.1.2.2.2.2 z.2)
    0

/-- Helper for Theorem 3.7: the explicit localized transition is measurable in
the preceding state and fresh batch. -/
private lemma measurable_canonicalLocalizedTransition
    (hX : MeasurableSet X) (k : ℕ) :
    Measurable (canonicalLocalizedTransition h oracle params Q B b X k) := by
  -- The named transition pays for projection normalization once, leaving the
  -- recursive measurability proof as a single composition.
  unfold canonicalLocalizedTransition
  have hactive : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hpoint : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hraw := measurable_canonicalRawEstimateAt oracle Q B b k
  have hnextPoint := measurable_canonicalNextPointAt
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b) k
  have hnextMultiplier := measurable_canonicalNextMultiplierAt
    (h := h) (oracle := oracle) (params := params) (Q := Q) (B := B) (b := b) k
  have hnextActive : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
        canonicalActiveFlag X z.1.1
          (canonicalNextPointAt h oracle params Q B b k z)) :=
    (measurable_canonicalActiveFlag hX).comp (hactive.prodMk hnextPoint)
  -- Assemble the five fields on the active branch and freeze all numerical
  -- data after the first failed localization test.
  apply Measurable.ite
  · exact (measurableSet_singleton (1 : ℝ)).preimage hnextActive
  · exact hnextActive.prodMk
      (hnextPoint.prodMk (hpoint.prodMk (hnextMultiplier.prodMk hraw)))
  · exact measurable_const

/-- Helper for Theorem 3.7: the localized pre-batch state is recursively
generated from exactly the batches preceding its index. -/
private noncomputable def canonicalLocalizedPreBatchState
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (Q B b : ℕ+)
    (X : Set (EuclideanSpace ℝ (Fin n))) :
    (k : ℕ) → ((Fin k) → ℕ → Ξ) →
      LocalizedPreBatchState (n := n) (m := m)
  | 0, _ => (1, x₀, x₀, multiplier₀, 0)
  | k + 1, samples =>
      canonicalLocalizedTransition h oracle params Q B b X k
        (canonicalLocalizedPreBatchState h oracle params Q B b X k
          (fun t i ↦ samples t.castSucc i), samples (Fin.last k))

/-- Helper for Theorem 3.7: the canonical localized state is measurable as a
function of its finite history of preceding batches. -/
private lemma measurable_canonicalLocalizedPreBatchState
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (k : ℕ) :
    Measurable (canonicalLocalizedPreBatchState h oracle params Q B b X k) := by
  -- Inductively compose the measurable transition with the restriction to the
  -- preceding history and the last batch projection.
  induction k with
  | zero =>
      simpa only [canonicalLocalizedPreBatchState] using
        (measurable_const : Measurable (fun _ : (Fin 0 → ℕ → Ξ) ↦
          ((1, x₀, x₀, multiplier₀, 0) :
            LocalizedPreBatchState (n := n) (m := m))))
  | succ k ih =>
      let restrictHistory : (Fin (k + 1) → ℕ → Ξ) → Fin k → ℕ → Ξ :=
        fun samples t i ↦ samples t.castSucc i
      have hrestrictHistory : Measurable restrictHistory := by
        apply measurable_pi_lambda
        intro t
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i).comp (measurable_pi_apply t.castSucc)
      have hstate : Measurable (fun samples ↦
          canonicalLocalizedPreBatchState h oracle params Q B b X k
            (restrictHistory samples)) :=
        ih.comp hrestrictHistory
      have hbatch : Measurable (fun samples : Fin (k + 1) → ℕ → Ξ ↦
          samples (Fin.last k)) := measurable_pi_apply (Fin.last k)
      -- Apply the standalone measurable transition to the measurable history
      -- restriction and last batch.
      simpa only [canonicalLocalizedPreBatchState, restrictHistory,
        Function.comp_def] using
        (measurable_canonicalLocalizedTransition (h := h) (oracle := oracle)
          (params := params) (Q := Q) (B := B) (b := b) hX k).comp
            (hstate.prodMk hbatch)

/-- Helper for Theorem 3.7: the canonical raw transition reproduces the stored
SPIDER raw estimate on every sample path. -/
private lemma canonicalRawEstimateAt_apply_samples
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    canonicalRawEstimateAt oracle Q B b k (run.point k omega)
        (run.point (k - 1) omega)
        (if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) omega)
        (fun i ↦ run.sample k i omega) =
      SPIDER.rawEstimate oracle run.point run.sample Q B b k omega := by
  -- The two branches are exactly the public refresh and update equations.
  by_cases hrefresh : k % Q = 0
  · rw [canonicalRawEstimateAt, if_pos hrefresh,
      SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b k omega hrefresh]
  · have hkPositive : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkZero
      apply hrefresh
      simp only [hkZero, Nat.zero_mod]
    have hkPredSucc : k - 1 + 1 = k := by omega
    have hnonrefreshPred : (k - 1 + 1) % Q ≠ 0 := by
      simpa only [hkPredSucc] using hrefresh
    rw [canonicalRawEstimateAt, if_neg hrefresh, if_neg (ne_of_gt hkPositive),
      ← hkPredSucc,
      SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b (k - 1) omega
        hnonrefreshPred]
    simp only [hkPredSucc]

/-- Helper for Theorem 3.7: survival at a successor horizon is previous
survival together with membership of the new point in the localization set. -/
private lemma mem_survivalEvent_succ_iff
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω) :
    omega ∈ survivalEvent run X (k + 1) ↔
      omega ∈ survivalEvent run X k ∧ run.point (k + 1) omega ∈ X := by
  -- Split the interval `1, ..., k + 1` at its last index.
  rw [mem_survivalEvent, mem_survivalEvent]
  constructor
  · intro hsurvival
    constructor
    · intro j hj
      rcases hj with ⟨hjOne, hjTop⟩
      exact hsurvival j ⟨hjOne, Nat.le.step hjTop⟩
    · exact hsurvival (k + 1) ⟨Nat.succ_pos k, le_rfl⟩
  · rintro ⟨hprevious, hlast⟩ j hj
    rcases hj with ⟨hjOne, hjTop⟩
    by_cases hjPrevious : j ≤ k
    · exact hprevious j ⟨hjOne, hjPrevious⟩
    · have hjLast : j = k + 1 := by omega
      simpa only [hjLast] using hlast

/-- Helper for Theorem 3.7: survival through horizon zero is automatic. -/
private lemma mem_survivalEvent_zero
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (omega : Ω) :
    omega ∈ survivalEvent run X 0 := by
  -- The defining interval from one through zero is empty.
  rw [mem_survivalEvent]
  intro j hj
  rcases hj with ⟨hjOne, hjZero⟩
  omega

/-- Helper for Theorem 3.7: the actual localized pre-batch state packages the
survival indicator with the numerical state fixed before the fresh batch. -/
private noncomputable def localizedPreBatchState
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (omega : Ω) :
    LocalizedPreBatchState (n := n) (m := m) :=
  (survivalEvent run X k).indicator
    (fun omega ↦
      ((1 : ℝ), run.point k omega, run.point (k - 1) omega,
        run.multiplier k omega,
        if k = 0 then 0 else
          SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) omega)) omega

/-- Helper for Theorem 3.7: evaluating the canonical recursion on the run's
sample history gives its actual localized pre-batch state. -/
private lemma canonicalLocalizedPreBatchState_apply_samples
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (omega : Ω) :
    canonicalLocalizedPreBatchState h oracle params Q B b X k
        (fun t i ↦ run.sample t i omega) =
      localizedPreBatchState run X k omega := by
  -- The canonical recursion agrees with the run while active and freezes all
  -- numerical fields after the first failed localization test.
  classical
  induction k with
  | zero =>
      rw [canonicalLocalizedPreBatchState, localizedPreBatchState]
      rw [Set.indicator_of_mem (mem_survivalEvent_zero run X omega)]
      rw [run.point_zero, run.multiplier_zero]
      simp only [Nat.zero_sub]
      simp only [if_true]
  | succ k ih =>
      have hprevious :
          canonicalLocalizedPreBatchState h oracle params Q B b X k
              (fun t i ↦ run.sample t i omega) =
            localizedPreBatchState run X k omega := ih
      by_cases hsurvival : omega ∈ survivalEvent run X k
      · have hsegment := preExitSegment run X initial_mem h_region omega k hsurvival
        have hcurrentRegion : run.point k omega ∈ h.region :=
          hsegment (left_mem_segment ℝ _ _)
        have hnextRegion : run.point (k + 1) omega ∈ h.region :=
          hsegment (right_mem_segment ℝ _ _)
        have hraw := canonicalRawEstimateAt_apply_samples run k omega
        have hrawStep :
            canonicalModelStep c params.rho params.beta (run.point k omega)
                (SPIDER.clip h.gradientBound
                  (SPIDER.rawEstimate oracle run.point run.sample Q B b k omega))
                (run.multiplier k omega) = run.step k omega := by
          simpa only [SPIDER.estimate_apply] using
            canonicalModelStep_eq_of_minimizes c params.rho params.beta
              (run.point k omega)
              (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k omega)
              (run.multiplier k omega) (run.step k omega)
              params.spec.1.2.2.1 params.spec.1.2.1 (run.minimizes_step k omega)
        have hstep :
            canonicalModelStepExtension h params.rho params.beta
                (run.point k omega,
                  SPIDER.clip h.gradientBound
                    (SPIDER.rawEstimate oracle run.point run.sample Q B b k omega),
                  run.multiplier k omega) = run.step k omega := by
          rw [canonicalModelStepExtension_eq h params.rho params.beta hcurrentRegion]
          exact hrawStep
        have hconstraint := h.constraintExtension_eq hnextRegion
        have hmultiplier :
            run.multiplier (k + 1) omega = run.multiplier k omega +
              (params.toAdmissibleParameters.rho : ℝ) •
                c (run.point (k + 1) omega) := by
          simpa only [positivePenaltyParameters_rho] using
            run.multiplier_succ k omega
        by_cases hnext : run.point (k + 1) omega ∈ X
        · have hsuccessor : omega ∈ survivalEvent run X (k + 1) :=
            (mem_survivalEvent_succ_iff run X k omega).2 ⟨hsurvival, hnext⟩
          rw [canonicalLocalizedPreBatchState, canonicalLocalizedTransition]
          simp only [Fin.val_castSucc, Fin.val_last, hprevious,
            localizedPreBatchState, Set.indicator_of_mem hsurvival,
            canonicalNextMultiplierAt, canonicalNextPointAt, canonicalStepAt,
            canonicalModelInputAt, canonicalClippedEstimateAt, Function.comp_apply,
            hraw, hstep, ← run.point_succ k omega, hconstraint, ← hmultiplier,
            canonicalActiveFlag, hnext, and_self, if_true,
            Set.indicator_of_mem hsuccessor, Nat.succ_ne_zero, if_false,
            Nat.add_sub_cancel]
        · have hsuccessor : omega ∉ survivalEvent run X (k + 1) := by
            intro hmem
            exact hnext ((mem_survivalEvent_succ_iff run X k omega).1 hmem).2
          rw [canonicalLocalizedPreBatchState, canonicalLocalizedTransition]
          simp only [Fin.val_castSucc, Fin.val_last, hprevious,
            localizedPreBatchState, Set.indicator_of_mem hsurvival,
            canonicalNextMultiplierAt, canonicalNextPointAt, canonicalStepAt,
            canonicalModelInputAt, canonicalClippedEstimateAt, Function.comp_apply,
            hraw, hstep, ← run.point_succ k omega, canonicalActiveFlag, hnext,
            and_false, if_false, Set.indicator_of_notMem hsuccessor]
          simp
      · have hsuccessor : omega ∉ survivalEvent run X (k + 1) := by
          intro hmem
          exact hsurvival ((mem_survivalEvent_succ_iff run X k omega).1 hmem).1
        rw [canonicalLocalizedPreBatchState, canonicalLocalizedTransition]
        simp only [Fin.val_castSucc, Fin.val_last, hprevious,
          localizedPreBatchState, Set.indicator_of_notMem hsurvival,
          Set.indicator_of_notMem hsuccessor]
        simp [canonicalActiveFlag]

/-- Helper for Theorem 3.7: each oracle-sample coordinate has a canonical
measurable version. -/
private noncomputable def measurableSampleCoordinate
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) : Ω → Ξ :=
  (run.hasLaw_sample ki.1 ki.2).aemeasurable.mk
    (run.sample ki.1 ki.2)

/-- Helper for Theorem 3.7: the canonical version of every sample coordinate
is measurable. -/
private lemma measurable_measurableSampleCoordinate
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) : Measurable (measurableSampleCoordinate run ki) := by
  -- This is the defining property of the measurable modification.
  exact (run.hasLaw_sample ki.1 ki.2).aemeasurable.measurable_mk

/-- Helper for Theorem 3.7: each canonical measurable coordinate agrees almost
everywhere with the corresponding run sample. -/
private lemma measurableSampleCoordinate_ae_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) :
    measurableSampleCoordinate run ki =ᵐ[ℙ] run.sample ki.1 ki.2 := by
  -- Orient the standard modification identity toward the original sample.
  exact (run.hasLaw_sample ki.1 ki.2).aemeasurable.ae_eq_mk.symm

/-- Helper for Theorem 3.7: measurable modification preserves mutual
independence of the full sample-coordinate family. -/
private lemma iIndepFun_measurableSampleCoordinate
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) :
    ProbabilityTheory.iIndepFun
      (fun ki : ℕ × ℕ ↦ measurableSampleCoordinate run ki) ℙ := by
  -- Transfer independence coordinatewise along almost-everywhere equality.
  exact ProbabilityTheory.iIndepFun.congr
    (fun ki ↦ (measurableSampleCoordinate_ae_eq run ki).symm)
    run.independent_sample

/-- Helper for Theorem 3.7: the sigma-algebra of one measurable sample
coordinate is its codomain sigma-algebra pulled back to the sample space. -/
private noncomputable abbrev sampleCoordinateSigma
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) : MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace Ξ).comap
    (measurableSampleCoordinate run ki)

/-- Helper for Theorem 3.7: every measurable coordinate sigma-algebra lies
below the ambient sample-space sigma-algebra. -/
private lemma sampleCoordinateSigma_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (ki : ℕ × ℕ) :
    sampleCoordinateSigma run ki ≤ (inferInstance : MeasurableSpace Ω) := by
  -- Ambient measurability is precisely the required comap inequality.
  unfold sampleCoordinateSigma
  exact (measurable_measurableSampleCoordinate run ki).comap_le

/-- Helper for Theorem 3.7: the measurable coordinate sigma-algebras are
mutually independent. -/
private lemma iIndep_sampleCoordinateSigma
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) :
    ProbabilityTheory.iIndep (fun ki : ℕ × ℕ ↦
      sampleCoordinateSigma run ki) ℙ := by
  -- Independence of functions is independence of their pulled-back spaces.
  simpa only [sampleCoordinateSigma] using
    (iIndepFun_measurableSampleCoordinate run).iIndep

/-- Helper for Theorem 3.7: indices with time strictly before `k`. -/
private def pastSampleIndexSet (k : ℕ) : Set (ℕ × ℕ) :=
  {ki | ki.1 < k}

/-- Helper for Theorem 3.7: all indices in the batch at time `k`. -/
private def currentSampleIndexSet (k : ℕ) : Set (ℕ × ℕ) :=
  {ki | ki.1 = k}

/-- Helper for Theorem 3.7: past and current-batch sample indices are
disjoint. -/
private lemma pastSampleIndexSet_disjoint_currentSampleIndexSet (k : ℕ) :
    Disjoint (pastSampleIndexSet k) (currentSampleIndexSet k) := by
  -- Their first coordinates would otherwise be both below and equal to `k`.
  rw [Set.disjoint_left]
  rintro ⟨t, i⟩ htPast htCurrent
  simp only [pastSampleIndexSet, Set.mem_setOf_eq] at htPast
  simp only [currentSampleIndexSet, Set.mem_setOf_eq] at htCurrent
  omega

/-- Helper for Theorem 3.7: the past-sample sigma-algebra is generated by all
coordinates whose time is strictly before `k`. -/
private noncomputable abbrev pastSampleSigma
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    MeasurableSpace Ω :=
  ⨆ ki ∈ pastSampleIndexSet k, sampleCoordinateSigma run ki

/-- Helper for Theorem 3.7: the current-batch sigma-algebra is generated by all
sample coordinates at time `k`. -/
private noncomputable abbrev currentSampleSigma
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    MeasurableSpace Ω :=
  ⨆ ki ∈ currentSampleIndexSet k, sampleCoordinateSigma run ki

/-- Helper for Theorem 3.7: the measurable finite history contains all
modified sample batches strictly before `k`. -/
private noncomputable def measurablePastSampleHistory
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → Fin k → ℕ → Ξ :=
  fun omega t i ↦ measurableSampleCoordinate run (t, i) omega

/-- Helper for Theorem 3.7: the measurable current batch contains every
modified coordinate at time `k`. -/
private noncomputable def measurableCurrentSampleBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    Ω → ℕ → Ξ :=
  fun omega i ↦ measurableSampleCoordinate run (k, i) omega

/-- Helper for Theorem 3.7: the modified finite history is measurable with
respect to the sigma-algebra generated by past sample coordinates. -/
private lemma measurable_measurablePastSampleHistory
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    Measurable[pastSampleSigma run k] (measurablePastSampleHistory run k) := by
  -- Expand the two function-space comaps; every coordinate is one generator
  -- of the past sigma-algebra.
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro t
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  have hmem : ((t : ℕ), i) ∈ pastSampleIndexSet k := by
    simp only [pastSampleIndexSet, Set.mem_setOf_eq]
    exact t.isLt
  unfold measurablePastSampleHistory pastSampleSigma sampleCoordinateSigma
  exact le_iSup_of_le ((t : ℕ), i) (le_iSup_of_le hmem le_rfl)

/-- Helper for Theorem 3.7: the modified current batch is measurable with
respect to the sigma-algebra generated at time `k`. -/
private lemma measurable_measurableCurrentSampleBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    Measurable[currentSampleSigma run k]
      (measurableCurrentSampleBatch run k) := by
  -- Expand the function-space comap; every coordinate is one generator of the
  -- current-batch sigma-algebra.
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_process_pi]
  apply iSup_le
  intro i
  have hmem : (k, i) ∈ currentSampleIndexSet k := by
    simp only [currentSampleIndexSet, Set.mem_setOf_eq]
  unfold measurableCurrentSampleBatch currentSampleSigma sampleCoordinateSigma
  exact le_iSup_of_le (k, i) (le_iSup_of_le hmem le_rfl)

/-- Helper for Theorem 3.7: the modified past history agrees almost everywhere
with the run's actual finite sample history. -/
private lemma measurablePastSampleHistory_ae_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    measurablePastSampleHistory run k =ᵐ[ℙ]
      (fun omega t i ↦ run.sample t i omega) := by
  -- Countability of `Fin k` and `ℕ` combines all coordinatewise identities.
  have hall : ∀ᵐ omega ∂ℙ, ∀ t : Fin k, ∀ i : ℕ,
      measurableSampleCoordinate run (t, i) omega =
        run.sample t i omega :=
    ae_all_iff.mpr (fun t ↦ ae_all_iff.mpr (fun i ↦
      measurableSampleCoordinate_ae_eq run (t, i)))
  filter_upwards [hall] with omega homega
  funext t i
  exact homega t i

/-- Helper for Theorem 3.7: the modified current batch agrees almost everywhere
with the run's actual batch at time `k`. -/
private lemma measurableCurrentSampleBatch_ae_eq
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    measurableCurrentSampleBatch run k =ᵐ[ℙ]
      (fun omega i ↦ run.sample k i omega) := by
  -- Countability of the batch index combines all coordinatewise identities.
  have hall : ∀ᵐ omega ∂ℙ, ∀ i : ℕ,
      measurableSampleCoordinate run (k, i) omega =
        run.sample k i omega :=
    ae_all_iff.mpr (fun i ↦ measurableSampleCoordinate_ae_eq run (k, i))
  filter_upwards [hall] with omega homega
  funext i
  exact homega i

/-- Helper for Theorem 3.7: the measurable past history is independent of the
measurable current batch. -/
private lemma indepFun_measurablePastHistory_currentBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    ProbabilityTheory.IndepFun (measurablePastSampleHistory run k)
      (measurableCurrentSampleBatch run k) ℙ := by
  -- Group the mutually independent coordinate sigma-algebras along the
  -- disjoint past/current partition.
  have hgrouped : ProbabilityTheory.Indep (pastSampleSigma run k)
      (currentSampleSigma run k) ℙ := by
    unfold pastSampleSigma currentSampleSigma
    exact ProbabilityTheory.indep_iSup_of_disjoint
      (sampleCoordinateSigma_le run)
      (iIndep_sampleCoordinateSigma run)
      (pastSampleIndexSet_disjoint_currentSampleIndexSet k)
  -- The two history maps generate sub-sigma-algebras of the grouped spaces.
  unfold ProbabilityTheory.IndepFun
  exact ProbabilityTheory.indep_of_indep_of_le hgrouped
    (measurable_measurablePastSampleHistory run k).comap_le
    (measurable_measurableCurrentSampleBatch run k).comap_le

/-- Helper for Theorem 3.7: the localized pre-batch state, including its
survival flag, is independent of the fresh oracle batch. -/
private lemma indepFun_localizedPreBatchState_freshBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    ProbabilityTheory.IndepFun (localizedPreBatchState run X k)
      (fun omega i ↦ run.sample k i omega) ℙ := by
  -- First transport grouped independence through the measurable recursive
  -- state while leaving the current batch unchanged.
  have hindependent : ProbabilityTheory.IndepFun
      (canonicalLocalizedPreBatchState h oracle params Q B b X k ∘
        measurablePastSampleHistory run k)
      (id ∘ measurableCurrentSampleBatch run k) ℙ :=
    (indepFun_measurablePastHistory_currentBatch run k).comp
      (measurable_canonicalLocalizedPreBatchState X hX k) measurable_id
  have hstateAE :
      canonicalLocalizedPreBatchState h oracle params Q B b X k ∘
          measurablePastSampleHistory run k =ᵐ[ℙ]
        localizedPreBatchState run X k := by
    filter_upwards [measurablePastSampleHistory_ae_eq run k] with omega homega
    rw [Function.comp_apply, homega,
      canonicalLocalizedPreBatchState_apply_samples run X initial_mem h_region k omega]
  have hbatchIdentity :
      id ∘ measurableCurrentSampleBatch run k =ᵐ[ℙ]
        (fun omega i ↦ run.sample k i omega) := by
    filter_upwards [measurableCurrentSampleBatch_ae_eq run k] with omega homega
    simpa only [Function.comp_apply, id_eq] using homega
  -- Finally replace both measurable versions by the actual run fields.
  exact hindependent.congr hstateAE hbatchIdentity

/-- Helper for Theorem 3.7: an integrable nonnegative function of two
independent random variables is bounded by an integrable pointwise section
bound. -/
private lemma independentPairIntegral_le
    {A : Type w} {D : Type x} [MeasurableSpace A] [MeasurableSpace D]
    (X : Ω → A) (Y : Ω → D) (phi : A × D → ℝ) (bound : A → ℝ)
    (h_independent : ProbabilityTheory.IndepFun X Y ℙ)
    (hX : AEMeasurable X ℙ) (hY : AEMeasurable Y ℙ)
    (hphi : AEMeasurable phi ((ℙ.map X).prod (ℙ.map Y)))
    (hphi_nonnegative : ∀ z, 0 ≤ phi z)
    (hsection : ∀ᵐ a ∂ℙ.map X, Integrable (fun d ↦ phi (a, d)) (ℙ.map Y))
    (hboundIntegrable : Integrable bound (ℙ.map X))
    (hbound : ∀ᵐ a ∂ℙ.map X, (∫ d, phi (a, d) ∂ℙ.map Y) ≤ bound a) :
    Integrable (fun omega ↦ phi (X omega, Y omega)) ℙ ∧
      (∫ omega, phi (X omega, Y omega) ∂ℙ) ≤
        ∫ a, bound a ∂ℙ.map X := by
  -- Integrate the absolute section bound first to establish product
  -- integrability without appealing to a conditional-expectation API.
  have hphiStrong := hphi.aestronglyMeasurable
  have hinnerMeasurable : AEStronglyMeasurable
      (fun a ↦ ∫ d, ‖phi (a, d)‖ ∂ℙ.map Y) (ℙ.map X) :=
    hphiStrong.norm.integral_prod_right'
  have hinnerIntegrable : Integrable
      (fun a ↦ ∫ d, ‖phi (a, d)‖ ∂ℙ.map Y) (ℙ.map X) := by
    apply Integrable.mono' hboundIntegrable hinnerMeasurable
    exact hbound.mono fun a ha ↦ by
      have hinnerNonnegative : 0 ≤ ∫ d, ‖phi (a, d)‖ ∂ℙ.map Y :=
        integral_nonneg fun d ↦ norm_nonneg _
      have hnormIntegral :
          (∫ d, ‖phi (a, d)‖ ∂ℙ.map Y) =
            ∫ d, phi (a, d) ∂ℙ.map Y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun d ↦ by
          simp only [Real.norm_eq_abs, abs_of_nonneg (hphi_nonnegative (a, d))]
      rw [Real.norm_eq_abs, abs_of_nonneg hinnerNonnegative, hnormIntegral]
      exact ha
  have hprod : Integrable phi ((ℙ.map X).prod (ℙ.map Y)) :=
    (integrable_prod_iff hphiStrong).2 ⟨hsection, hinnerIntegrable⟩
  have hpairMeasurable : AEMeasurable (fun omega ↦ (X omega, Y omega)) ℙ :=
    hX.prodMk hY
  have hmap :
      ℙ.map (fun omega ↦ (X omega, Y omega)) =
        (ℙ.map X).prod (ℙ.map Y) :=
    h_independent.map_prod_eq_prod_map_map hX hY
  have hphiMap : AEStronglyMeasurable phi
      (ℙ.map fun omega ↦ (X omega, Y omega)) := by
    rw [hmap]
    exact hphiStrong
  have hprodMap : Integrable phi
      (ℙ.map fun omega ↦ (X omega, Y omega)) := by
    rw [hmap]
    exact hprod
  have hcomp : Integrable (fun omega ↦ phi (X omega, Y omega)) ℙ :=
    (integrable_map_measure hphiMap hpairMeasurable).1 hprodMap
  refine ⟨hcomp, ?_⟩
  -- Independence identifies the joint law with the product law, where Fubini
  -- exposes the pointwise section estimate.
  calc
    (∫ omega, phi (X omega, Y omega) ∂ℙ) =
        ∫ z, phi z ∂ℙ.map (fun omega ↦ (X omega, Y omega)) := by
      exact (integral_map hpairMeasurable hphiMap).symm
    _ = ∫ z, phi z ∂(ℙ.map X).prod (ℙ.map Y) := by rw [hmap]
    _ = ∫ a, ∫ d, phi (a, d) ∂ℙ.map Y ∂ℙ.map X := integral_prod phi hprod
    _ ≤ ∫ a, bound a ∂ℙ.map X :=
      integral_mono_ae hprod.integral_prod_left hboundIntegrable hbound

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure ℙ] in
/-- Helper for Theorem 3.7: the squared norm of an average of independent,
identically distributed centered Euclidean vectors is bounded by the common
second moment divided by the batch size. -/
private lemma independentBatchMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ)
    (hvalue : Integrable value ν) (hmean : ∫ xi, value xi ∂ν = 0)
    (hsquare : Integrable (fun xi ↦ ‖value xi‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ xi, ‖value xi‖ ^ 2 ∂ν) ≤ secondMoment) :
    Integrable (fun omega ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2) ℙ ∧
      (∫ omega, ‖(batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2 ∂ℙ) ≤
          secondMoment / (batch : ℝ) := by
  classical
  have hvalueRandom (i : ℕ) :
      Integrable (fun omega ↦ value (sample i omega)) ℙ := by
    have hmap : Integrable value (ℙ.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hsquareRandom (i : ℕ) :
      Integrable (fun omega ↦ ‖value (sample i omega)‖ ^ 2) ℙ := by
    have hmap : Integrable (fun xi ↦ ‖value xi‖ ^ 2) (ℙ.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hmeanRandom (i : ℕ) :
      (∫ omega, value (sample i omega) ∂ℙ) = 0 := by
    -- Transport centering along the common sample law.
    simpa only [Function.comp_apply, hmean] using
      (hlaw i).integral_comp hvalue.aestronglyMeasurable
  have hsecondRandom (i : ℕ) :
      (∫ omega, ‖value (sample i omega)‖ ^ 2 ∂ℙ) ≤ secondMoment := by
    calc
      (∫ omega, ‖value (sample i omega)‖ ^ 2 ∂ℙ) =
          ∫ xi, ‖value xi‖ ^ 2 ∂ν := by
        simpa only [Function.comp_apply] using
          (hlaw i).integral_comp hsquare.aestronglyMeasurable
      _ ≤ secondMoment := hsecond
  have hindependentValue :
      ProbabilityTheory.iIndepFun (fun i omega ↦ value (sample i omega)) ℙ := by
    apply hindependent.comp₀ (fun _ ↦ value)
    · exact fun i ↦ (hlaw i).aemeasurable
    · intro i
      rw [(hlaw i).map_eq]
      exact hvalue.aemeasurable
  have hcrossIntegrable (i j : ℕ) : Integrable
      (fun omega ↦ inner ℝ (value (sample i omega)) (value (sample j omega))) ℙ := by
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hsquareRandom i
    · have hbilinear := (hindependentValue.indepFun hij).integrable_bilin
        (hvalueRandom i) (hvalueRandom j) (innerSL ℝ)
      exact hbilinear.congr (Filter.Eventually.of_forall fun omega ↦
        innerSL_apply_apply ℝ (value (sample i omega)) (value (sample j omega)))
  have hcrossIntegral (i j : ℕ) (hij : i ≠ j) :
      (∫ omega, inner ℝ (value (sample i omega))
        (value (sample j omega)) ∂ℙ) = 0 := by
    have hbilinear := (hindependentValue.indepFun hij).integral_bilin
      (hvalueRandom i) (hvalueRandom j) (innerSL ℝ)
    calc
      (∫ omega, inner ℝ (value (sample i omega))
          (value (sample j omega)) ∂ℙ) =
          ∫ omega, innerSL ℝ (value (sample i omega))
            (value (sample j omega)) ∂ℙ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega ↦
          (innerSL_apply_apply ℝ
            (value (sample i omega)) (value (sample j omega))).symm
      _ = innerSL ℝ (∫ omega, value (sample i omega) ∂ℙ)
            (∫ omega, value (sample j omega) ∂ℙ) := hbilinear
      _ = inner ℝ (∫ omega, value (sample i omega) ∂ℙ)
            (∫ omega, value (sample j omega) ∂ℙ) := by
        exact innerSL_apply_apply ℝ _ _
      _ = 0 := by rw [hmeanRandom i, hmeanRandom j, inner_zero_left]
  have havgIdentity (omega : Ω) :
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
          value (sample i omega)‖ ^ 2 =
        (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j omega)) (value (sample i omega)) := by
    -- Expand the squared norm into diagonal and cross terms.
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_smul_left, inner_smul_right, inner_sum, sum_inner,
      starRingEnd_apply, star_trivial]
    calc
      (batch : ℝ)⁻¹ * ∑ i ∈ Finset.range batch,
          (batch : ℝ)⁻¹ * ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j omega)) (value (sample i omega)) =
          ∑ i ∈ Finset.range batch,
            (batch : ℝ)⁻¹ * ((batch : ℝ)⁻¹ *
              ∑ j ∈ Finset.range batch,
                inner ℝ (value (sample j omega)) (value (sample i omega))) := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range batch, (batch : ℝ)⁻¹ ^ 2 *
            ∑ j ∈ Finset.range batch,
              inner ℝ (value (sample j omega)) (value (sample i omega)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            inner ℝ (value (sample j omega)) (value (sample i omega)) := by
        symm
        rw [Finset.mul_sum]
  have hdoubleIntegrable : Integrable (fun omega ↦
      ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
        inner ℝ (value (sample j omega)) (value (sample i omega))) ℙ :=
    integrable_finsetSum _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hcrossIntegrable j i
  have havgIntegrable : Integrable (fun omega ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        value (sample i omega)‖ ^ 2) ℙ :=
    (hdoubleIntegrable.const_mul ((batch : ℝ)⁻¹ ^ 2)).congr
      (Filter.Eventually.of_forall fun omega ↦ (havgIdentity omega).symm)
  refine ⟨havgIntegrable, ?_⟩
  -- Independence and centering kill every off-diagonal integral.
  calc
    (∫ omega, ‖(batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2 ∂ℙ) =
        (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch, ∑ j ∈ Finset.range batch,
            ∫ omega, inner ℝ (value (sample j omega))
              (value (sample i omega)) ∂ℙ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall havgIdentity),
        integral_const_mul, integral_finsetSum _ (fun i _ ↦
          integrable_finsetSum _ fun j _ ↦ hcrossIntegrable j i)]
      apply congrArg ((batch : ℝ)⁻¹ ^ 2 * ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ ↦ hcrossIntegrable j i)]
    _ = (batch : ℝ)⁻¹ ^ 2 *
          ∑ i ∈ Finset.range batch,
            ∫ omega, ‖value (sample i omega)‖ ^ 2 ∂ℙ := by
      apply congrArg ((batch : ℝ)⁻¹ ^ 2 * ·)
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega ↦
          real_inner_self_eq_norm_sq (value (sample i omega))
      · intro j hj hji
        exact hcrossIntegral j i hji
      · exact fun hiMissing ↦ (hiMissing hi).elim
    _ ≤ (batch : ℝ)⁻¹ ^ 2 *
          ∑ _i ∈ Finset.range batch, secondMoment := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ hsecondRandom i) (sq_nonneg _)
    _ = secondMoment / (batch : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hbatch : (batch : ℝ) ≠ 0 := by positivity
      field_simp

omit [IsProbabilityMeasure ν] in
/-- Helper for Theorem 3.7: shifting a centered independent batch average by a
deterministic vector adds its squared norm to the mean-square bound. -/
private lemma independentBatchShiftedMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ)
    (hvalue : Integrable value ν) (hmean : ∫ xi, value xi ∂ν = 0)
    (hsquare : Integrable (fun xi ↦ ‖value xi‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ xi, ‖value xi‖ ^ 2 ∂ν) ≤ secondMoment)
    (a : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun omega ↦
      ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2) ℙ ∧
      (∫ omega, ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2 ∂ℙ) ≤
          ‖a‖ ^ 2 + secondMoment / (batch : ℝ) := by
  classical
  let average : Ω → EuclideanSpace ℝ (Fin n) := fun omega ↦
    (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value (sample i omega)
  have hvalueRandom (i : ℕ) :
      Integrable (fun omega ↦ value (sample i omega)) ℙ := by
    have hmap : Integrable value (ℙ.map (sample i)) := by
      rwa [(hlaw i).map_eq]
    exact hmap.comp_aemeasurable (hlaw i).aemeasurable
  have hmeanRandom (i : ℕ) :
      (∫ omega, value (sample i omega) ∂ℙ) = 0 := by
    simpa only [Function.comp_apply, hmean] using
      (hlaw i).integral_comp hvalue.aestronglyMeasurable
  have hsum : Integrable
      (fun omega ↦ ∑ i ∈ Finset.range batch, value (sample i omega)) ℙ :=
    integrable_finsetSum _ fun i _ ↦ hvalueRandom i
  have haverage : Integrable average ℙ := by
    unfold average
    change Integrable
      ((batch : ℝ)⁻¹ •
        (fun omega ↦ ∑ i ∈ Finset.range batch, value (sample i omega))) ℙ
    exact hsum.smul ((batch : ℝ)⁻¹)
  have haverageMean : (∫ omega, average omega ∂ℙ) = 0 := by
    simp only [average]
    rw [integral_smul, integral_finsetSum _ (fun i _ ↦ hvalueRandom i)]
    simp only [hmeanRandom, Finset.sum_const_zero, smul_zero]
  have hbatch := independentBatchMeanSquare_le value sample batch hlaw hindependent
    hvalue hmean hsquare secondMoment hsecond
  have haverageSquare : Integrable (fun omega ↦ ‖average omega‖ ^ 2) ℙ := by
    simpa only [average] using hbatch.1
  have hinner : Integrable (fun omega ↦ inner ℝ a (average omega)) ℙ :=
    haverage.const_inner a
  have hexpanded : Integrable (fun omega ↦
      ‖a‖ ^ 2 + 2 * inner ℝ a (average omega) + ‖average omega‖ ^ 2) ℙ :=
    ((integrable_const _).add (hinner.const_mul 2)).add haverageSquare
  have hshifted : Integrable (fun omega ↦ ‖a + average omega‖ ^ 2) ℙ :=
    hexpanded.congr (Filter.Eventually.of_forall fun omega ↦
      (norm_add_sq_real a (average omega)).symm)
  have hshiftedExpanded : Integrable (fun omega ↦
      ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2) ℙ := by
    simpa only [average] using hshifted
  refine ⟨hshiftedExpanded, ?_⟩
  -- Expand the shifted norm and use that the average remains centered.
  calc
    (∫ omega, ‖a + (batch : ℝ)⁻¹ •
        ∑ i ∈ Finset.range batch, value (sample i omega)‖ ^ 2 ∂ℙ) =
        ∫ omega, (‖a‖ ^ 2 + 2 * inner ℝ a (average omega)) +
          ‖average omega‖ ^ 2 ∂ℙ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        simp only [average, norm_add_sq_real]
    _ = ‖a‖ ^ 2 + 2 * inner ℝ a (∫ omega, average omega ∂ℙ) +
          ∫ omega, ‖average omega‖ ^ 2 ∂ℙ := by
      calc
        (∫ omega, (‖a‖ ^ 2 + 2 * inner ℝ a (average omega)) +
            ‖average omega‖ ^ 2 ∂ℙ) =
            (∫ omega, ‖a‖ ^ 2 + 2 * inner ℝ a (average omega) ∂ℙ) +
              ∫ omega, ‖average omega‖ ^ 2 ∂ℙ :=
          integral_add ((integrable_const _).add (hinner.const_mul 2)) haverageSquare
        _ = ((∫ _omega, ‖a‖ ^ 2 ∂ℙ) +
              ∫ omega, 2 * inner ℝ a (average omega) ∂ℙ) +
              ∫ omega, ‖average omega‖ ^ 2 ∂ℙ := by
          rw [integral_add (integrable_const _) (hinner.const_mul 2)]
        _ = ‖a‖ ^ 2 + 2 * inner ℝ a (∫ omega, average omega ∂ℙ) +
              ∫ omega, ‖average omega‖ ^ 2 ∂ℙ := by
          rw [integral_const, integral_const_mul, integral_inner haverage a]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    _ = ‖a‖ ^ 2 + ∫ omega, ‖average omega‖ ^ 2 ∂ℙ := by
      rw [haverageMean]
      simp
    _ ≤ ‖a‖ ^ 2 + secondMoment / (batch : ℝ) := by
      have hbatchBound :
          (∫ omega, ‖average omega‖ ^ 2 ∂ℙ) ≤
            secondMoment / (batch : ℝ) := by
        simpa only [average] using hbatch.2
      exact add_le_add le_rfl hbatchBound

/-- Helper for Theorem 3.7: centering an integrable square-integrable Euclidean
random vector cannot increase its second moment. -/
private lemma centeredMeanSquare_le
    (value : Ξ → EuclideanSpace ℝ (Fin n))
    (mean : EuclideanSpace ℝ (Fin n))
    (hvalue : Integrable value ν) (hmean : ∫ xi, value xi ∂ν = mean)
    (hsquare : Integrable (fun xi ↦ ‖value xi‖ ^ 2) ν)
    (secondMoment : ℝ)
    (hsecond : (∫ xi, ‖value xi‖ ^ 2 ∂ν) ≤ secondMoment) :
    Integrable (fun xi ↦ ‖value xi - mean‖ ^ 2) ν ∧
      (∫ xi, ‖value xi - mean‖ ^ 2 ∂ν) ≤ secondMoment := by
  -- Expand the centered square and identify its cross term with the mean.
  have hinner : Integrable (fun xi ↦ inner ℝ (value xi) mean) ν :=
    hvalue.inner_const mean
  have hexpanded : Integrable (fun xi ↦
      ‖value xi‖ ^ 2 - 2 * inner ℝ (value xi) mean + ‖mean‖ ^ 2) ν :=
    (hsquare.sub (hinner.const_mul 2)).add (integrable_const _)
  have hcentered : Integrable (fun xi ↦ ‖value xi - mean‖ ^ 2) ν :=
    hexpanded.congr (Filter.Eventually.of_forall fun xi ↦
      (norm_sub_sq_real (value xi) mean).symm)
  refine ⟨hcentered, ?_⟩
  have hinnerIntegral :
      (∫ xi, inner ℝ (value xi) mean ∂ν) = ‖mean‖ ^ 2 := by
    calc
      (∫ xi, inner ℝ (value xi) mean ∂ν) =
          ∫ xi, inner ℝ mean (value xi) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun xi ↦ real_inner_comm _ _
      _ = inner ℝ mean (∫ xi, value xi ∂ν) := integral_inner hvalue mean
      _ = ‖mean‖ ^ 2 := by rw [hmean, real_inner_self_eq_norm_sq]
  calc
    (∫ xi, ‖value xi - mean‖ ^ 2 ∂ν) =
        (∫ xi, ‖value xi‖ ^ 2 ∂ν) - ‖mean‖ ^ 2 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun xi ↦
          norm_sub_sq_real (value xi) mean)]
      calc
        (∫ xi, (‖value xi‖ ^ 2 - 2 * inner ℝ (value xi) mean) +
            ‖mean‖ ^ 2 ∂ν) =
            (∫ xi, ‖value xi‖ ^ 2 - 2 * inner ℝ (value xi) mean ∂ν) +
              ∫ _xi, ‖mean‖ ^ 2 ∂ν :=
          integral_add (hsquare.sub (hinner.const_mul 2)) (integrable_const _)
        _ = ((∫ xi, ‖value xi‖ ^ 2 ∂ν) -
              ∫ xi, 2 * inner ℝ (value xi) mean ∂ν) +
              ∫ _xi, ‖mean‖ ^ 2 ∂ν := by
          rw [integral_sub hsquare (hinner.const_mul 2)]
        _ = (∫ xi, ‖value xi‖ ^ 2 ∂ν) - ‖mean‖ ^ 2 := by
          rw [integral_const_mul, hinnerIntegral, integral_const]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
          ring
    _ ≤ ∫ xi, ‖value xi‖ ^ 2 ∂ν := sub_le_self _ (sq_nonneg _)
    _ ≤ secondMoment := hsecond

/-- Helper for Theorem 3.7: subtracting a constant inside a positive-size
batch average subtracts that constant from the average. -/
private lemma batchAverage_sub
    (batch : ℕ+) (value : ℕ → EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) :
    (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, (value i - a) =
      (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch, value i - a := by
  -- Pull the constant through the finite average and cancel the positive size.
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub]
  have hbatch : (batch : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← mul_smul, inv_mul_cancel₀ hbatch, one_smul]

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Theorem 3.7: at a fixed point in the regularity region, an
independent refresh batch has centered mean square bounded by the oracle noise
variance divided by its size. -/
private lemma fixedPointRefreshBatchMeanSquare_le
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region)
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ) :
    Integrable (fun omega ↦
      ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        (oracle.sampleGradient x (sample i omega) - gradient f x)‖ ^ 2) ℙ ∧
      (∫ omega, ‖(batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        (oracle.sampleGradient x (sample i omega) - gradient f x)‖ ^ 2 ∂ℙ) ≤
          (oracle.noiseLevel : ℝ) ^ 2 / (batch : ℝ) := by
  have hunbiased := oracle.unbiased_spec x hx
  have hvariance := oracle.variance_spec x hx
  have hcentered : Integrable
      (fun xi ↦ oracle.sampleGradient x xi - gradient f x) ν :=
    hunbiased.1.sub (integrable_const _)
  have hcenteredMean :
      (∫ xi, oracle.sampleGradient x xi - gradient f x ∂ν) = 0 := by
    -- Unbiasedness centers each sample-gradient error.
    rw [integral_sub hunbiased.1 (integrable_const _), hunbiased.2, integral_const]
    simp
  exact independentBatchMeanSquare_le
    (fun xi ↦ oracle.sampleGradient x xi - gradient f x) sample batch
      hlaw hindependent hcentered hcenteredMean hvariance.1
        ((oracle.noiseLevel : ℝ) ^ 2) hvariance.2

/-- Helper for Theorem 3.7: at two fixed points in the regularity region, a
fresh update batch adds a centered innovation controlled by the oracle
mean-square Lipschitz constant. -/
private lemma fixedPointUpdateBatchMeanSquare_le
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ h.region)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ h.region)
    (a : EuclideanSpace ℝ (Fin n))
    (sample : ℕ → Ω → Ξ) (batch : ℕ+)
    (hlaw : ∀ i, ProbabilityTheory.HasLaw (sample i) ν ℙ)
    (hindependent : ProbabilityTheory.iIndepFun sample ℙ) :
    Integrable (fun omega ↦
      ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i omega) -
            oracle.sampleGradient y (sample i omega)) -
          (gradient f x - gradient f y))‖ ^ 2) ℙ ∧
      (∫ omega, ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i omega) -
            oracle.sampleGradient y (sample i omega)) -
          (gradient f x - gradient f y))‖ ^ 2 ∂ℙ) ≤
        ‖a‖ ^ 2 + (oracle.meanSquareLipschitz : ℝ) ^ 2 / (batch : ℝ) *
          ‖x - y‖ ^ 2 := by
  let difference : Ξ → EuclideanSpace ℝ (Fin n) := fun xi ↦
    oracle.sampleGradient x xi - oracle.sampleGradient y xi
  let meanDifference : EuclideanSpace ℝ (Fin n) := gradient f x - gradient f y
  let centered : Ξ → EuclideanSpace ℝ (Fin n) := fun xi ↦
    difference xi - meanDifference
  have hxUnbiased := oracle.unbiased_spec x hx
  have hyUnbiased := oracle.unbiased_spec y hy
  have hdifference : Integrable difference ν :=
    hxUnbiased.1.sub hyUnbiased.1
  have hdifferenceMean : (∫ xi, difference xi ∂ν) = meanDifference := by
    simp only [difference, meanDifference]
    rw [integral_sub hxUnbiased.1 hyUnbiased.1, hxUnbiased.2, hyUnbiased.2]
  have hlipschitz := oracle.meanSquareLipschitz_spec x hx y hy
  have hcenteredSquare := centeredMeanSquare_le difference meanDifference
    hdifference hdifferenceMean hlipschitz.1
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2) hlipschitz.2
  have hcentered : Integrable centered ν :=
    hdifference.sub (integrable_const _)
  have hcenteredMean : (∫ xi, centered xi ∂ν) = 0 := by
    simp only [centered]
    rw [integral_sub hdifference (integrable_const _), hdifferenceMean, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, sub_self]
  have hshifted := independentBatchShiftedMeanSquare_le centered sample batch hlaw
    hindependent hcentered hcenteredMean hcenteredSquare.1
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2)
      hcenteredSquare.2 a
  have hshiftedIntegrable : Integrable (fun omega ↦
      ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i omega) -
            oracle.sampleGradient y (sample i omega)) -
          (gradient f x - gradient f y))‖ ^ 2) ℙ := by
    simpa only [centered, difference, meanDifference] using hshifted.1
  refine ⟨hshiftedIntegrable, ?_⟩
  -- Normalize the scalar coefficient after applying the shifted batch estimate.
  calc
    (∫ omega, ‖a + (batch : ℝ)⁻¹ • ∑ i ∈ Finset.range batch,
        ((oracle.sampleGradient x (sample i omega) -
            oracle.sampleGradient y (sample i omega)) -
          (gradient f x - gradient f y))‖ ^ 2 ∂ℙ) ≤
        ‖a‖ ^ 2 + ((oracle.meanSquareLipschitz : ℝ) ^ 2 * ‖x - y‖ ^ 2) /
          (batch : ℝ) := by
      simpa only [centered, difference, meanDifference] using hshifted.2
    _ = ‖a‖ ^ 2 + (oracle.meanSquareLipschitz : ℝ) ^ 2 / (batch : ℝ) *
          ‖x - y‖ ^ 2 := by ring

/-- Helper for Theorem 3.7: the actual localized state has an almost-everywhere
measurable representative obtained from the finite past sample history. -/
private lemma aemeasurable_localizedPreBatchState
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    AEMeasurable (localizedPreBatchState run X k) ℙ := by
  -- Feed the almost-everywhere measurable actual history into the canonical
  -- measurable recursion, then use its pointwise specification.
  let past : Ω → Fin k → ℕ → Ξ := fun omega t i ↦ run.sample t i omega
  have hpast : AEMeasurable past ℙ := by
    apply aemeasurable_pi_lambda
    intro t
    apply aemeasurable_pi_lambda
    intro i
    exact (run.hasLaw_sample t i).aemeasurable
  have hcanonical : AEMeasurable
      (canonicalLocalizedPreBatchState h oracle params Q B b X k ∘ past) ℙ :=
    (measurable_canonicalLocalizedPreBatchState X hX k).comp_aemeasurable hpast
  have hspec :
      canonicalLocalizedPreBatchState h oracle params Q B b X k ∘ past =ᵐ[ℙ]
        localizedPreBatchState run X k := by
    exact Filter.Eventually.of_forall fun omega ↦ by
      simpa only [Function.comp_apply, past] using
        canonicalLocalizedPreBatchState_apply_samples run X initial_mem h_region k omega
  exact hcanonical.congr hspec

/-- Helper for Theorem 3.7: the current oracle batch is almost everywhere
measurable as a sample-valued process. -/
private lemma aemeasurable_freshBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    AEMeasurable (fun omega i ↦ run.sample k i omega) ℙ := by
  -- Assemble coordinatewise measurability through the product sigma-algebra.
  exact aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable

/-- Helper for Theorem 3.7: the sample coordinates within a fixed fresh batch
are mutually independent. -/
private lemma iIndepFun_freshBatch
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    ProbabilityTheory.iIndepFun (run.sample k) ℙ := by
  -- Restrict global coordinate independence along the injective current-time
  -- embedding.
  have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
    intro i j hij
    exact congrArg Prod.snd hij
  simpa only using run.independent_sample.precomp hinjective

/-- Helper for Theorem 3.7: the survival-masked squared raw SPIDER error at one
iteration. -/
private noncomputable def activeRawGradientErrorIntegrand
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Ω → ℝ :=
  (survivalEvent run X k).indicator (fun omega ↦
    ‖SPIDER.rawEstimate oracle run.point run.sample Q B b k omega -
      gradient f (run.point k omega)‖ ^ 2)

/-- Helper for Theorem 3.7: the expected survival-masked squared raw SPIDER
error at one iteration. -/
private noncomputable def activeRawGradientError
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ :=
  ∫ omega, activeRawGradientErrorIntegrand run X k omega ∂ℙ

/-- Helper for Theorem 3.7: the survival-masked squared primal step at one
iteration. -/
private noncomputable def activeStepSquareIntegrand
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Ω → ℝ :=
  (survivalEvent run X k).indicator (fun omega ↦ ‖run.step k omega‖ ^ 2)

/-- Helper for Theorem 3.7: each survival-masked squared step is integrable. -/
private lemma integrable_activeStepSquareIntegrand
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Integrable (activeStepSquareIntegrand run X k) ℙ := by
  unfold activeStepSquareIntegrand
  exact (integrableOn_stepSquare_preExit run X hX initial_mem h_region k).integrable_indicator₀
    (nullMeasurableSet_survivalEvent run X hX k)

/-- Helper for Theorem 3.7: the expected survival-masked squared step at one
iteration. -/
private noncomputable def activeStepMoment
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ :=
  ∫ omega, activeStepSquareIntegrand run X k omega ∂ℙ

/-- Helper for Theorem 3.7: every expected survival-masked squared step is
nonnegative. -/
private lemma activeStepMoment_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    0 ≤ activeStepMoment run X k := by
  -- The integrand is either zero or a squared norm.
  rw [activeStepMoment]
  exact integral_nonneg fun omega ↦ by
    unfold activeStepSquareIntegrand
    by_cases hsurvival : omega ∈ survivalEvent run X k
    · simp only [Set.indicator_of_mem hsurvival]
      positivity
    · simp only [Set.indicator_of_notMem hsurvival]
      exact le_rfl

/-- Helper for Theorem 3.7: at a refresh index, the survival-masked raw SPIDER
error is integrable and bounded by the refresh variance. -/
private lemma activeRawGradientError_refresh
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hrefresh : k % Q = 0) :
    Integrable (activeRawGradientErrorIntegrand run X k) ℙ ∧
      activeRawGradientError run X k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
  classical
  let state := localizedPreBatchState run X k
  let freshBatch : Ω → (ℕ → Ξ) := fun omega i ↦ run.sample k i omega
  have hstate : AEMeasurable state ℙ := by
    simpa only [state] using
      aemeasurable_localizedPreBatchState run X hX initial_mem h_region k
  have hfreshBatch : AEMeasurable freshBatch ℙ := by
    simpa only [freshBatch] using aemeasurable_freshBatch run k
  have hindependent : ProbabilityTheory.IndepFun state freshBatch ℙ := by
    simpa only [state, freshBatch] using
      indepFun_localizedPreBatchState_freshBatch run X hX initial_mem h_region k
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) ℙ :=
    iIndepFun_freshBatch run k
  let phi :
      (LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) → ℝ := fun z ↦
    if z.1.1 = 1 ∧ z.1.2.1 ∈ h.region then
      ‖(B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
        (oracle.sampleGradient z.1.2.1 (z.2 i) -
          h.objectiveGradientExtension z.1.2.1)‖ ^ 2
    else 0
  let bound : LocalizedPreBatchState (n := n) (m := m) → ℝ :=
    fun _ ↦ (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ)
  have hphi : Measurable phi := by
    unfold phi
    have hflag : Measurable (fun z :
        LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
      fun_prop
    have hpoint : Measurable (fun z :
        LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
      fun_prop
    apply Measurable.ite
    · exact ((measurableSet_singleton (1 : ℝ)).preimage hflag).inter
        (h.isOpen_region.measurableSet.preimage hpoint)
    · have hsampled (i : ℕ) : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            oracle.sampleGradient z.1.2.1 (z.2 i)) :=
        oracle.measurable_sampleGradient.comp
          (hpoint.prodMk ((measurable_pi_apply i).comp measurable_snd))
      have hgradient : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            h.objectiveGradientExtension z.1.2.1) :=
        h.measurable_objectiveGradientExtension.comp hpoint
      have hsum : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            ∑ i ∈ Finset.range B,
              (oracle.sampleGradient z.1.2.1 (z.2 i) -
                h.objectiveGradientExtension z.1.2.1)) :=
        Finset.measurable_sum _ fun i _ ↦ (hsampled i).sub hgradient
      exact (hsum.const_smul ((B : ℝ)⁻¹)).norm.pow_const 2
    · exact measurable_const
  have hsection : ∀ s, Integrable (fun d ↦ phi (s, d)) (ℙ.map freshBatch) := by
    intro s
    have hsectionMeasurable : Measurable (fun d ↦ phi (s, d)) :=
      hphi.comp (measurable_const.prodMk measurable_id)
    by_cases hs : s.1 = 1 ∧ s.2.1 ∈ h.region
    · have hfixed := fixedPointRefreshBatchMeanSquare_le
        (oracle := oracle) s.2.1 hs.2 (run.sample k) B
        (run.hasLaw_sample k) hbatchIndependent
      have hgradient := h.objectiveGradientExtension_eq hs.2
      refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
        hfreshBatch).2 ?_
      simpa only [Function.comp_def, freshBatch, phi, if_pos hs, hgradient] using hfixed.1
    · have hzero : Integrable (fun _omega : Ω ↦ (0 : ℝ)) ℙ :=
        integrable_const _
      refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
        hfreshBatch).2 ?_
      simpa only [Function.comp_def, phi, if_neg hs] using hzero
  have hsectionBound : ∀ s,
      (∫ d, phi (s, d) ∂ℙ.map freshBatch) ≤ bound s := by
    intro s
    have hsectionMeasurable : Measurable (fun d ↦ phi (s, d)) :=
      hphi.comp (measurable_const.prodMk measurable_id)
    rw [integral_map hfreshBatch hsectionMeasurable.aestronglyMeasurable]
    by_cases hs : s.1 = 1 ∧ s.2.1 ∈ h.region
    · have hfixed := fixedPointRefreshBatchMeanSquare_le
        (oracle := oracle) s.2.1 hs.2 (run.sample k) B
        (run.hasLaw_sample k) hbatchIndependent
      have hgradient := h.objectiveGradientExtension_eq hs.2
      simpa only [Function.comp_apply, freshBatch, phi, bound, if_pos hs,
        hgradient] using hfixed.2
    · simp only [phi, bound, if_neg hs, integral_zero]
      positivity
  have hphiNonnegative : ∀ z, 0 ≤ phi z := by
    intro z
    unfold phi
    split
    · positivity
    · exact le_rfl
  have hpair := independentPairIntegral_le state freshBatch phi bound
    hindependent hstate hfreshBatch hphi.aemeasurable hphiNonnegative
    (Filter.Eventually.of_forall hsection) (integrable_const _)
    (Filter.Eventually.of_forall hsectionBound)
  have hidentify (omega : Ω) :
      phi (state omega, freshBatch omega) =
        activeRawGradientErrorIntegrand run X k omega := by
    by_cases hsurvival : omega ∈ survivalEvent run X k
    · have hsegment :=
        (preExitPrefixBounds run X initial_mem h_region omega k hsurvival).1 k
          (Nat.lt_succ_self k)
      have hx : run.point k omega ∈ h.region :=
        hsegment (left_mem_segment ℝ _ _)
      have hgradient := h.objectiveGradientExtension_eq hx
      simp only [phi, state, freshBatch, localizedPreBatchState,
        Set.indicator_of_mem hsurvival, hx, and_self, if_pos, hgradient,
        activeRawGradientErrorIntegrand]
      rw [SPIDER.rawEstimate_of_refresh oracle run.point run.sample Q B b k omega
          hrefresh,
        batchAverage_sub]
    · simp only [phi, state, freshBatch, localizedPreBatchState,
        Set.indicator_of_notMem hsurvival, activeRawGradientErrorIntegrand]
      simp
  have hintegrable : Integrable (activeRawGradientErrorIntegrand run X k) ℙ :=
    hpair.1.congr (Filter.Eventually.of_forall hidentify)
  refine ⟨hintegrable, ?_⟩
  -- Replace the active raw moment by the independent-pair integral and
  -- integrate the constant variance bound under a probability law.
  rw [activeRawGradientError]
  calc
    (∫ omega, activeRawGradientErrorIntegrand run X k omega ∂ℙ) =
        ∫ omega, phi (state omega, freshBatch omega) ∂ℙ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ (hidentify omega).symm
    _ ≤ ∫ s, bound s ∂ℙ.map state := hpair.2
    _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
      rw [integral_const, Measure.real,
        Measure.map_apply_of_aemeasurable hstate MeasurableSet.univ]
      simp only [Set.preimage_univ, measure_univ,
        ENNReal.toReal_one, one_smul]

/-- Helper for Theorem 3.7: at an update index, the survival-masked raw SPIDER
error adds at most one mean-square-Lipschitz innovation to the preceding
masked error. -/
private lemma activeRawGradientError_update
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hupdate : k % Q ≠ 0)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand run X (k - 1)) ℙ) :
    Integrable (activeRawGradientErrorIntegrand run X k) ℙ ∧
      activeRawGradientError run X k ≤
        activeRawGradientError run X (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∫ omega, activeStepSquareIntegrand run X (k - 1) omega ∂ℙ := by
  classical
  have hkPositive : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkZero
    apply hupdate
    simp only [hkZero, Nat.zero_mod]
  have hkPredSucc : k - 1 + 1 = k := by omega
  have hkPredLt : k - 1 < k + 1 := by omega
  let state := localizedPreBatchState run X k
  let freshBatch : Ω → (ℕ → Ξ) := fun omega i ↦ run.sample k i omega
  have hstate : AEMeasurable state ℙ := by
    simpa only [state] using
      aemeasurable_localizedPreBatchState run X hX initial_mem h_region k
  have hfreshBatch : AEMeasurable freshBatch ℙ := by
    simpa only [freshBatch] using aemeasurable_freshBatch run k
  have hindependent : ProbabilityTheory.IndepFun state freshBatch ℙ := by
    simpa only [state, freshBatch] using
      indepFun_localizedPreBatchState_freshBatch run X hX initial_mem h_region k
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) ℙ :=
    iIndepFun_freshBatch run k
  let phi :
      (LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ)) → ℝ := fun z ↦
    if z.1.1 = 1 ∧ z.1.2.1 ∈ h.region ∧ z.1.2.2.1 ∈ h.region then
      ‖(z.1.2.2.2.2 - h.objectiveGradientExtension z.1.2.2.1) +
        (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
          ((oracle.sampleGradient z.1.2.1 (z.2 i) -
              oracle.sampleGradient z.1.2.2.1 (z.2 i)) -
            (h.objectiveGradientExtension z.1.2.1 -
              h.objectiveGradientExtension z.1.2.2.1))‖ ^ 2
    else 0
  let bound : LocalizedPreBatchState (n := n) (m := m) → ℝ := fun s ↦
    if s.1 = 1 ∧ s.2.1 ∈ h.region ∧ s.2.2.1 ∈ h.region then
      ‖s.2.2.2.2 - h.objectiveGradientExtension s.2.2.1‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖s.2.1 - s.2.2.1‖ ^ 2
    else 0
  have hflagMeasurable : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hxMeasurable : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hyMeasurable : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦ z.1.2.2.1) := by
    fun_prop
  have hgradientX : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
        h.objectiveGradientExtension z.1.2.1) :=
    h.measurable_objectiveGradientExtension.comp hxMeasurable
  have hgradientY : Measurable (fun z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
        h.objectiveGradientExtension z.1.2.2.1) :=
    h.measurable_objectiveGradientExtension.comp hyMeasurable
  have hconditionMeasurable : MeasurableSet {z :
      LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) |
        z.1.1 = 1 ∧ z.1.2.1 ∈ h.region ∧ z.1.2.2.1 ∈ h.region} := by
    exact (measurableSet_eq_fun hflagMeasurable measurable_const).inter
      ((h.isOpen_region.measurableSet.preimage hxMeasurable).inter
        (h.isOpen_region.measurableSet.preimage hyMeasurable))
  have hphi : Measurable phi := by
    unfold phi
    apply Measurable.ite hconditionMeasurable
    · have hsampledX (i : ℕ) : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            oracle.sampleGradient z.1.2.1 (z.2 i)) :=
        oracle.measurable_sampleGradient.comp
          (hxMeasurable.prodMk ((measurable_pi_apply i).comp measurable_snd))
      have hsampledY (i : ℕ) : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            oracle.sampleGradient z.1.2.2.1 (z.2 i)) :=
        oracle.measurable_sampleGradient.comp
          (hyMeasurable.prodMk ((measurable_pi_apply i).comp measurable_snd))
      have hsum : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            ∑ i ∈ Finset.range b,
              ((oracle.sampleGradient z.1.2.1 (z.2 i) -
                  oracle.sampleGradient z.1.2.2.1 (z.2 i)) -
                (h.objectiveGradientExtension z.1.2.1 -
                  h.objectiveGradientExtension z.1.2.2.1))) :=
        Finset.measurable_sum _ fun i _ ↦
          ((hsampledX i).sub (hsampledY i)).sub (hgradientX.sub hgradientY)
      have hpreviousRaw : Measurable (fun z :
          LocalizedPreBatchState (n := n) (m := m) × (ℕ → Ξ) ↦
            z.1.2.2.2.2) := by
        fun_prop
      exact ((hpreviousRaw.sub hgradientY).add
        (hsum.const_smul ((b : ℝ)⁻¹))).norm.pow_const 2
    · exact measurable_const
  have hboundMeasurable : Measurable bound := by
    unfold bound
    have hflag : Measurable (fun s :
        LocalizedPreBatchState (n := n) (m := m) ↦ s.1) := measurable_fst
    have hxState : Measurable (fun s :
        LocalizedPreBatchState (n := n) (m := m) ↦ s.2.1) := by
      fun_prop
    have hyState : Measurable (fun s :
        LocalizedPreBatchState (n := n) (m := m) ↦ s.2.2.1) := by
      fun_prop
    have hpreviousRaw : Measurable (fun s :
        LocalizedPreBatchState (n := n) (m := m) ↦ s.2.2.2.2) := by
      fun_prop
    have hgradientState : Measurable (fun s :
        LocalizedPreBatchState (n := n) (m := m) ↦
          h.objectiveGradientExtension s.2.2.1) :=
      h.measurable_objectiveGradientExtension.comp hyState
    have hcondition : MeasurableSet {s :
        LocalizedPreBatchState (n := n) (m := m) |
          s.1 = 1 ∧ s.2.1 ∈ h.region ∧ s.2.2.1 ∈ h.region} := by
      exact (measurableSet_eq_fun hflag measurable_const).inter
        ((h.isOpen_region.measurableSet.preimage hxState).inter
          (h.isOpen_region.measurableSet.preimage hyState))
    apply Measurable.ite hcondition
    · exact ((hpreviousRaw.sub hgradientState).norm.pow_const 2).add
        (((hxState.sub hyState).norm.pow_const 2).const_mul
          ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)))
    · exact measurable_const
  have hsection : ∀ s, Integrable (fun d ↦ phi (s, d)) (ℙ.map freshBatch) := by
    intro s
    have hsectionMeasurable : Measurable (fun d ↦ phi (s, d)) :=
      hphi.comp (measurable_const.prodMk measurable_id)
    by_cases hs : s.1 = 1 ∧ s.2.1 ∈ h.region ∧ s.2.2.1 ∈ h.region
    · have hfixed := fixedPointUpdateBatchMeanSquare_le
        (oracle := oracle) s.2.1 hs.2.1 s.2.2.1 hs.2.2
        (s.2.2.2.2 - gradient f s.2.2.1) (run.sample k) b
        (run.hasLaw_sample k) hbatchIndependent
      have hgradientX := h.objectiveGradientExtension_eq hs.2.1
      have hgradientY := h.objectiveGradientExtension_eq hs.2.2
      refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
        hfreshBatch).2 ?_
      simpa only [Function.comp_def, freshBatch, phi, if_pos hs,
        hgradientX, hgradientY] using hfixed.1
    · have hzero : Integrable (fun _omega : Ω ↦ (0 : ℝ)) ℙ :=
        integrable_const _
      refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable
        hfreshBatch).2 ?_
      simpa only [Function.comp_def, phi, if_neg hs] using hzero
  have hsectionBound : ∀ s,
      (∫ d, phi (s, d) ∂ℙ.map freshBatch) ≤ bound s := by
    intro s
    have hsectionMeasurable : Measurable (fun d ↦ phi (s, d)) :=
      hphi.comp (measurable_const.prodMk measurable_id)
    rw [integral_map hfreshBatch hsectionMeasurable.aestronglyMeasurable]
    by_cases hs : s.1 = 1 ∧ s.2.1 ∈ h.region ∧ s.2.2.1 ∈ h.region
    · have hfixed := fixedPointUpdateBatchMeanSquare_le
        (oracle := oracle) s.2.1 hs.2.1 s.2.2.1 hs.2.2
        (s.2.2.2.2 - gradient f s.2.2.1) (run.sample k) b
        (run.hasLaw_sample k) hbatchIndependent
      have hgradientX := h.objectiveGradientExtension_eq hs.2.1
      have hgradientY := h.objectiveGradientExtension_eq hs.2.2
      simpa only [Function.comp_apply, freshBatch, phi, bound, if_pos hs,
        hgradientX, hgradientY] using hfixed.2
    · simp only [phi, bound, if_neg hs, integral_zero]
      exact le_rfl
  have hsurvivalCurrent := nullMeasurableSet_survivalEvent run X hX k
  have hsurvivalPrevious :=
    nullMeasurableSet_survivalEvent run X hX (k - 1)
  have hkPredLe : k - 1 ≤ k := by omega
  have hsubset : survivalEvent run X k ⊆ survivalEvent run X (k - 1) :=
    survivalEvent_antitone run X hkPredLe
  let previousSquare : Ω → ℝ := fun omega ↦
    ‖SPIDER.rawEstimate oracle run.point run.sample Q B b (k - 1) omega -
      gradient f (run.point (k - 1) omega)‖ ^ 2
  let stepSquare : Ω → ℝ := fun omega ↦ ‖run.step (k - 1) omega‖ ^ 2
  have hpreviousCurrent : Integrable
      ((survivalEvent run X k).indicator previousSquare) ℙ := by
    have hnested := hprevious.indicator₀ hsurvivalCurrent
    have hmaskEquality :
        (survivalEvent run X k).indicator
            (activeRawGradientErrorIntegrand run X (k - 1)) =
          (survivalEvent run X k).indicator previousSquare := by
      funext omega
      by_cases hcurrent : omega ∈ survivalEvent run X k
      · have hprev : omega ∈ survivalEvent run X (k - 1) := hsubset hcurrent
        simp only [Set.indicator_of_mem hcurrent, activeRawGradientErrorIntegrand,
          Set.indicator_of_mem hprev, previousSquare]
      · simp only [Set.indicator_of_notMem hcurrent]
    rw [hmaskEquality] at hnested
    exact hnested
  have hstepCurrent : Integrable
      ((survivalEvent run X k).indicator stepSquare) ℙ := by
    unfold stepSquare
    exact ((integrableOn_stepSquare_preExit run X hX initial_mem h_region (k - 1)).mono_set
      hsubset).integrable_indicator₀ hsurvivalCurrent
  have hpointSucc (omega : Ω) :
      run.point k omega = run.point (k - 1) omega + run.step (k - 1) omega := by
    simpa only [hkPredSucc] using run.point_succ (k - 1) omega
  have hboundIdentify (omega : Ω) :
      bound (state omega) =
        (survivalEvent run X k).indicator (fun omega' ↦
          previousSquare omega' +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              stepSquare omega') omega := by
    by_cases hsurvival : omega ∈ survivalEvent run X k
    · have hbounds :=
        preExitPrefixBounds run X initial_mem h_region omega k hsurvival
      have hx : run.point k omega ∈ h.region :=
        hbounds.1 k (Nat.lt_succ_self k) (left_mem_segment ℝ _ _)
      have hy : run.point (k - 1) omega ∈ h.region :=
        hbounds.1 (k - 1) hkPredLt (left_mem_segment ℝ _ _)
      have hgradientY := h.objectiveGradientExtension_eq hy
      simp only [bound, state, localizedPreBatchState,
        Set.indicator_of_mem hsurvival, hx, hy, true_and, if_true,
        ne_of_gt hkPositive, if_false, previousSquare, stepSquare,
        hgradientY]
      rw [hpointSucc, add_sub_cancel_left]
    · simp only [bound, state, localizedPreBatchState,
        Set.indicator_of_notMem hsurvival]
      simp
  have hcoefficientNonnegative :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  have hboundComp : Integrable (fun omega ↦ bound (state omega)) ℙ := by
    have hsum := hpreviousCurrent.add
      (hstepCurrent.const_mul
        ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)))
    have hsumPointwise (omega : Ω) :
          (survivalEvent run X k).indicator previousSquare omega +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              (survivalEvent run X k).indicator stepSquare omega =
        (survivalEvent run X k).indicator (fun omega' ↦
          previousSquare omega' +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              stepSquare omega') omega := by
      by_cases hsurvival : omega ∈ survivalEvent run X k
      · simp only [Set.indicator_of_mem hsurvival]
      · simp only [Set.indicator_of_notMem hsurvival, mul_zero, add_zero]
    have hmaskedSum : Integrable (fun omega ↦
        (survivalEvent run X k).indicator (fun omega' ↦
          previousSquare omega' +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              stepSquare omega') omega) ℙ :=
      hsum.congr (Filter.Eventually.of_forall hsumPointwise)
    exact hmaskedSum.congr (Filter.Eventually.of_forall fun omega ↦
      (hboundIdentify omega).symm)
  have hboundMap : Integrable bound (ℙ.map state) :=
    (integrable_map_measure hboundMeasurable.aestronglyMeasurable hstate).2
      hboundComp
  have hphiNonnegative : ∀ z, 0 ≤ phi z := by
    intro z
    unfold phi
    split
    · positivity
    · exact le_rfl
  have hpair := independentPairIntegral_le state freshBatch phi bound
    hindependent hstate hfreshBatch hphi.aemeasurable hphiNonnegative
    (Filter.Eventually.of_forall hsection) hboundMap
    (Filter.Eventually.of_forall hsectionBound)
  have hidentify (omega : Ω) :
      phi (state omega, freshBatch omega) =
        activeRawGradientErrorIntegrand run X k omega := by
    by_cases hsurvival : omega ∈ survivalEvent run X k
    · have hbounds :=
        preExitPrefixBounds run X initial_mem h_region omega k hsurvival
      have hx : run.point k omega ∈ h.region :=
        hbounds.1 k (Nat.lt_succ_self k) (left_mem_segment ℝ _ _)
      have hy : run.point (k - 1) omega ∈ h.region :=
        hbounds.1 (k - 1) hkPredLt (left_mem_segment ℝ _ _)
      have hgradientX := h.objectiveGradientExtension_eq hx
      have hgradientY := h.objectiveGradientExtension_eq hy
      have hnonrefreshPred : (k - 1 + 1) % Q ≠ 0 := by
        simpa only [hkPredSucc] using hupdate
      simp only [phi, state, freshBatch, localizedPreBatchState,
        Set.indicator_of_mem hsurvival, hx, hy, and_self, if_pos,
        ne_of_gt hkPositive, if_false, activeRawGradientErrorIntegrand,
        hgradientX, hgradientY]
      rw [← hkPredSucc,
        SPIDER.rawEstimate_of_update oracle run.point run.sample Q B b (k - 1)
          omega hnonrefreshPred,
        batchAverage_sub]
      simp only [hkPredSucc]
      apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ 2)
      module
    · simp only [phi, state, freshBatch, localizedPreBatchState,
        Set.indicator_of_notMem hsurvival, activeRawGradientErrorIntegrand]
      simp
  have hintegrable : Integrable (activeRawGradientErrorIntegrand run X k) ℙ :=
    hpair.1.congr (Filter.Eventually.of_forall hidentify)
  have hpreviousIntegralLe :
      (∫ omega, (survivalEvent run X k).indicator previousSquare omega ∂ℙ) ≤
        activeRawGradientError run X (k - 1) := by
    have hpointwise (omega : Ω) :
        (survivalEvent run X k).indicator previousSquare omega ≤
          activeRawGradientErrorIntegrand run X (k - 1) omega := by
      by_cases hcurrent : omega ∈ survivalEvent run X k
      · have hprev : omega ∈ survivalEvent run X (k - 1) := hsubset hcurrent
        simp only [Set.indicator_of_mem hcurrent, activeRawGradientErrorIntegrand,
          Set.indicator_of_mem hprev, previousSquare]
        exact le_rfl
      · simp only [Set.indicator_of_notMem hcurrent]
        unfold activeRawGradientErrorIntegrand
        by_cases hprev : omega ∈ survivalEvent run X (k - 1)
        · simp only [Set.indicator_of_mem hprev]
          positivity
        · simp only [Set.indicator_of_notMem hprev]
          exact le_rfl
    rw [activeRawGradientError]
    exact integral_mono hpreviousCurrent hprevious hpointwise
  have hstepPrevious :=
    integrable_activeStepSquareIntegrand run X hX initial_mem h_region (k - 1)
  have hstepCurrentAsActive : Integrable
      ((survivalEvent run X k).indicator stepSquare) ℙ := hstepCurrent
  have hstepIntegralLe :
      (∫ omega, (survivalEvent run X k).indicator stepSquare omega ∂ℙ) ≤
        ∫ omega, activeStepSquareIntegrand run X (k - 1) omega ∂ℙ := by
    have hpointwise (omega : Ω) :
        (survivalEvent run X k).indicator stepSquare omega ≤
          activeStepSquareIntegrand run X (k - 1) omega := by
      by_cases hcurrent : omega ∈ survivalEvent run X k
      · have hprev : omega ∈ survivalEvent run X (k - 1) := hsubset hcurrent
        simp only [Set.indicator_of_mem hcurrent, activeStepSquareIntegrand,
          Set.indicator_of_mem hprev, stepSquare]
        exact le_rfl
      · simp only [Set.indicator_of_notMem hcurrent]
        unfold activeStepSquareIntegrand
        by_cases hprev : omega ∈ survivalEvent run X (k - 1)
        · simp only [Set.indicator_of_mem hprev]
          positivity
        · simp only [Set.indicator_of_notMem hprev]
          exact le_rfl
    exact integral_mono hstepCurrentAsActive hstepPrevious hpointwise
  refine ⟨hintegrable, ?_⟩
  -- Integrate the statewise update bound, then enlarge both current survival
  -- masks to the preceding survival event.
  rw [activeRawGradientError]
  calc
    (∫ omega, activeRawGradientErrorIntegrand run X k omega ∂ℙ) =
        ∫ omega, phi (state omega, freshBatch omega) ∂ℙ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ (hidentify omega).symm
    _ ≤ ∫ s, bound s ∂ℙ.map state := hpair.2
    _ = ∫ omega, bound (state omega) ∂ℙ :=
      integral_map hstate hboundMeasurable.aestronglyMeasurable
    _ = (∫ omega, (survivalEvent run X k).indicator previousSquare omega ∂ℙ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∫ omega, (survivalEvent run X k).indicator stepSquare omega ∂ℙ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hboundIdentify)]
      have hmaskAddPointwise (omega : Ω) :
          (survivalEvent run X k).indicator (fun omega' ↦
            previousSquare omega' +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                stepSquare omega') omega =
            (survivalEvent run X k).indicator previousSquare omega +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                (survivalEvent run X k).indicator stepSquare omega := by
        by_cases hsurvival : omega ∈ survivalEvent run X k
        · simp only [Set.indicator_of_mem hsurvival]
        · simp only [Set.indicator_of_notMem hsurvival, mul_zero, add_zero]
      rw [integral_congr_ae (Filter.Eventually.of_forall hmaskAddPointwise),
        integral_add hpreviousCurrent
          (hstepCurrent.const_mul
            ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))),
        integral_const_mul]
    _ ≤ activeRawGradientError run X (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∫ omega, activeStepSquareIntegrand run X (k - 1) omega ∂ℙ :=
      add_le_add hpreviousIntegralLe
        (mul_le_mul_of_nonneg_left hstepIntegralLe hcoefficientNonnegative)

/-- Helper for Theorem 3.7: summing prefixes since the latest refresh counts
each nonnegative summand at most the refresh period many times. -/
private lemma sum_lastRefresh_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (q K : ℕ) (hq : 0 < q) :
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j ≤
      q * ∑ j ∈ Finset.range K, a j := by
  classical
  -- Put every block prefix over the common horizon before interchanging the
  -- two finite sums.
  have interval_eq_filter (k : ℕ) (hk : k ∈ Finset.range K) :
      Finset.Ico (k - k % q) k =
        (Finset.range K).filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) := by
    have hk' : k < K := Finset.mem_range.mp hk
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  calc
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.Ico (k - k % q) k, a j =
        ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ j ∈ Finset.Ico (k - k % q) k, a j =
            ∑ j ∈ (Finset.range K).filter
              (fun j ↦ j ∈ Finset.Ico (k - k % q) k), a j :=
          congrArg (fun s : Finset ℕ ↦ ∑ j ∈ s, a j) (interval_eq_filter k hk)
        _ = ∑ j ∈ Finset.range K,
              if j ∈ Finset.Ico (k - k % q) k then a j else 0 :=
          Finset.sum_filter (fun j ↦ j ∈ Finset.Ico (k - k % q) k) a
    _ = ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
          if j ∈ Finset.Ico (k - k % q) k then a j else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range K, q * a j := by
      apply Finset.sum_le_sum
      intro j hj
      have hsubset :
          (Finset.range K).filter (fun k ↦ j ∈ Finset.Ico (k - k % q) k) ⊆
            Finset.Ioc j (j + q) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
          Finset.mem_Ioc] at hk ⊢
        have hmod : k % q < q := Nat.mod_lt k hq
        omega
      have hcard :
          ((Finset.range K).filter
            (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤ q := by
        calc
          ((Finset.range K).filter
              (fun k ↦ j ∈ Finset.Ico (k - k % q) k)).card ≤
              (Finset.Ioc j (j + q)).card := Finset.card_le_card hsubset
          _ = q := by simp
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hcard) (ha j)
    _ = q * ∑ j ∈ Finset.range K, a j := by
      rw [Finset.mul_sum]

/-- Helper for Theorem 3.7: the active raw SPIDER error accumulates update
variance only since its most recent refresh. -/
private lemma activeRawGradientError_le_lastRefresh
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Integrable (activeRawGradientErrorIntegrand run X k) ℙ ∧
      activeRawGradientError run X k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k, activeStepMoment run X j := by
  -- Strong induction remains inside the current refresh block and resets the
  -- accumulated variance whenever `k % Q = 0`.
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hrefresh : k % Q = 0
      · have hone := activeRawGradientError_refresh X hX initial_mem run h_region
          k hrefresh
        refine ⟨hone.1, ?_⟩
        simpa only [hrefresh, Nat.sub_zero, Finset.Ico_self, Finset.sum_empty,
          mul_zero, add_zero] using hone.2
      · have hkPositive : 0 < k := by
          exact Nat.pos_of_ne_zero fun hkZero ↦
            hrefresh (by simp only [hkZero, Nat.zero_mod])
        have hkPredSucc : k - 1 + 1 = k := by omega
        have hprevious := ih (k - 1) (by omega)
        have hone := activeRawGradientError_update X hX initial_mem run h_region
          k hrefresh hprevious.1
        refine ⟨hone.1, ?_⟩
        have hQGtOne : 1 < (Q : ℕ) := by
          have hQPositive : 0 < (Q : ℕ) := Q.pos
          by_contra hnot
          have hQeq : (Q : ℕ) = 1 := by omega
          exact hrefresh (by rw [hQeq, Nat.mod_one])
        have hmodSucc :
            k % Q = ((k - 1) % Q + 1) % Q := by
          conv_lhs => rw [← hkPredSucc]
          rw [Nat.add_mod, Nat.mod_eq_of_lt hQGtOne]
        have hpreviousRemainderSucc : (k - 1) % Q + 1 < Q := by
          have hpreviousModLt : (k - 1) % Q < Q :=
            Nat.mod_lt (k - 1) Q.pos
          by_contra hnot
          have heq : (k - 1) % Q + 1 = Q := by omega
          apply hrefresh
          rw [hmodSucc, heq, Nat.mod_self]
        have hkModSucc : k % Q = (k - 1) % Q + 1 := by
          rw [hmodSucc, Nat.mod_eq_of_lt hpreviousRemainderSucc]
        have hblockStart :
            k - k % Q = (k - 1) - (k - 1) % Q := by
          omega
        have hstart_le : k - k % Q ≤ k - 1 := by
          have hkModPositive : 0 < k % Q := Nat.pos_of_ne_zero hrefresh
          omega
        have hblockSum :
            (∑ j ∈ Finset.Ico (k - k % Q) k, activeStepMoment run X j) =
              (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                activeStepMoment run X j) + activeStepMoment run X (k - 1) := by
          calc
            (∑ j ∈ Finset.Ico (k - k % Q) k, activeStepMoment run X j) =
                ∑ j ∈ Finset.Ico (k - k % Q) ((k - 1) + 1),
                  activeStepMoment run X j := by rw [hkPredSucc]
            _ = (∑ j ∈ Finset.Ico (k - k % Q) (k - 1),
                  activeStepMoment run X j) + activeStepMoment run X (k - 1) :=
              Finset.sum_Ico_succ_top hstart_le (activeStepMoment run X)
            _ = (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  activeStepMoment run X j) + activeStepMoment run X (k - 1) := by
              rw [hblockStart]
        have honeBound : activeRawGradientError run X k ≤
            activeRawGradientError run X (k - 1) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                activeStepMoment run X (k - 1) := by
          simpa only [activeStepMoment] using hone.2
        calc
          activeRawGradientError run X k ≤
              activeRawGradientError run X (k - 1) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  activeStepMoment run X (k - 1) := honeBound
          _ ≤ ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                    activeStepMoment run X j) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                activeStepMoment run X (k - 1) := by
            exact add_le_add hprevious.2 le_rfl
          _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico (k - k % Q) k,
                    activeStepMoment run X j := by
            rw [hblockSum]
            ring

/-- Helper for Theorem 3.7: radial clipping cannot increase the active
mean-square gradient error. -/
private lemma activeGradientError_le_activeRawGradientError
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ)
    (hraw : Integrable (activeRawGradientErrorIntegrand run X k) ℙ) :
    (∫ omega in survivalEvent run X k, ‖run.gradientError k omega‖ ^ 2 ∂ℙ) ≤
      activeRawGradientError run X k := by
  -- Compare the two indicator integrands pointwise on survival, where the true
  -- gradient lies in the clipping ball supplied by the region condition.
  have hactive := nullMeasurableSet_survivalEvent run X hX k
  have hprojected : Integrable
      ((survivalEvent run X k).indicator
        (fun omega ↦ ‖run.gradientError k omega‖ ^ 2)) ℙ :=
    (integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k).integrable_indicator₀
      hactive
  have hpointwise (omega : Ω) :
      (survivalEvent run X k).indicator
          (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega ≤
        activeRawGradientErrorIntegrand run X k omega := by
    by_cases hsurvival : omega ∈ survivalEvent run X k
    · have hsegment :=
        (preExitPrefixBounds run X initial_mem h_region omega k hsurvival).1 k
          (Nat.lt_succ_self k)
      have hx : run.point k omega ∈ h.region :=
        hsegment (left_mem_segment ℝ _ _)
      simp only [Set.indicator_of_mem hsurvival,
        activeRawGradientErrorIntegrand]
      rw [run.gradientError_apply, run.gradientEstimate_apply,
        SPIDER.estimate_apply]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (SPIDER.norm_clip_sub_le h.gradientBound _ _
          (h.norm_gradient_le _ hx)) 2
    · simp only [Set.indicator_of_notMem hsurvival,
        activeRawGradientErrorIntegrand]
      exact le_rfl
  -- Integrating the pointwise contraction gives the active raw comparison.
  rw [← integral_indicator₀ hactive, activeRawGradientError]
  exact integral_mono hprojected hraw hpointwise

/-- Helper for Theorem 3.7: summing active step moments recovers the stopped
step energy. -/
private lemma sum_activeStepMoment_eq_stoppedStepEnergy
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) (K : ℕ) :
    ∑ k ∈ Finset.range K, activeStepMoment run X k =
      stoppedStepEnergy run X K := by
  -- Convert each integral of a survival indicator into its set integral.
  rw [stoppedStepEnergy]
  apply Finset.sum_congr rfl
  intro k hk
  rw [activeStepMoment, activeStepSquareIntegrand,
    integral_indicator₀ (nullMeasurableSet_survivalEvent run X hX k)]

/-- Helper for Theorem 3.7: the stopped projected-gradient-error energy obeys
the refresh-block SPIDER variance estimate. -/
private lemma stoppedGradientErrorEnergy_le
    (K : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) :
    stoppedErrorEnergy run X K ≤
      (K : ℝ) * oracle.noiseLevel ^ 2 / (B : ℝ) +
        ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
          stoppedStepEnergy run X K := by
  classical
  -- First combine the last-refresh raw estimate with the clipping contraction
  -- at every active iteration.
  have hrawBound (k : ℕ) (hk : k < K) :
      (∫ omega in survivalEvent run X k, ‖run.gradientError k omega‖ ^ 2 ∂ℙ) ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k, activeStepMoment run X j := by
    have hraw := activeRawGradientError_le_lastRefresh X hX initial_mem run
      h_region k
    exact (activeGradientError_le_activeRawGradientError X hX initial_mem run
      h_region k hraw.1).trans hraw.2
  have hblockCount := sum_lastRefresh_le (activeStepMoment run X)
    (activeStepMoment_nonneg run X) Q K Q.pos
  have hcoefficientNonnegative :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  have hstepSum := sum_activeStepMoment_eq_stoppedStepEnergy run X hX K
  -- Sum the active pointwise bounds, count every update step at most `Q`
  -- times, and identify the resulting active-step sum.
  rw [stoppedErrorEnergy]
  calc
    ∑ k ∈ Finset.range K,
        ∫ omega in survivalEvent run X k, ‖run.gradientError k omega‖ ^ 2 ∂ℙ ≤
        ∑ k ∈ Finset.range K,
          ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                activeStepMoment run X j) := by
      exact Finset.sum_le_sum fun k hk ↦ hrawBound k (Finset.mem_range.mp hk)
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ k ∈ Finset.range K,
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                activeStepMoment run X j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ((Q : ℕ) * ∑ k ∈ Finset.range K,
              activeStepMoment run X k) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hblockCount hcoefficientNonnegative) _
    _ = (K : ℝ) * oracle.noiseLevel ^ 2 / (B : ℝ) +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            stoppedStepEnergy run X K := by
      rw [hstepSum]
      ring

/-- Helper for Theorem 3.7: stopped Lyapunov and SPIDER recursions couple the
total active primal-step and estimator-error energies. -/
private lemma stoppedEnergyCoupling
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) :
    stoppedStepEnergy run X K ≤
        initialStepBound h params +
          errorStepConstant h params * stoppedErrorEnergy run X K ∧
      stoppedErrorEnergy run X K ≤
        (K : ℝ) * oracle.noiseLevel ^ 2 / (B : ℝ) +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 / (b : ℝ)) *
            stoppedStepEnergy run X K := by
  -- Pair the deterministic active-prefix telescope with the stopped estimator
  -- recursion, keeping the two proof interfaces independent.
  exact ⟨stoppedStepEnergy_le K hK X hX initial_mem run h_region,
    stoppedGradientErrorEnergy_le K X hX initial_mem run h_region⟩

/-- Helper for Theorem 3.7: the scheduled inner batch makes the coupled
error-step coefficient at most one half. -/
private lemma scheduledErrorStepCoefficient_le_half (K : ℕ) :
    errorStepConstant h params *
        ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) ≤
      (1 : ℝ) / 2 := by
  -- Unpack the schedule's sufficient-batch certificate and divide by its size.
  have hbatch := (SPIDER.isSufficientInnerBatchSize_iff h oracle params
    (SPIDER.refreshPeriod K) (SPIDER.innerBatchSize h oracle params K)).mp
      (SPIDER.innerBatchSize_isSufficient h oracle params K)
  have hb : 0 < (SPIDER.innerBatchSize h oracle params K : ℝ) := by positivity
  have hdivided :
      (2 * errorStepConstant h params * (SPIDER.refreshPeriod K : ℝ) *
          oracle.meanSquareLipschitz ^ 2) /
          (SPIDER.innerBatchSize h oracle params K : ℝ) ≤ 1 := by
    calc
      (2 * errorStepConstant h params * (SPIDER.refreshPeriod K : ℝ) *
          oracle.meanSquareLipschitz ^ 2) /
          (SPIDER.innerBatchSize h oracle params K : ℝ) ≤
          (SPIDER.innerBatchSize h oracle params K : ℝ) /
            (SPIDER.innerBatchSize h oracle params K : ℝ) :=
        (div_le_div_iff_of_pos_right hb).2 hbatch
      _ = 1 := div_self hb.ne'
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  calc
    errorStepConstant h params *
        ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) =
        ((2 * errorStepConstant h params * (SPIDER.refreshPeriod K : ℝ) *
          oracle.meanSquareLipschitz ^ 2) /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) / 2 := by
      ring
    _ ≤ (1 : ℝ) / 2 := div_le_div_of_nonneg_right hdivided htwoNonneg

/-- Helper for Theorem 3.7: the prescribed SPIDER schedule bounds both stopped
estimator-error and stopped primal-step energies by their canonical allowances. -/
private lemma scheduledStoppedEnergyBounds
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    stoppedErrorEnergy run X K ≤ errorAverageConstant h oracle params ∧
      stoppedStepEnergy run X K ≤ stepAverageConstant h oracle params := by
  -- Absorb the stopped estimator/step coupling using the scheduled half factor.
  have hcoupling := stoppedEnergyCoupling K hK X hX initial_mem run h_region
  have hsteps := hcoupling.1
  have herrors := hcoupling.2
  rw [SPIDER.refreshBatchSize_coe K hK] at herrors
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have hvariance :
      (K : ℝ) * oracle.noiseLevel ^ 2 / K = oracle.noiseLevel ^ 2 := by
    field_simp [hKzero]
  rw [hvariance] at herrors
  have hDpos : 0 < errorStepConstant h params := errorStepConstant_pos
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hD0pos := initialStepBound_pos X initial_mem h_region
  have hD0nonneg : 0 ≤ initialStepBound h params := hD0pos.le
  have herrorNonneg := stoppedErrorEnergy_nonneg run X K
  have hcoefficientNonneg :
      0 ≤ (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
        (SPIDER.innerBatchSize h oracle params K : ℝ) := by
    positivity
  have hstepsScaled := mul_le_mul_of_nonneg_left hsteps hcoefficientNonneg
  have hcombined :
      stoppedErrorEnergy run X K ≤
        oracle.noiseLevel ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
            (SPIDER.innerBatchSize h oracle params K : ℝ)) *
            (initialStepBound h params +
              errorStepConstant h params * stoppedErrorEnergy run X K) :=
    herrors.trans (add_le_add (le_refl _) hstepsScaled)
  have habsorb := scheduledErrorStepCoefficient_le_half
    (h := h) (oracle := oracle) (params := params) K
  have habsorbCommuted :
      ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) *
          errorStepConstant h params ≤ (1 : ℝ) / 2 := by
    simpa only [mul_comm] using habsorb
  have habsorbError :=
    mul_le_mul_of_nonneg_right habsorbCommuted herrorNonneg
  have hcoefficientLe :
      (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ) ≤
        ((1 : ℝ) / 2) / errorStepConstant h params :=
    (le_div_iff₀ hDpos).2 habsorbCommuted
  have hinitialContribution :=
    mul_le_mul_of_nonneg_right hcoefficientLe hD0nonneg
  have hinitialNormalized :
      ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) *
          initialStepBound h params ≤
        initialStepBound h params / (2 * errorStepConstant h params) := by
    calc
      ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) *
          initialStepBound h params ≤
          ((1 : ℝ) / 2) / errorStepConstant h params *
            initialStepBound h params := hinitialContribution
      _ = initialStepBound h params / (2 * errorStepConstant h params) := by
        field_simp [hDzero]
  have hbound :
      stoppedErrorEnergy run X K ≤
        oracle.noiseLevel ^ 2 +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedErrorEnergy run X K := by
    calc
      stoppedErrorEnergy run X K ≤
          oracle.noiseLevel ^ 2 +
            ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
              (SPIDER.innerBatchSize h oracle params K : ℝ)) *
              (initialStepBound h params +
                errorStepConstant h params * stoppedErrorEnergy run X K) := hcombined
      _ = oracle.noiseLevel ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
            (SPIDER.innerBatchSize h oracle params K : ℝ)) *
            initialStepBound h params +
          (((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
            (SPIDER.innerBatchSize h oracle params K : ℝ)) *
              errorStepConstant h params) * stoppedErrorEnergy run X K := by
        ring
      _ ≤ oracle.noiseLevel ^ 2 +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedErrorEnergy run X K :=
        add_le_add (add_le_add (le_refl _) hinitialNormalized) habsorbError
  have hinitialDouble :
      2 * (initialStepBound h params / (2 * errorStepConstant h params)) =
        initialStepBound h params / errorStepConstant h params := by
    field_simp [hDzero]
  have herrorBound :
      stoppedErrorEnergy run X K ≤ errorAverageConstant h oracle params := by
    rw [errorAverageConstant_def]
    linarith [hbound, hinitialDouble]
  have hstepBound :
      stoppedStepEnergy run X K ≤ stepAverageConstant h oracle params := by
    calc
      stoppedStepEnergy run X K ≤
          initialStepBound h params +
            errorStepConstant h params * stoppedErrorEnergy run X K := hsteps
      _ ≤ initialStepBound h params +
          errorStepConstant h params * errorAverageConstant h oracle params :=
        add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left herrorBound hDpos.le)
      _ = stepAverageConstant h oracle params := by
        rw [errorAverageConstant_def, stepAverageConstant_def]
        field_simp [hDzero]
        ring
  exact ⟨herrorBound, hstepBound⟩

/-- Helper for Theorem 3.7: an exit by the horizon has a concrete first-exit
iterate whose objective is controlled by deterministic potential and active errors. -/
private lemma objectiveAtExit_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (hω : exitTime run X ω ≤ K) :
    ∃ j ∈ Set.Icc 1 K, run.point j ω ∉ X ∧
      f (run.point j ω) ≤
        LALM.deterministicObjectiveBound h params +
          2 * lyapunovErrorConstant h params * activeErrorEnergyReal run X K ω ∧
      ‖c (run.point j ω)‖ ≤ 2 * params.multiplierBound / params.rho := by
  -- An exit bounded by a natural horizon is finite, so its canonical hitting
  -- index is attained in the complement of the localization set.
  have hexitFinite : exitTime run X ω ≠ ⊤ := by
    intro hexitTop
    simp only [hexitTop, WithTop.top_le_iff] at hω
    exact (WithTop.coe_ne_top : (K : WithTop ℕ) ≠ ⊤) hω
  have hexitPoint :
      run.point (exitTime run X ω).untopA ω ∈ Xᶜ := by
    simpa only [exitTime_def] using
      (MeasureTheory.hittingAfter_mem_set_of_ne_top
        (u := run.point) (s := Xᶜ) (n := 1) (ω := ω) hexitFinite)
  lift exitTime run X ω to ℕ using hexitFinite with j hj
  have hjUpper : j ≤ K := ENat.coe_le_coe.mp hω
  have hexitLower : (1 : WithTop ℕ) ≤ exitTime run X ω :=
    MeasureTheory.le_hittingAfter (u := run.point) (s := Xᶜ) (n := 1) ω
  have hjLowerTop : (1 : WithTop ℕ) ≤ (j : WithTop ℕ) :=
    hexitLower.trans_eq hj.symm
  have hjLower : 1 ≤ j := by
    exact_mod_cast hjLowerTop
  have hjOutside : run.point j ω ∉ X := by
    simpa [← ENat.some_eq_coe] using hexitPoint
  -- Truncation does not alter this bounded first-exit index, so the preceding
  -- prefix is precisely a surviving prefix.
  have hKone : 1 ≤ K := by omega
  have hactiveLength : activePrefixLength run X K ω = j := by
    rw [activePrefixLength, ← hj, WithTop.untopD_coe, min_eq_right hjUpper]
  have hjPredLtK : j - 1 < K := by omega
  have hjSurvival : ω ∈ survivalEvent run X (j - 1) := by
    have hspec := (activePrefixLength_spec run X K hKone ω).2.2
      (j - 1) hjPredLtK
    apply hspec.mp
    rw [hactiveLength]
    omega
  have hobjective := objectiveAtPrefixEnd_le_of_survival j hjLower X initial_mem
    run h_region ω hjSurvival
  have hconstraint := constraintNorm_le_of_survival run X initial_mem h_region
    ω j hjLower hjSurvival
  -- The same active-prefix normalization identifies the error sum in that
  -- deterministic bound with the stopped pathwise error energy.
  have hactiveError :
      activeErrorEnergyReal run X K ω =
        ∑ k ∈ Finset.range j, ‖run.gradientError k ω‖ ^ 2 := by
    unfold activeErrorEnergyReal
    rw [activePrefixSum_eq run X K hKone ω
        (fun k ω' ↦ ‖run.gradientError k ω'‖ ^ 2),
      hactiveLength]
  refine ⟨j, ⟨hjLower, hjUpper⟩, hjOutside, ?_, hconstraint⟩
  rw [hactiveError]
  exact hobjective

/-- Helper for Theorem 3.7: exiting by the horizon forces the active error
energy above the confidence-scaled scheduled allowance. -/
private lemma exit_imp_activeErrorEnergy_ge
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (hω : exitTime run X ω ≤ K) :
    ENNReal.ofReal (errorAverageConstant h oracle params / confidence) ≤
      activeErrorEnergy run X K ω := by
  -- Compare the controlled first-exit objective with sublevel containment.
  obtain ⟨j, hj, hjOutside, hobjectiveUpper, hconstraint⟩ :=
    objectiveAtExit_le K hK confidence X initial_mem run h_region ω hω
  have hobjectiveLower :
      objectiveBound h oracle params confidence < f (run.point j ω) := by
    apply lt_of_not_ge
    intro hobjective
    apply hjOutside
    apply h_region.sublevel_subset
    exact (mem_sublevel h oracle params confidence _).2
      ⟨hobjective, hconstraint⟩
  have hcoefficientPos : 0 < lyapunovErrorConstant h params :=
    lyapunovErrorConstant_pos
  rw [objectiveBound_def] at hobjectiveLower
  have hnormalizeErrorThreshold :
      2 * lyapunovErrorConstant h params * errorAverageConstant h oracle params /
          confidence =
        2 * lyapunovErrorConstant h params *
          (errorAverageConstant h oracle params / confidence) := by
    ring
  rw [hnormalizeErrorThreshold] at hobjectiveLower
  have hactiveLower :
      errorAverageConstant h oracle params / confidence <
        activeErrorEnergyReal run X K ω := by
    nlinarith
  rw [activeErrorEnergy_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal hactiveLower.le

/-- Theorem 3.7 (1): under the prescribed SPIDER schedule and localization
conditions, including the source's explicit hypothesis `x₀ ∈ X`, the
probability of leaving `X` by iteration `K` is at most `confidence`. -/
theorem exitProbability_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    ℙ {ω | exitTime run X ω ≤ K} ≤ ENNReal.ofReal confidence := by
  -- A first exit is contained in the Markov event for active error energy.
  have herrorPos : 0 < errorAverageConstant h oracle params :=
    errorAverageConstant_pos X initial_mem h_region
  have hthresholdPos :
      0 < errorAverageConstant h oracle params / confidence :=
    div_pos herrorPos confidence_pos
  have hexitSubset :
      {ω | exitTime run X ω ≤ K} ⊆
        {ω | ENNReal.ofReal (errorAverageConstant h oracle params / confidence) ≤
          activeErrorEnergy run X K ω} := by
    intro ω hω
    exact exit_imp_activeErrorEnergy_ge K hK confidence X
      initial_mem run h_region ω hω
  have hmarkov := measure_activeErrorEnergy_ge_le run X hX initial_mem h_region K
    (errorAverageConstant h oracle params / confidence) hthresholdPos
  have hstopped :=
    (scheduledStoppedEnergyBounds K hK X hX initial_mem run h_region).1
  have hquotient :
      stoppedErrorEnergy run X K /
          (errorAverageConstant h oracle params / confidence) ≤
        errorAverageConstant h oracle params /
          (errorAverageConstant h oracle params / confidence) :=
    (div_le_div_iff_of_pos_right hthresholdPos).2 hstopped
  have hcancel :
      errorAverageConstant h oracle params /
          (errorAverageConstant h oracle params / confidence) = confidence := by
    field_simp [herrorPos.ne', confidence_pos.ne']
  calc
    ℙ {ω | exitTime run X ω ≤ K} ≤
        ℙ {ω | ENNReal.ofReal
            (errorAverageConstant h oracle params / confidence) ≤
          activeErrorEnergy run X K ω} := measure_mono hexitSubset
    _ ≤ ENNReal.ofReal
        (stoppedErrorEnergy run X K /
          (errorAverageConstant h oracle params / confidence)) := hmarkov
    _ ≤ ENNReal.ofReal
        (errorAverageConstant h oracle params /
          (errorAverageConstant h oracle params / confidence)) :=
      ENNReal.ofReal_le_ofReal hquotient
    _ = ENNReal.ofReal confidence := by rw [hcancel]

/-- Companion to Theorem 3.7 (2): under the same localization conditions, the run survives
through iteration `K` with probability at least `1 - confidence`. -/
theorem survivalProbability_ge
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    ENNReal.ofReal (1 - confidence) ≤ ℙ (survivalEvent run X K) := by
  let exitEvent : Set Ω := {ω | exitTime run X ω ≤ K}
  have hexitEvent :
      exitEvent = ⋃ j ∈ Finset.Icc 1 K, run.point j ⁻¹' Xᶜ := by
    ext ω
    simp only [exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  have hexitNullMeasurable : NullMeasurableSet exitEvent ℙ := by
    rw [hexitEvent]
    exact (Finset.Icc 1 K).nullMeasurableSet_biUnion fun j _hj ↦
      (run.aemeasurable_point j).nullMeasurableSet_preimage hX.compl
  have hsurvival : survivalEvent run X K = exitEventᶜ := by
    ext ω
    rw [mem_survivalEvent]
    simp only [Set.mem_compl_iff, exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  have hexit : ℙ exitEvent ≤ ENNReal.ofReal confidence := by
    exact exitProbability_le K hK confidence confidence_pos X hX initial_mem run h_region
  rw [hsurvival, prob_compl_eq_one_sub₀ hexitNullMeasurable,
    ENNReal.ofReal_sub 1 confidence_pos.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hexit 1

/-- Companion to Theorem 3.7 (3): under the source's localization conditions, on survival
through `K` every segment in the length-`K` prefix lies in the regularity region. -/
theorem survival_imp_prefixAdmissible
    (K : ℕ) (confidence : ℝ) (_confidence_pos : 0 < confidence)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (hω : ω ∈ survivalEvent run X K) (k : ℕ) (hk : k < K) :
    segment ℝ (run.point k ω) (run.point (k + 1) ω) ⊆ h.region := by
  exact preExitSegment run X initial_mem h_region ω k
    (survivalEvent_antitone run X (Nat.le_of_lt hk) hω)


end Localization

namespace UniformOutput

open Localization

/-- Helper for Theorem 3.7: adjacent pairs of a nonnegative sequence are
bounded by twice its full prefix sum. -/
private lemma sumAdjacent_le_two_range (a : ℕ → ℝ) (K : ℕ) (hK : 2 ≤ K)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1))) ≤
      2 * ∑ k ∈ Finset.range K, a k := by
  -- Replace the closed output interval by the half-open prefix interval.
  have hinterval : Finset.Icc 1 (K - 1) = Finset.Ico 1 K := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hshift :
      (∑ k ∈ Finset.Icc 1 (K - 1), a (k - 1)) =
        ∑ k ∈ Finset.range (K - 1), a k := by
    rw [hinterval, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    omega
  -- Both shifted copies are bounded by the same nonnegative prefix sum.
  have hrangeIndex : K - 1 ≤ K := by omega
  have hrange :
      (∑ k ∈ Finset.range (K - 1), a k) ≤ ∑ k ∈ Finset.range K, a k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hrangeIndex) (fun k _ _ ↦ ha k)
  have honeLeK : 1 ≤ K := by omega
  have hrangeSplit :
      (∑ k ∈ Finset.range K, a k) =
        a 0 + ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
    rw [hinterval, Finset.sum_range_eq_add_Ico a honeLeK]
  rw [Finset.sum_add_distrib, hshift, hrangeSplit]
  linarith [ha 0]

/-- Helper for Theorem 3.7: restricting a product integral with a finite
uniform first coordinate is bounded by the uniform average of its sections. -/
private lemma setLIntegral_uniform_le_sum
    (K : ℕ) (hK : 2 ≤ K) (S : Set Ω) (g : ℕ × Ω → ℝ≥0∞) :
    ∫⁻ output in Set.univ ×ˢ S, g output ∂measure K hK ℙ ≤
      (∑ k ∈ Finset.Icc 1 (K - 1), ∫⁻ ω in S, g (k, ω) ∂ℙ) /
        (Finset.Icc 1 (K - 1)).card := by
  -- Tonelli's inequality reduces the restricted product integral to sections.
  let s := Finset.Icc 1 (K - 1)
  let p := indexLaw K hK
  change (∫⁻ output in Set.univ ×ˢ S, g output ∂p.toMeasure.prod ℙ) ≤ _
  rw [← Measure.prod_restrict]
  calc
    (∫⁻ output, g output ∂
        (p.toMeasure.restrict Set.univ).prod (ℙ.restrict S)) ≤
        ∫⁻ k in Set.univ, ∫⁻ ω in S, g (k, ω) ∂ℙ ∂p.toMeasure :=
      lintegral_prod_le g
    _ = ∑' k, (∫⁻ ω in S, g (k, ω) ∂ℙ) * p.toMeasure {k} := by
      rw [Measure.restrict_univ, lintegral_countable']
    _ = ∑ k ∈ s, (∫⁻ ω in S, g (k, ω) ∂ℙ) * (s.card : ℝ≥0∞)⁻¹ := by
      have hp (k : ℕ) :
          p.toMeasure {k} =
            if k ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
        rw [PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)]
        change (PMF.uniformOfFinset s _) k = _
        by_cases hk : k ∈ s
        · simp only [PMF.uniformOfFinset_apply, if_pos hk]
        · simp only [PMF.uniformOfFinset_apply, if_neg hk]
      simp_rw [hp]
      rw [tsum_eq_sum (s := s)]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos hk]
      · intro k hk
        rw [if_neg hk, mul_zero]
    _ = (∑ k ∈ Finset.Icc 1 (K - 1), ∫⁻ ω in S, g (k, ω) ∂ℙ) /
        (Finset.Icc 1 (K - 1)).card := by
      rw [ENNReal.div_eq_inv_mul, mul_comm, Finset.sum_mul]

/-- Helper for Theorem 3.7: on survival through `K`, a fixed residual is
bounded by the adjacent step and estimator-error energies. -/
private lemma residualSq_le_of_survival
    (K : ℕ) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (ω : Ω) (hω : ω ∈ survivalEvent run X K)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk : k < K) :
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 ≤
      LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- Extract precisely the current and preceding fixed-path bounds from survival.
  have hbounds := preExitPrefixBounds run X initial_mem h_region ω K hω
  have hsegmentCurrent := hbounds.1 k (by omega)
  have hsegmentPreviousRaw := hbounds.1 (k - 1) (by omega)
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hsegmentPrevious :
      segment ℝ (run.point (k - 1) ω) (run.point k ω) ⊆ h.region := by
    simpa only [hpred] using hsegmentPreviousRaw
  have hstepCurrent := hbounds.2.1 k (by omega)
  have hstepPrevious := hbounds.2.1 (k - 1) (by omega)
  have hmultiplierCurrent := hbounds.2.2 k (by omega)
  have hmultiplierNext := hbounds.2.2 (k + 1) (by omega)
  exact residualSq_le_of_pathBounds run k hk_pos ω hsegmentCurrent
    hsegmentPrevious hstepCurrent hstepPrevious hmultiplierCurrent
    hmultiplierNext

/-- Helper for Theorem 3.7: a surviving fixed-index residual section is
controlled by its four neighboring restricted energy integrals. -/
private lemma survivalRestrictedResidualSection_le
    (K : ℕ) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk : k < K) :
    (∫⁻ ω in survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω) ^ 2) ∂ℙ) ≤
      ENNReal.ofReal
        (LALM.stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
          ((∫ ω in survivalEvent run X K, ‖run.step k ω‖ ^ 2 ∂ℙ) +
            (∫ ω in survivalEvent run X K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ((∫ ω in survivalEvent run X K, ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
              ∫ ω in survivalEvent run X K,
                ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ))) := by
  -- Restrict every neighboring moment to the common terminal survival event.
  let C : ℝ := LALM.stochasticResidualConstant h params.delta params.beta params.rho
    params.multiplierBound
  let moments : Ω → ℝ := fun ω ↦
    ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
      ‖run.gradientError k ω‖ ^ 2 + ‖run.gradientError (k - 1) ω‖ ^ 2
  have hkPrev : k - 1 < K := by omega
  have hsurvivalK := nullMeasurableSet_survivalEvent run X hX K
  have hsubsetK : survivalEvent run X K ⊆ survivalEvent run X k :=
    survivalEvent_antitone run X (Nat.le_of_lt hk)
  have hsubsetPrev : survivalEvent run X K ⊆ survivalEvent run X (k - 1) :=
    survivalEvent_antitone run X (Nat.le_of_lt hkPrev)
  have hstepK : IntegrableOn (fun ω ↦ ‖run.step k ω‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_stepSquare_preExit run X hX initial_mem h_region k).mono_set
      hsubsetK
  have hstepPrev : IntegrableOn (fun ω ↦ ‖run.step (k - 1) ω‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_stepSquare_preExit run X hX initial_mem h_region (k - 1)).mono_set
      hsubsetPrev
  have herrorK : IntegrableOn (fun ω ↦ ‖run.gradientError k ω‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k).mono_set
      hsubsetK
  have herrorPrev : IntegrableOn (fun ω ↦ ‖run.gradientError (k - 1) ω‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region (k - 1)).mono_set
      hsubsetPrev
  have hmoments : IntegrableOn moments (survivalEvent run X K) ℙ :=
    ((hstepK.add hstepPrev).add herrorK).add herrorPrev
  have hC : 0 ≤ C := stochasticResidualConstant_nonneg
  have hright : IntegrableOn (fun ω ↦ C * moments ω)
      (survivalEvent run X K) ℙ := hmoments.const_mul C
  have hmomentsNonneg (ω : Ω) : 0 ≤ moments ω := by
    dsimp only [moments]
    positivity
  have hrightNonneg :
      0 ≤ᵐ[ℙ.restrict (survivalEvent run X K)] fun ω ↦ C * moments ω :=
    ae_of_all _ fun ω ↦ mul_nonneg hC (hmomentsNonneg ω)
  -- Expand the restricted integral only after applying the pathwise comparison.
  have hmomentsIntegral :
      (∫ ω in survivalEvent run X K, moments ω ∂ℙ) =
        (∫ ω in survivalEvent run X K, ‖run.step k ω‖ ^ 2 ∂ℙ) +
          (∫ ω in survivalEvent run X K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
          ((∫ ω in survivalEvent run X K, ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ) := by
    have hfirst := integral_add hstepK hstepPrev
    have hsecond := integral_add (hstepK.add hstepPrev) herrorK
    have hthird := integral_add ((hstepK.add hstepPrev).add herrorK) herrorPrev
    have hsecond' :
        (∫ ω in survivalEvent run X K,
          ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
            ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
          (∫ ω in survivalEvent run X K,
            ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError k ω‖ ^ 2 ∂ℙ := by
      simpa only [Pi.add_apply] using hsecond
    calc
      (∫ ω in survivalEvent run X K, moments ω ∂ℙ) =
          (∫ ω in survivalEvent run X K,
            ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
              ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        simpa only [moments, Pi.add_apply] using hthird
      _ = ((∫ ω in survivalEvent run X K,
              ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        rw [hsecond']
      _ = (((∫ ω in survivalEvent run X K, ‖run.step k ω‖ ^ 2 ∂ℙ) +
              ∫ ω in survivalEvent run X K,
                ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        rw [hfirst]
      _ = (∫ ω in survivalEvent run X K, ‖run.step k ω‖ ^ 2 ∂ℙ) +
          (∫ ω in survivalEvent run X K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
          ((∫ ω in survivalEvent run X K, ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω in survivalEvent run X K,
              ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ) := by
        ring
  calc
    (∫⁻ ω in survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω) ^ 2) ∂ℙ) ≤
        ∫⁻ ω in survivalEvent run X K, ENNReal.ofReal (C * moments ω) ∂ℙ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem₀ hsurvivalK] with ω hω
      apply ENNReal.ofReal_le_ofReal
      exact residualSq_le_of_survival K confidence X initial_mem run h_region
        ω hω k hk_pos hk
    _ = ENNReal.ofReal
        (∫ ω in survivalEvent run X K, C * moments ω ∂ℙ) :=
      (ofReal_integral_eq_lintegral_ofReal hright hrightNonneg).symm
    _ = ENNReal.ofReal
        (LALM.stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
          ((∫ ω in survivalEvent run X K, ‖run.step k ω‖ ^ 2 ∂ℙ) +
            (∫ ω in survivalEvent run X K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ((∫ ω in survivalEvent run X K, ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
              ∫ ω in survivalEvent run X K,
                ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ))) := by
      rw [integral_const_mul, hmomentsIntegral]

/-- Helper for Theorem 3.7: the survival-restricted uniform-output residual
numerator is bounded by the canonical complexity constant divided by `K - 1`. -/
private lemma survivalRestrictedResidualLIntegral_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    (∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (point run output) (multiplier run output) ^ 2)
          ∂measure K hK ℙ) ≤
      ENNReal.ofReal (complexityConstant h oracle params / ((K : ℝ) - 1)) := by
  -- Use one common terminal survival set for all fixed-index sections.
  let S : Set Ω := survivalEvent run X K
  let C : ℝ := LALM.stochasticResidualConstant h params.delta params.beta params.rho
    params.multiplierBound
  let a : ℕ → ℝ := fun k ↦
    (∫ ω in S, ‖run.step k ω‖ ^ 2 ∂ℙ) +
      ∫ ω in S, ‖run.gradientError k ω‖ ^ 2 ∂ℙ
  have hC : 0 ≤ C := stochasticResidualConstant_nonneg
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp only [a]
    exact add_nonneg (integral_nonneg fun ω ↦ sq_nonneg _)
      (integral_nonneg fun ω ↦ sq_nonneg _)
  -- Terminally restricted moments are dominated termwise by the stopped energies.
  have hstepRestricted :
      (∑ k ∈ Finset.range K, ∫ ω in S, ‖run.step k ω‖ ^ 2 ∂ℙ) ≤
        stoppedStepEnergy run X K := by
    rw [stoppedStepEnergy]
    apply Finset.sum_le_sum
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    have hsubset : S ⊆ survivalEvent run X k :=
      survivalEvent_antitone run X (Nat.le_of_lt hklt)
    have hintegrable : IntegrableOn (fun ω ↦ ‖run.step k ω‖ ^ 2)
        (survivalEvent run X k) ℙ :=
      integrableOn_stepSquare_preExit run X hX initial_mem h_region k
    exact setIntegral_mono_set hintegrable
      (ae_of_all _ fun ω ↦ sq_nonneg ‖run.step k ω‖)
      (ae_of_all _ hsubset)
  have herrorRestricted :
      (∑ k ∈ Finset.range K,
        ∫ ω in S, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) ≤
        stoppedErrorEnergy run X K := by
    rw [stoppedErrorEnergy]
    apply Finset.sum_le_sum
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    have hsubset : S ⊆ survivalEvent run X k :=
      survivalEvent_antitone run X (Nat.le_of_lt hklt)
    have hintegrable :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact setIntegral_mono_set hintegrable
      (ae_of_all _ fun ω ↦ sq_nonneg ‖run.gradientError k ω‖)
      (ae_of_all _ hsubset)
  have htotalRange :
      (∑ k ∈ Finset.range K, a k) ≤
        stoppedStepEnergy run X K + stoppedErrorEnergy run X K := by
    dsimp only [a]
    rw [Finset.sum_add_distrib]
    exact add_le_add hstepRestricted herrorRestricted
  have hstopped := scheduledStoppedEnergyBounds K hK X hX initial_mem run h_region
  have htotalAllowance :
      (∑ k ∈ Finset.range K, a k) ≤
        stepAverageConstant h oracle params + errorAverageConstant h oracle params :=
    htotalRange.trans (add_le_add hstopped.2 hstopped.1)
  have hadjacent := sumAdjacent_le_two_range a K hK ha
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hrealSum :
      (∑ k ∈ Finset.Icc 1 (K - 1), C * (a k + a (k - 1))) ≤
        complexityConstant h oracle params := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1), C * (a k + a (k - 1))) =
          C * ∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1)) := by
        rw [Finset.mul_sum]
      _ ≤ C * (2 * ∑ k ∈ Finset.range K, a k) :=
        mul_le_mul_of_nonneg_left hadjacent hC
      _ ≤ C * (2 * (stepAverageConstant h oracle params +
          errorAverageConstant h oracle params)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact mul_le_mul_of_nonneg_left htotalAllowance htwoNonneg
      _ = complexityConstant h oracle params := by
        rw [complexityConstant_def]
        ring
  -- Sum the verified fixed-section estimates and normalize the uniform card.
  have htermNonneg (k : ℕ) (_hk : k ∈ Finset.Icc 1 (K - 1)) :
      0 ≤ C * (a k + a (k - 1)) :=
    mul_nonneg hC (add_nonneg (ha k) (ha (k - 1)))
  have hfixedSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        ∫⁻ ω in S,
          ENNReal.ofReal
            (KKT.residual f c (point run (k, ω))
              (multiplier run (k, ω)) ^ 2) ∂ℙ) ≤
        ENNReal.ofReal (complexityConstant h oracle params) := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
        ∫⁻ ω in S,
          ENNReal.ofReal
            (KKT.residual f c (point run (k, ω))
              (multiplier run (k, ω)) ^ 2) ∂ℙ) ≤
          ∑ k ∈ Finset.Icc 1 (K - 1),
            ENNReal.ofReal (C * (a k + a (k - 1))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkbounds := Finset.mem_Icc.mp hk
        have hklt : k < K := by omega
        simpa only [S, C, a, point_apply, multiplier_apply] using
          survivalRestrictedResidualSection_le K confidence X hX initial_mem run
            h_region k hkbounds.1 hklt
      _ = ENNReal.ofReal
          (∑ k ∈ Finset.Icc 1 (K - 1), C * (a k + a (k - 1))) :=
        (ENNReal.ofReal_sum_of_nonneg htermNonneg).symm
      _ ≤ ENNReal.ofReal (complexityConstant h oracle params) :=
        ENNReal.ofReal_le_ofReal hrealSum
  have huniform := setLIntegral_uniform_le_sum (ℙ := ℙ) K hK S
    (fun output ↦ ENNReal.ofReal
      (KKT.residual f c (point run output) (multiplier run output) ^ 2))
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hKnatOne : 1 < K := by omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnatOne
  have hdenominator : 0 < (K : ℝ) - 1 := by linarith
  have hOneNonneg : (0 : ℝ) ≤ 1 := by norm_num
  calc
    (∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (point run output) (multiplier run output) ^ 2)
          ∂measure K hK ℙ) ≤
        (∑ k ∈ Finset.Icc 1 (K - 1),
          ∫⁻ ω in S,
            ENNReal.ofReal
              (KKT.residual f c (point run (k, ω))
                (multiplier run (k, ω)) ^ 2) ∂ℙ) /
          (Finset.Icc 1 (K - 1)).card := by
      simpa only [S] using huniform
    _ ≤ ENNReal.ofReal (complexityConstant h oracle params) /
        (Finset.Icc 1 (K - 1)).card :=
      ENNReal.div_le_div_right hfixedSum _
    _ = ENNReal.ofReal
        (complexityConstant h oracle params / ((K : ℝ) - 1)) := by
      rw [hcard, ENNReal.natCast_sub, Nat.cast_one,
        ENNReal.ofReal_div_of_pos hdenominator,
        ENNReal.ofReal_sub (K : ℝ) hOneNonneg,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- Companion to Theorem 3.7 (4): conditioned on survival, the independent uniform output
has squared KKT residual mean at most `C_st / ((1 - confidence) * (K - 1))`. -/
theorem conditionalResidualMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    conditionalResidualMeanSquare run K hK X ≤
      ENNReal.ofReal
        (complexityConstant h oracle params / ((1 - confidence) * ((K : ℝ) - 1))) := by
  -- Bound the restricted numerator and invert the positive survival lower bound.
  have hnumerator := survivalRestrictedResidualLIntegral_le K hK confidence X hX
    initial_mem run h_region
  have hsurvival := survivalProbability_ge K hK confidence confidence_pos X hX
    initial_mem run h_region
  have honeMinusConfidence : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hprobabilityInv :
      (ℙ (survivalEvent run X K))⁻¹ ≤ (ENNReal.ofReal (1 - confidence))⁻¹ :=
    ENNReal.inv_le_inv.mpr hsurvival
  have hKnatOne : 1 < K := by omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnatOne
  have hKdenominator : 0 < (K : ℝ) - 1 := by linarith
  have hrealQuotient :
      (complexityConstant h oracle params / ((K : ℝ) - 1)) /
          (1 - confidence) =
        complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1)) := by
    field_simp [honeMinusConfidence.ne', hKdenominator.ne']
  -- The conditional formula is multiplication by the inverse survival mass.
  rw [conditionalResidualMeanSquare_eq_inv_mul_setLIntegral]
  calc
    (ℙ (survivalEvent run X K))⁻¹ *
        (∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
          ENNReal.ofReal
            (KKT.residual f c (point run output) (multiplier run output) ^ 2)
            ∂measure K hK ℙ) ≤
        (ENNReal.ofReal (1 - confidence))⁻¹ *
          (∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
            ENNReal.ofReal
              (KKT.residual f c (point run output) (multiplier run output) ^ 2)
              ∂measure K hK ℙ) :=
      mul_le_mul_of_nonneg_right hprobabilityInv zero_le
    _ ≤ (ENNReal.ofReal (1 - confidence))⁻¹ *
        ENNReal.ofReal
          (complexityConstant h oracle params / ((K : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hnumerator zero_le
    _ = ENNReal.ofReal
        ((complexityConstant h oracle params / ((K : ℝ) - 1)) /
          (1 - confidence)) := by
      rw [← ENNReal.div_eq_inv_mul,
        ← ENNReal.ofReal_div_of_pos honeMinusConfidence]
    _ = ENNReal.ofReal
        (complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
      rw [hrealQuotient]


end UniformOutput

end LALM.StochasticRun

end
