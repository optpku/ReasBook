/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.DeterministicPrefix
public import TR_LALM_theory.Corollary_4_2.StochasticPathwise

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: the derivative of the explicit-gradient model is
represented by its first-order stationarity vector. -/
private lemma hasFDerivAtStepModelWithGradient
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (LALM.stepModelWithGradient c g ρ β x multiplier)
      (innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p)) p := by
  -- Differentiate the affine constraint model once and reuse it in both terms.
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
      (fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2)
      ((ρ / 2) • 2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))) p := by
    simpa only [EqualityConstrained.constraintGradient_def,
      ContinuousLinearMap.innerSL_apply_comp] using
        haffine.norm_sq.const_mul (ρ / 2)
  have hproximal : HasFDerivAt (fun q ↦ (β / 2) * ‖q‖ ^ 2)
      ((β / 2) • 2 • innerSL ℝ p) p := by
    simpa only [id_eq, ContinuousLinearMap.comp_id] using
      (hasFDerivAt_id p).norm_sq.const_mul (β / 2)
  -- Collect the four derivatives in the canonical stationarity spelling.
  let modelDerivative : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ((innerSL ℝ g +
        innerSL ℝ (EqualityConstrained.constraintGradient c x multiplier)) +
      ((ρ / 2) • (2 • innerSL ℝ (EqualityConstrained.constraintGradient c x
        (c x + fderiv ℝ c x p))))) + ((β / 2) • (2 • innerSL ℝ p))
  have hsum : HasFDerivAt
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (β / 2) * ‖q‖ ^ 2) modelDerivative p := by
    simpa only [modelDerivative] using
      ((hobjective.add hmultiplier).add hpenalty).add hproximal
  have hderivativeEq : modelDerivative =
      innerSL ℝ (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p) := by
    ext v
    simp only [map_add, map_smul, innerSL_apply_apply, add_apply, smul_apply,
      EqualityConstrained.constraintGradient_def, modelDerivative]
    ring
  have hfunctions : LALM.stepModelWithGradient c g ρ β x multiplier =ᶠ[nhds p]
      ((((fun q ↦ ⟪g, q⟫_ℝ) +
          fun q ↦ ⟪multiplier, c x + fderiv ℝ c x q⟫_ℝ) +
          fun q ↦ (ρ / 2) * ‖c x + fderiv ℝ c x q‖ ^ 2) +
        fun q ↦ (β / 2) * ‖q‖ ^ 2) := by
    filter_upwards with q
    exact LALM.stepModelWithGradient_def c g ρ β x multiplier q
  exact (hsum.congr_of_eventuallyEq hfunctions).congr_fderiv hderivativeEq

/-- Helper for Corollary 4.2: a minimizer of the explicit-gradient model
satisfies its canonical first-order equation. -/
theorem stepModelWithGradientOptimality
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g ρ β x multiplier) Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p = 0 := by
  -- Fermat's rule annihilates the explicit derivative computed above.
  have hderivative : innerSL ℝ
      (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p) = 0 :=
    (hp.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
      (hasFDerivAtStepModelWithGradient g ρ β x multiplier p)
  have hnormSq :
      ‖g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p‖ ^ 2 = 0 := by
    simpa only [innerSL_apply_apply, real_inner_self_eq_norm_sq, zero_apply] using
      congrArg (fun A ↦ A (g + EqualityConstrained.constraintGradient c x
        (multiplier + ρ • (c x + fderiv ℝ c x p)) + β • p)) hderivative
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)

/-- Helper for Corollary 4.2: explicit-gradient model optimality gives the
corrected perturbed-multiplier identity. -/
theorem perturbedMultiplierIdentityWithGradient
    (g : EuclideanSpace ℝ (Fin n)) (ρ β : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g ρ β x multiplier) Set.univ p) :
    g + EqualityConstrained.constraintGradient c x
        (nextMultiplier c ρ x multiplier p) + β • p =
      ρ • EqualityConstrained.constraintGradient c x (error c x p) := by
  -- Expand the corrected update and eliminate its linearized part by stationarity.
  rw [nextMultiplier_def, error_def]
  simp only [map_add, map_sub, map_smul]
  have hstationary := stepModelWithGradientOptimality g ρ β x multiplier p hp
  simp only [map_add, map_smul] at hstationary
  linear_combination (norm := module) hstationary

/-- Helper for Corollary 4.2: an admissible bounded corrected base step controls
the scaled constraint-gradient image of its nonlinear correction error. -/
theorem normScaledConstraintGradientError_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x p : EuclideanSpace ℝ (Fin n))
    (hadm : IsAdmissible h x p) (hstep : ‖p‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
      params.rho * h.constraintGradientBound * errorFactor h params.delta *
        (params.delta : ℝ) ^ 2 := by
  -- First bound the nonlinear error, then apply the constraint-gradient operator.
  have hx := base_mem_region h x p hadm
  have herror := norm_error_le_factor h params.delta x p hadm hstep
  have hstepSq : ‖p‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have herrorFactorNonneg : 0 ≤ errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  have herrorBound :
      ‖error c x p‖ ≤ errorFactor h params.delta * (params.delta : ℝ) ^ 2 :=
    herror.trans (mul_le_mul_of_nonneg_left hstepSq herrorFactorNonneg)
  have hoperator := h.norm_constraintGradient_le x hx
  have hρ : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
        params.rho *
          (‖EqualityConstrained.constraintGradient c x‖ * ‖error c x p‖) :=
      mul_le_mul_of_nonneg_left
        ((EqualityConstrained.constraintGradient c x).le_opNorm (error c x p)) hρ.le
    _ ≤ params.rho *
        (h.constraintGradientBound *
          (errorFactor h params.delta * (params.delta : ℝ) ^ 2)) := by
      gcongr
    _ = params.rho * h.constraintGradientBound * errorFactor h params.delta *
        (params.delta : ℝ) ^ 2 := by ring

/-- Helper for Corollary 4.2: bounded explicit-gradient model data control the
constraint-gradient image of the corrected next multiplier. -/
theorem normConstraintGradient_nextMultiplier_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (g : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g params.rho params.beta x multiplier)
      Set.univ p)
    (hadm : IsAdmissible h x p) (hstep : ‖p‖ ≤ params.delta)
    (hgradient : ‖g‖ ≤ h.gradientBound) :
    ‖EqualityConstrained.constraintGradient c x
        (nextMultiplier c params.rho x multiplier p)‖ ≤
      h.gradientBound + params.beta * params.delta +
        params.rho * h.constraintGradientBound * errorFactor h params.delta *
          (params.delta : ℝ) ^ 2 := by
  -- Normalize perturbed stationarity, then combine the three norm bounds.
  have hperturbed := perturbedMultiplierIdentityWithGradient
    g params.rho params.beta x multiplier p hp
  have hidentity :
      EqualityConstrained.constraintGradient c x
          (nextMultiplier c params.rho x multiplier p) =
        -g - (params.beta : ℝ) • p +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c x (error c x p) := by
    linear_combination (norm := module) hperturbed
  have hperturbation := normScaledConstraintGradientError_le h params x p hadm hstep
  have hβ : 0 < (params.beta : ℝ) := params.spec.1.2.1
  rw [hidentity]
  calc
    ‖-g - params.beta • p +
        (params.rho : ℝ) • EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
        ‖-g - params.beta • p‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
            (error c x p)‖ := norm_add_le _ _
    _ ≤ (‖g‖ + params.beta * ‖p‖) +
        ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x
          (error c x p)‖ := by
      gcongr
      calc
        ‖-g - (params.beta : ℝ) • p‖ ≤ ‖-g‖ + ‖(params.beta : ℝ) • p‖ :=
          norm_sub_le _ _
        _ = ‖g‖ + params.beta * ‖p‖ := by
          rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    _ ≤ h.gradientBound + params.beta * params.delta +
        params.rho * h.constraintGradientBound * errorFactor h params.delta *
          (params.delta : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hstep hβ.le]

namespace StochasticRun

variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

/-- Helper for Corollary 4.2: bounded corrected stochastic multipliers control
the effective multiplier in one pathwise normal equation. -/
lemma normEffectiveMultiplier_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hMultiplier : ∀ j ≤ k, ‖run.multiplier j ω‖ ≤ params.multiplierBound) :
    ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
      3 * (params.multiplierBound : ℝ) := by
  cases k with
  | zero =>
      -- Initialization is controlled by the two defining parameter bounds.
      rw [run.multiplier_zero, run.point_zero]
      calc
        ‖multiplier₀ + (params.rho : ℝ) • c x₀‖ ≤
            ‖multiplier₀‖ + ‖(params.rho : ℝ) • c x₀‖ := norm_add_le _ _
        _ = ‖multiplier₀‖ + params.rho * ‖c x₀‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1]
        _ ≤ 3 * params.multiplierBound := by
          have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
          linarith [params.norm_multiplier₀_le, params.initialResidual_le]
  | succ k =>
      -- The corrected update rewrites the effective multiplier as `2 λ_(k+1) - λ_k`.
      have hupdate :
          run.multiplier (k + 1) ω = run.multiplier k ω +
            (params.rho : ℝ) • c (run.point (k + 1) ω) := by
        rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
      have heffective :
          run.multiplier (k + 1) ω +
              (params.rho : ℝ) • c (run.point (k + 1) ω) =
            (2 : ℝ) • run.multiplier (k + 1) ω - run.multiplier k ω := by
        rw [hupdate]
        module
      rw [heffective]
      calc
        ‖(2 : ℝ) • run.multiplier (k + 1) ω - run.multiplier k ω‖ ≤
            ‖(2 : ℝ) • run.multiplier (k + 1) ω‖ +
              ‖run.multiplier k ω‖ := norm_sub_le _ _
        _ = 2 * ‖run.multiplier (k + 1) ω‖ + ‖run.multiplier k ω‖ := by
          rw [norm_smul, Real.norm_ofNat]
        _ ≤ 3 * params.multiplierBound := by
          have hnext := hMultiplier (k + 1) (Nat.le_refl _)
          have hprevious := hMultiplier k (Nat.le_succ k)
          have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
          linarith

/-- Helper for Corollary 4.2: regularity, clipping, and an effective-multiplier
bound control one corrected stochastic base step. -/
lemma normBaseStep_le_of_normEffectiveMultiplier_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) (hx : run.point k ω ∈ h.region)
    (heffective :
      ‖run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)‖ ≤
        3 * params.multiplierBound) :
    ‖run.baseStep k ω‖ ≤ params.delta := by
  -- Rearrange corrected stochastic model optimality into the damped normal equation.
  have hoptimal := stepModelWithGradientOptimality
    (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
    params.rho params.beta (run.point k ω) (run.multiplier k ω)
    (run.baseStep k ω) (run.minimizes_baseStep k ω)
  rw [← run.gradientEstimate_apply] at hoptimal
  have hequation :
      (params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • (fderiv ℝ c (run.point k ω)).adjoint
            (fderiv ℝ c (run.point k ω) (run.baseStep k ω)) =
        -run.gradientEstimate k ω -
          (fderiv ℝ c (run.point k ω)).adjoint
            (run.multiplier k ω + (params.rho : ℝ) • c (run.point k ω)) := by
    simp only [EqualityConstrained.constraintGradient_def, map_add, map_smul] at hoptimal ⊢
    linear_combination (norm := module) hoptimal
  have hβ : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hρ : 0 ≤ (params.rho : ℝ) := params.spec.1.2.2.1.le
  have hestimate := Run.normDampedNormalEquation_le
    (fderiv ℝ c (run.point k ω)) hβ hρ h.licqModulus_pos
    (h.licqLowerBound (run.point k ω) hx) (run.baseStep k ω)
    (run.gradientEstimate k ω)
    (run.multiplier k ω + params.rho • c (run.point k ω)) hequation
  -- Clipping supplies the bounded-gradient input required by the parameter choice.
  have hgradient : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
    rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
    exact SPIDER.norm_clip_le h.gradientBound _
  have hoperator :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le (run.point k ω) hx
  have hdenom :
      0 < (params.beta : ℝ) + params.rho * (h.licqModulus : ℝ) ^ 2 := by
    exact add_pos_of_pos_of_nonneg hβ
      (mul_nonneg hρ (sq_nonneg (h.licqModulus : ℝ)))
  have hgradientTerm :
      ‖run.gradientEstimate k ω‖ / params.beta ≤ h.gradientBound / params.beta :=
    (div_le_div_iff_of_pos_right hβ).2 hgradient
  have hproduct :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ *
          ‖run.multiplier k ω + params.rho • c (run.point k ω)‖ ≤
        h.constraintGradientBound * (3 * params.multiplierBound) :=
    mul_le_mul hoperator heffective (norm_nonneg _)
      (NNReal.coe_nonneg h.constraintGradientBound)
  have hconstraintTerm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ *
          ‖run.multiplier k ω + params.rho • c (run.point k ω)‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) ≤
        3 * h.constraintGradientBound * params.multiplierBound /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
    rw [div_le_div_iff_of_pos_right hdenom]
    nlinarith
  calc
    ‖run.baseStep k ω‖ ≤
        ‖run.gradientEstimate k ω‖ / params.beta +
          ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k ω))‖ *
            ‖run.multiplier k ω + params.rho • c (run.point k ω)‖ /
              (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Corollary 4.2: an admissible bounded corrected base step
propagates the pathwise multiplier bound through one iteration. -/
lemma normMultiplier_succ_le_of_normBaseStep_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω)
    (hadm : IsAdmissible h (run.point k ω) (run.baseStep k ω))
    (hstep : ‖run.baseStep k ω‖ ≤ params.delta) :
    ‖run.multiplier (k + 1) ω‖ ≤ params.multiplierBound := by
  -- Apply the normalized next-multiplier bound and then use LICQ.
  have hx := base_mem_region h (run.point k ω) (run.baseStep k ω) hadm
  have hgradient : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
    rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
    exact SPIDER.norm_clip_le h.gradientBound _
  have hminimizes :
      IsMinOn (LALM.stepModelWithGradient c (run.gradientEstimate k ω)
        params.rho params.beta (run.point k ω) (run.multiplier k ω))
        Set.univ (run.baseStep k ω) := by
    simpa only [run.gradientEstimate_apply] using run.minimizes_baseStep k ω
  have hnormalBound := normConstraintGradient_nextMultiplier_le h params
    (run.gradientEstimate k ω) (run.point k ω) (run.multiplier k ω)
    (run.baseStep k ω) hminimizes hadm hstep hgradient
  rw [← run.multiplier_succ k ω] at hnormalBound
  have hlicq := h.licqLowerBound (run.point k ω) hx (run.multiplier (k + 1) ω)
  have hscaled :
      (h.licqModulus : ℝ) * ‖run.multiplier (k + 1) ω‖ ≤
        h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            (params.delta : ℝ) ^ 2 := hlicq.trans hnormalBound
  have hquotient :
      ‖run.multiplier (k + 1) ω‖ ≤
        (h.gradientBound + params.beta * params.delta +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            (params.delta : ℝ) ^ 2) / h.licqModulus := by
    rw [le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)]
    simpa only [mul_comm] using hscaled
  exact hquotient.trans params.parameterBound_le

/-- Helper for Corollary 4.2: pathwise corrected prefix admissibility
simultaneously controls every base step and multiplier through the horizon. -/
theorem admissiblePrefix_normBounds
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (N : ℕ) (h_admissible : run.IsAdmissiblePrefix N) :
    (∀ k < N, ∀ ω, ‖run.baseStep k ω‖ ≤ params.delta) ∧
      (∀ k ≤ N, ∀ ω, ‖run.multiplier k ω‖ ≤ params.multiplierBound) := by
  -- Induct on completed iterations while carrying the mutually supporting bounds.
  induction N with
  | zero =>
      constructor
      · intro k hk
        omega
      · intro k hk ω
        have hkzero : k = 0 := by omega
        subst k
        rw [run.multiplier_zero]
        exact params.norm_multiplier₀_le
  | succ N ih =>
      have htransitions := (run.isAdmissiblePrefix_iff (N + 1)).1 h_admissible
      have hprefix : run.IsAdmissiblePrefix N :=
        (run.isAdmissiblePrefix_iff N).2 fun j hj ω ↦
          htransitions j (Nat.lt_succ_of_lt hj) ω
      have hbounds := ih hprefix
      have hnewStep (ω : Ω) : ‖run.baseStep N ω‖ ≤ params.delta := by
        have hadm := htransitions N (Nat.lt_succ_self N) ω
        have hx := base_mem_region h (run.point N ω) (run.baseStep N ω) hadm
        have heffective := run.normEffectiveMultiplier_le N ω
          (fun j hj ↦ hbounds.2 j hj ω)
        exact run.normBaseStep_le_of_normEffectiveMultiplier_le N ω hx heffective
      have hnewMultiplier (ω : Ω) :
          ‖run.multiplier (N + 1) ω‖ ≤ params.multiplierBound := by
        exact run.normMultiplier_succ_le_of_normBaseStep_le N ω
          (htransitions N (Nat.lt_succ_self N) ω) (hnewStep ω)
      constructor
      · intro k hk ω
        by_cases hkold : k < N
        · exact hbounds.1 k hkold ω
        · have hkeq : k = N := by omega
          simpa only [hkeq] using hnewStep ω
      · intro k hk ω
        by_cases hkold : k ≤ N
        · exact hbounds.2 k hkold ω
        · have hkeq : k = N + 1 := by omega
          simpa only [hkeq] using hnewMultiplier ω

/-- Helper for Corollary 4.2: a uniformly bounded corrected base step has an
integrable squared norm below a pathwise admissible horizon. -/
theorem integrable_baseStepSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N) :
    Integrable (fun ω ↦ ‖run.baseStep k ω‖ ^ 2) P := by
  -- Combine AE measurability with the uniform prefix bound and finite measure.
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.baseStep k ω‖ ^ 2) P :=
    ((run.aemeasurable_baseStep k).norm.pow_const 2).aestronglyMeasurable
  have hstep := (run.admissiblePrefix_normBounds N h_admissible).1 k hk
  have hbound (ω : Ω) :
      ‖(‖run.baseStep k ω‖ ^ 2 : ℝ)‖ ≤ (params.delta : ℝ) ^ 2 := by
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 (hstep ω)
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  exact Integrable.mono' (integrable_const _) hsquareMeasurable (ae_of_all P hbound)

/-- Helper for Corollary 4.2: squared corrected gradient errors are integrable
below a pathwise admissible horizon. -/
theorem integrable_gradientErrorSquare
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N) :
    Integrable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) P := by
  -- Establish measurability of clipping and use the regularity-region gradient extension.
  have hclipMeasurable : Measurable (SPIDER.clip h.gradientBound :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
    unfold SPIDER.clip
    apply Measurable.ite
    · exact measurableSet_le continuous_norm.measurable measurable_const
    · exact measurable_id
    · exact (measurable_const.div continuous_norm.measurable).smul measurable_id
  have hestimate : AEMeasurable (run.gradientEstimate k) P := by
    have hcomposed := hclipMeasurable.comp_aemeasurable
      (run.aemeasurable_rawEstimate k)
    have hestimateEq :
        run.gradientEstimate k =
          SPIDER.clip h.gradientBound ∘
            SPIDER.rawEstimate oracle run.point run.sample Q B b k := by
      funext ω
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      rfl
    rw [hestimateEq]
    exact hcomposed
  have hgradientExtension :
      AEMeasurable (fun ω ↦ h.objectiveGradientExtension (run.point k ω)) P :=
    h.measurable_objectiveGradientExtension.comp_aemeasurable
      (run.aemeasurable_point k)
  have hgradient :
      AEMeasurable (fun ω ↦ gradient f (run.point k ω)) P := by
    apply hgradientExtension.congr
    apply ae_of_all
    intro ω
    have hadm := (run.isAdmissiblePrefix_iff N).mp h_admissible k hk ω
    have hx := base_mem_region h (run.point k ω) (run.baseStep k ω) hadm
    exact h.objectiveGradientExtension_eq hx
  have herror : AEMeasurable (run.gradientError k) P := by
    have herrorEq :
        run.gradientError k =
          fun ω ↦ run.gradientEstimate k ω - gradient f (run.point k ω) := by
      funext ω
      exact run.gradientError_apply k ω
    rw [herrorEq]
    exact hestimate.sub hgradient
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) P :=
    (herror.norm.pow_const 2).aestronglyMeasurable
  -- Prefix admissibility bounds both summands of the gradient error uniformly.
  have hbound (ω : Ω) :
      ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤
        (2 * (h.gradientBound : ℝ)) ^ 2 := by
    have hadm := (run.isAdmissiblePrefix_iff N).mp h_admissible k hk ω
    have hx := base_mem_region h (run.point k ω) (run.baseStep k ω) hadm
    have hestimateNorm : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      exact SPIDER.norm_clip_le h.gradientBound _
    have hgradientNorm : ‖gradient f (run.point k ω)‖ ≤ h.gradientBound :=
      h.norm_gradient_le _ hx
    have herrorNorm :
        ‖run.gradientError k ω‖ ≤ 2 * (h.gradientBound : ℝ) := by
      rw [run.gradientError_apply]
      calc
        ‖run.gradientEstimate k ω - gradient f (run.point k ω)‖ ≤
            ‖run.gradientEstimate k ω‖ + ‖gradient f (run.point k ω)‖ :=
          norm_sub_le _ _
        _ ≤ 2 * (h.gradientBound : ℝ) := by linarith
    have hclipBoundNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) := by positivity
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) hclipBoundNonneg).2 herrorNorm
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  exact Integrable.mono' (integrable_const _)
    hsquareMeasurable (ae_of_all P hbound)

end StochasticRun

end LALM.Correction

end
