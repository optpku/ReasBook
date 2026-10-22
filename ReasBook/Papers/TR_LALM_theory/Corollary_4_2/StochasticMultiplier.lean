/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StochasticMoments

public section

open MeasureTheory
open scoped InnerProductSpace NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: a bounded admissible base step controls the
scaled constraint-gradient image of its corrected error linearly in the step norm. -/
lemma normScaledConstraintGradientError_le_mul_norm
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (x p : EuclideanSpace ℝ (Fin n))
    (hadm : IsAdmissible h x p) (hstep : ‖p‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
      params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta * ‖p‖ := by
  -- Apply the operator bound to the quadratic corrected error estimate.
  have hx := base_mem_region h x p hadm
  have hoperator := h.norm_constraintGradient_le x hx
  have herror := norm_error_le_factor h params.delta x p hadm hstep
  have happlication :
      ‖EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
        h.constraintGradientBound * ‖error c x p‖ :=
    (EqualityConstrained.constraintGradient c x).le_opNorm (error c x p) |>.trans
      (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have herrorApplied :
      ‖EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
        h.constraintGradientBound * (errorFactor h params.delta * ‖p‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror (NNReal.coe_nonneg h.constraintGradientBound))
  -- Use the radius bound on one factor while retaining the other step norm.
  have hstepProduct : ‖p‖ * ‖p‖ ≤ params.delta * ‖p‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound *
        errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c x (error c x p)‖ ≤
        params.rho *
          (h.constraintGradientBound * (errorFactor h params.delta * ‖p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left herrorApplied hrho.le
    _ = (params.rho * h.constraintGradientBound * errorFactor h params.delta) *
        (‖p‖ * ‖p‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound * errorFactor h params.delta) *
        (params.delta * ‖p‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta * ‖p‖ := by ring

namespace StochasticRun

variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

/-- Helper for Corollary 4.2: subtracting adjacent corrected stochastic
stationarity identities exposes the multiplier increment and both gradient errors. -/
lemma constraintGradientMultiplierIncrement
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (omega : Ω) :
    EqualityConstrained.constraintGradient c (run.point k omega)
        (run.multiplier (k + 1) omega - run.multiplier k omega) =
      (-(params.beta : ℝ) • run.baseStep k omega +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k omega)
            (error c (run.point k omega) (run.baseStep k omega))) +
        ((params.beta : ℝ) • run.baseStep (k - 1) omega -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) omega)
            (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))) +
        (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega))
            (run.multiplier k omega) +
        (run.gradientError (k - 1) omega - run.gradientError k omega) := by
  -- Align model minimizers with the run-facing estimator spelling.
  have hcurrentMinimizes :
      IsMinOn (LALM.stepModelWithGradient c (run.gradientEstimate k omega)
        params.rho params.beta (run.point k omega) (run.multiplier k omega))
          Set.univ (run.baseStep k omega) := by
    simpa only [run.gradientEstimate_apply] using run.minimizes_baseStep k omega
  have hpreviousMinimizes :
      IsMinOn (LALM.stepModelWithGradient c (run.gradientEstimate (k - 1) omega)
        params.rho params.beta (run.point (k - 1) omega)
          (run.multiplier (k - 1) omega)) Set.univ (run.baseStep (k - 1) omega) := by
    simpa only [run.gradientEstimate_apply] using run.minimizes_baseStep (k - 1) omega
  have hcurrent := perturbedMultiplierIdentityWithGradient
    (run.gradientEstimate k omega) params.rho params.beta
    (run.point k omega) (run.multiplier k omega) (run.baseStep k omega)
      hcurrentMinimizes
  have hprevious := perturbedMultiplierIdentityWithGradient
    (run.gradientEstimate (k - 1) omega) params.rho params.beta
    (run.point (k - 1) omega) (run.multiplier (k - 1) omega)
      (run.baseStep (k - 1) omega) hpreviousMinimizes
  -- Rewrite corrected next multipliers to stored successors before subtraction.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  rw [← run.multiplier_succ k omega] at hcurrent
  rw [← run.multiplier_succ (k - 1) omega, hpred] at hprevious
  rw [run.gradientError_apply, run.gradientError_apply]
  simp only [map_sub, sub_apply]
  linear_combination (norm := module) hcurrent - hprevious

/-- Helper for Corollary 4.2: explicit fixed-path admissibility and bounds
control the constraint-gradient image of a corrected multiplier increment. -/
lemma normConstraintGradientMultiplierIncrement_le_of_bounds
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (omega : Ω)
    (hadmCurrent : IsAdmissible h (run.point k omega) (run.baseStep k omega))
    (hadmPrevious : IsAdmissible h (run.point (k - 1) omega)
      (run.baseStep (k - 1) omega))
    (hstepCurrent : ‖run.baseStep k omega‖ ≤ params.delta)
    (hstepPrevious : ‖run.baseStep (k - 1) omega‖ ≤ params.delta)
    (hmultiplier : ‖run.multiplier k omega‖ ≤ params.multiplierBound) :
    ‖EqualityConstrained.constraintGradient c (run.point k omega)
        (run.multiplier (k + 1) omega - run.multiplier k omega)‖ ≤
      primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1) omega‖ +
        ‖run.gradientError k omega‖ + ‖run.gradientError (k - 1) omega‖ := by
  -- Use the two supplied transitions directly, without quantifying over other paths.
  have hpred : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hxCurrent :=
    base_mem_region h (run.point k omega) (run.baseStep k omega) hadmCurrent
  have hxPrevious := base_mem_region h (run.point (k - 1) omega)
    (run.baseStep (k - 1) omega) hadmPrevious
  have herrorCurrent := normScaledConstraintGradientError_le_mul_norm h params
    (run.point k omega) (run.baseStep k omega) hadmCurrent hstepCurrent
  have herrorPrevious := normScaledConstraintGradientError_le_mul_norm h params
    (run.point (k - 1) omega) (run.baseStep (k - 1) omega)
      hadmPrevious hstepPrevious
  -- Corrected displacement replaces the exact point-plus-step identity.
  have hpointDisplacement :
      ‖run.point k omega - run.point (k - 1) omega‖ ≤
        displacementFactor h params.delta * ‖run.baseStep (k - 1) omega‖ := by
    have hdisplacement := displacement_le h params.delta (run.point (k - 1) omega)
      (run.baseStep (k - 1) omega) hadmPrevious hstepPrevious
    rw [← run.point_succ (k - 1) omega, hpred] at hdisplacement
    exact hdisplacement
  have hgradientDifference :
      ‖gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)‖ ≤
        h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1) omega‖ := by
    have hlipschitz :
        ‖gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)‖ ≤
          h.gradientLipschitz *
            ‖run.point k omega - run.point (k - 1) omega‖ := by
      calc
        ‖gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)‖ =
            dist (gradient f (run.point (k - 1) omega))
              (gradient f (run.point k omega)) := (dist_eq_norm _ _).symm
        _ ≤ h.gradientLipschitz *
            dist (run.point (k - 1) omega) (run.point k omega) :=
          h.lipschitzOn_gradient.dist_le_mul
            (run.point (k - 1) omega) hxPrevious (run.point k omega) hxCurrent
        _ = h.gradientLipschitz *
            ‖run.point k omega - run.point (k - 1) omega‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)‖ ≤
          h.gradientLipschitz *
            ‖run.point k omega - run.point (k - 1) omega‖ := hlipschitz
      _ ≤ h.gradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep (k - 1) omega‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1) omega‖ := by ring
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega)‖ ≤
        h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1) omega‖ := by
    have hlipschitz :
        ‖EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega)‖ ≤
          h.constraintGradientLipschitz *
            ‖run.point k omega - run.point (k - 1) omega‖ := by
      calc
        ‖EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega)‖ =
            dist (EqualityConstrained.constraintGradient c (run.point (k - 1) omega))
              (EqualityConstrained.constraintGradient c (run.point k omega)) :=
          (dist_eq_norm _ _).symm
        _ ≤ h.constraintGradientLipschitz *
            dist (run.point (k - 1) omega) (run.point k omega) :=
          h.lipschitzOn_constraintGradient.dist_le_mul
            (run.point (k - 1) omega) hxPrevious (run.point k omega) hxCurrent
        _ = h.constraintGradientLipschitz *
            ‖run.point k omega - run.point (k - 1) omega‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega)‖ ≤
          h.constraintGradientLipschitz *
            ‖run.point k omega - run.point (k - 1) omega‖ := hlipschitz
      _ ≤ h.constraintGradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep (k - 1) omega‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep (k - 1) omega‖ := by ring
  have hdisplacementFactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega))
            (run.multiplier k omega)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep (k - 1) omega‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega))
            (run.multiplier k omega)‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega)‖ *
              ‖run.multiplier k omega‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega)).le_opNorm
            (run.multiplier k omega)
      _ ≤ (h.constraintGradientLipschitz * displacementFactor h params.delta *
            ‖run.baseStep (k - 1) omega‖) * params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (NNReal.coe_nonneg _) hdisplacementFactorNonneg)
            (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep (k - 1) omega‖ := by ring
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  -- Pair each base step with its corrected nonlinear-error contribution.
  have hcurrentPair :
      ‖-(params.beta : ℝ) • run.baseStep k omega +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k omega)
            (error c (run.point k omega) (run.baseStep k omega))‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ := by
    calc
      ‖-(params.beta : ℝ) • run.baseStep k omega +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k omega)
            (error c (run.point k omega) (run.baseStep k omega))‖ ≤
          ‖-(params.beta : ℝ) • run.baseStep k omega‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))‖ :=
        norm_add_le _ _
      _ = params.beta * ‖run.baseStep k omega‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hbeta]
      _ ≤ params.beta * ‖run.baseStep k omega‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖run.baseStep k omega‖ := add_le_add_right herrorCurrent _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep k omega‖ := by
        rw [primalConstant_def]
        ring
  have hpreviousPair :
      ‖(params.beta : ℝ) • run.baseStep (k - 1) omega -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) omega)
            (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep (k - 1) omega‖ := by
    calc
      ‖(params.beta : ℝ) • run.baseStep (k - 1) omega -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) omega)
            (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))‖ ≤
          ‖(params.beta : ℝ) • run.baseStep (k - 1) omega‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) omega)
              (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))‖ :=
        norm_sub_le _ _
      _ = params.beta * ‖run.baseStep (k - 1) omega‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) omega)
            (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbeta]
      _ ≤ params.beta * ‖run.baseStep (k - 1) omega‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖run.baseStep (k - 1) omega‖ :=
        add_le_add_right herrorPrevious _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep (k - 1) omega‖ := by
        rw [primalConstant_def]
        ring
  -- First collect the deterministic corrected geometry in one norm comparison.
  have hdeterministicCore :
      ‖((-(params.beta : ℝ) • run.baseStep k omega +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))) +
          ((params.beta : ℝ) • run.baseStep (k - 1) omega -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) omega)
              (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))) +
          (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega))
              (run.multiplier k omega))‖ ≤
        primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1) omega‖ := by
    calc
      ‖((-(params.beta : ℝ) • run.baseStep k omega +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))) +
          ((params.beta : ℝ) • run.baseStep (k - 1) omega -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) omega)
              (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))) +
          (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega))
              (run.multiplier k omega))‖ ≤
          ‖-(params.beta : ℝ) • run.baseStep k omega +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))‖ +
          ‖(params.beta : ℝ) • run.baseStep (k - 1) omega -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) omega)
              (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))‖ +
          ‖gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)‖ +
          ‖(EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega))
              (run.multiplier k omega)‖ := by
        have hfirst := norm_add_le
          (-(params.beta : ℝ) • run.baseStep k omega +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k omega) (error c (run.point k omega) (run.baseStep k omega)))
          ((params.beta : ℝ) • run.baseStep (k - 1) omega -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) omega)
              (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega)))
        have hsecond := norm_add_le
          ((-(params.beta : ℝ) • run.baseStep k omega +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))) +
            ((params.beta : ℝ) • run.baseStep (k - 1) omega -
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                (run.point (k - 1) omega)
                (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))))
          (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega))
        have hthird := norm_add_le
          (((-(params.beta : ℝ) • run.baseStep k omega +
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point k omega) (error c (run.point k omega) (run.baseStep k omega))) +
              ((params.beta : ℝ) • run.baseStep (k - 1) omega -
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point (k - 1) omega)
                  (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega)))) +
            (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)))
          ((EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega))
              (run.multiplier k omega))
        linarith
      _ ≤ primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
          primalConstant h params.delta params.beta params.rho *
            ‖run.baseStep (k - 1) omega‖ +
          h.gradientLipschitz * displacementFactor h params.delta *
            ‖run.baseStep (k - 1) omega‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            displacementFactor h params.delta * ‖run.baseStep (k - 1) omega‖ :=
        add_le_add (add_le_add (add_le_add hcurrentPair hpreviousPair)
          hgradientDifference) hoperatorApplied
      _ = primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1) omega‖ := by
        rw [primalComparisonConstant_def]
        ring
  -- Append the estimator-error difference only after the deterministic core is closed.
  rw [run.constraintGradientMultiplierIncrement k hk_pos omega]
  calc
    ‖((-(params.beta : ℝ) • run.baseStep k omega +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k omega)
            (error c (run.point k omega) (run.baseStep k omega))) +
        ((params.beta : ℝ) • run.baseStep (k - 1) omega -
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point (k - 1) omega)
            (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))) +
        (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)) +
        (EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
          EqualityConstrained.constraintGradient c (run.point k omega))
            (run.multiplier k omega)) +
        (run.gradientError (k - 1) omega - run.gradientError k omega)‖ ≤
        ‖((-(params.beta : ℝ) • run.baseStep k omega +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k omega)
              (error c (run.point k omega) (run.baseStep k omega))) +
          ((params.beta : ℝ) • run.baseStep (k - 1) omega -
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point (k - 1) omega)
              (error c (run.point (k - 1) omega) (run.baseStep (k - 1) omega))) +
          (gradient f (run.point (k - 1) omega) - gradient f (run.point k omega)) +
          (EqualityConstrained.constraintGradient c (run.point (k - 1) omega) -
            EqualityConstrained.constraintGradient c (run.point k omega))
              (run.multiplier k omega))‖ +
        ‖run.gradientError (k - 1) omega - run.gradientError k omega‖ := norm_add_le _ _
    _ ≤ (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1) omega‖) +
        (‖run.gradientError (k - 1) omega‖ + ‖run.gradientError k omega‖) :=
      add_le_add hdeterministicCore (norm_sub_le _ _)
    _ = primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1) omega‖ +
        ‖run.gradientError k omega‖ + ‖run.gradientError (k - 1) omega‖ := by ring

/-- Helper for Corollary 4.2: global prefix admissibility specializes the
fixed-path constraint-gradient multiplier estimate. -/
lemma normConstraintGradientMultiplierIncrement_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (omega : Ω) :
    ‖EqualityConstrained.constraintGradient c (run.point k omega)
        (run.multiplier (k + 1) omega - run.multiplier k omega)‖ ≤
      primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1) omega‖ +
        ‖run.gradientError k omega‖ + ‖run.gradientError (k - 1) omega‖ := by
  -- Project the two adjacent transitions and their norm bounds at this sample path.
  have hkPrevious : k - 1 < N := by omega
  have hkLeN : k ≤ N := by omega
  have hadmissible := (run.isAdmissiblePrefix_iff N).1 h_admissible
  have hbounds := run.admissiblePrefix_normBounds N h_admissible
  exact run.normConstraintGradientMultiplierIncrement_le_of_bounds k hk_pos omega
    (hadmissible k hk omega) (hadmissible (k - 1) hkPrevious omega)
    (hbounds.1 k hk omega) (hbounds.1 (k - 1) hkPrevious omega)
    (hbounds.2 k hkLeN omega)

/-- Helper for Corollary 4.2: the square of four weighted scalar terms is
controlled by the larger weight square and the two unweighted error squares. -/
private lemma weightedFourTerm_sq_le
    (A B x y e₀ e₁ : ℝ) :
    (A * x + B * y + e₀ + e₁) ^ 2 ≤
      4 * (max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) + (e₀ ^ 2 + e₁ ^ 2)) := by
  -- Group the weighted terms and error terms, then apply the two-term square bound twice.
  let a := A * x
  let b := B * y
  have hab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have he : (e₀ + e₁) ^ 2 ≤ 2 * (e₀ ^ 2 + e₁ ^ 2) := by
    nlinarith [sq_nonneg (e₀ - e₁)]
  have hfour :
      (a + b + e₀ + e₁) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by
    calc
      (a + b + e₀ + e₁) ^ 2 = ((a + b) + (e₀ + e₁)) ^ 2 := by ring
      _ ≤ 2 * ((a + b) ^ 2 + (e₀ + e₁) ^ 2) := by
        nlinarith [sq_nonneg ((a + b) - (e₀ + e₁))]
      _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * (e₀ ^ 2 + e₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hab he) (by norm_num)
      _ = 4 * (a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2) := by ring
  -- Dominate each weighted square by the shared maximum coefficient.
  have ha : a ^ 2 ≤ max (A ^ 2) (B ^ 2) * x ^ 2 := by
    dsimp only [a]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hb : b ^ 2 ≤ max (A ^ 2) (B ^ 2) * y ^ 2 := by
    dsimp only [b]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hsquares :
      a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2 ≤
        max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) + (e₀ ^ 2 + e₁ ^ 2) := by
    calc
      a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2 ≤
          (max (A ^ 2) (B ^ 2) * x ^ 2 +
            max (A ^ 2) (B ^ 2) * y ^ 2) + e₀ ^ 2 + e₁ ^ 2 :=
        add_le_add (add_le_add (add_le_add ha hb) (le_refl _)) (le_refl _)
      _ = max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) +
          (e₀ ^ 2 + e₁ ^ 2) := by ring
  calc
    (A * x + B * y + e₀ + e₁) ^ 2 = (a + b + e₀ + e₁) ^ 2 := by
      simp only [a, b]
    _ ≤ 4 * (a ^ 2 + b ^ 2 + e₀ ^ 2 + e₁ ^ 2) := hfour
    _ ≤ 4 *
        (max (A ^ 2) (B ^ 2) * (x ^ 2 + y ^ 2) + (e₀ ^ 2 + e₁ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hsquares (by norm_num)

/-- Helper for Corollary 4.2: explicit fixed-path admissibility and norm bounds
control the squared corrected multiplier increment. -/
theorem norm_multiplier_succ_sub_sq_le_of_bounds
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (hk_pos : 1 ≤ k) (omega : Ω)
    (hadmCurrent : IsAdmissible h (run.point k omega) (run.baseStep k omega))
    (hadmPrevious : IsAdmissible h (run.point (k - 1) omega)
      (run.baseStep (k - 1) omega))
    (hstepCurrent : ‖run.baseStep k omega‖ ≤ params.delta)
    (hstepPrevious : ‖run.baseStep (k - 1) omega‖ ≤ params.delta)
    (hmultiplier : ‖run.multiplier k omega‖ ≤ params.multiplierBound) :
    ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k omega‖ ^ 2 +
          ‖run.gradientError (k - 1) omega‖ ^ 2) := by
  -- LICQ transports the constraint-gradient comparison to the multiplier norm.
  have hx := base_mem_region h (run.point k omega) (run.baseStep k omega) hadmCurrent
  have hcomparison := run.normConstraintGradientMultiplierIncrement_le_of_bounds
    k hk_pos omega hadmCurrent hadmPrevious hstepCurrent hstepPrevious hmultiplier
  have hlicq := h.licqLowerBound (run.point k omega) hx
    (run.multiplier (k + 1) omega - run.multiplier k omega)
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
      0 ≤ primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep (k - 1) omega‖ +
        ‖run.gradientError k omega‖ + ‖run.gradientError (k - 1) omega‖ := by
    positivity
  have hleftNonneg :
      0 ≤ (h.licqModulus : ℝ) *
        ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ := by positivity
  have hscaledSquare :
      ((h.licqModulus : ℝ) *
          ‖run.multiplier (k + 1) omega - run.multiplier k omega‖) ^ 2 ≤
        (primalConstant h params.delta params.beta params.rho * ‖run.baseStep k omega‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1) omega‖ +
          ‖run.gradientError k omega‖ + ‖run.gradientError (k - 1) omega‖) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hscaled
  -- Apply the checked four-term square estimate in the named coefficient spelling.
  have hfour := weightedFourTerm_sq_le
    (primalConstant h params.delta params.beta params.rho)
    (primalComparisonConstant h params.delta params.beta params.rho
      params.multiplierBound)
    ‖run.baseStep k omega‖ ‖run.baseStep (k - 1) omega‖
    ‖run.gradientError k omega‖ ‖run.gradientError (k - 1) omega‖
  have hscaledExpanded :
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 ≤
        4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2)) := by
    calc
      (h.licqModulus : ℝ) ^ 2 *
          ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 =
          ((h.licqModulus : ℝ) *
            ‖run.multiplier (k + 1) omega - run.multiplier k omega‖) ^ 2 := by ring
      _ ≤ (primalConstant h params.delta params.beta params.rho *
            ‖run.baseStep k omega‖ +
          primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep (k - 1) omega‖ +
          ‖run.gradientError k omega‖ + ‖run.gradientError (k - 1) omega‖) ^ 2 :=
        hscaledSquare
      _ ≤ 4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2)) := hfour
  -- Divide only after the scalar comparison is fully normalized.
  have hsigmaSq : 0 < (h.licqModulus : ℝ) ^ 2 := sq_pos_of_pos h.licqModulus_pos
  have hscaledCommuted :
      ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 *
          (h.licqModulus : ℝ) ^ 2 ≤
        4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2)) := by
    simpa only [mul_comm] using hscaledExpanded
  calc
    ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 ≤
        (4 *
          (max (primalConstant h params.delta params.beta params.rho ^ 2)
              (primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2) *
            (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2))) /
          (h.licqModulus : ℝ) ^ 2 :=
      (le_div_iff₀ hsigmaSq).2 hscaledCommuted
    _ = multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k omega‖ ^ 2 +
          ‖run.gradientError (k - 1) omega‖ ^ 2) := by
      rw [multiplierPrimalConstant_def, LALM.multiplierErrorConstant_def]
      ring

/-- Helper for Corollary 4.2: global prefix admissibility specializes the
fixed-path squared multiplier-increment estimate. -/
theorem norm_multiplier_succ_sub_sq_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (omega : Ω) :
    ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k omega‖ ^ 2 +
          ‖run.gradientError (k - 1) omega‖ ^ 2) := by
  -- Project the two adjacent transitions and their norm bounds at this sample path.
  have hkPrevious : k - 1 < N := by omega
  have hkLeN : k ≤ N := by omega
  have hadmissible := (run.isAdmissiblePrefix_iff N).1 h_admissible
  have hbounds := run.admissiblePrefix_normBounds N h_admissible
  exact run.norm_multiplier_succ_sub_sq_le_of_bounds k hk_pos omega
    (hadmissible k hk omega) (hadmissible (k - 1) hkPrevious omega)
    (hbounds.1 k hk omega) (hbounds.1 (k - 1) hkPrevious omega)
    (hbounds.2 k hkLeN omega)

end LALM.Correction.StochasticRun

end
