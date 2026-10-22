/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.OperationalTrace
public import TR_LALM_theory.Corollary_4_2.RestartSemantics
public import TR_LALM_theory.Corollary_4_2.DeterministicMultiplier
public import TR_LALM_theory.Corollary_4_2.StochasticEnergy
public import TR_LALM_theory.Corollary_4_2.StochasticMultiplier
public import TR_LALM_theory.Corollary_4_2.StoppedEnergy
public import TR_LALM_theory.Corollary_4_2.ScheduleCertificate
public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorStoppedEnergy
public import TR_LALM_theory.Corollary_4_2.StochasticEstimatorRecursion
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedEnergy
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedPath
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedCanonicalPath
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedSemantics
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedSchedule
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedLocalization
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedCertificate
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedLyapunovStep
public import TR_LALM_theory.Theorem_2_13.KurdykaLojasiewicz

public section

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal InnerProductSpace LALM NNReal

namespace LALM.Correction

open LALM.StochasticRun.UniformOutput

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/- Corollary 4.2 (1): the corrected initial-potential bound uses the corrected
displacement and multiplier--primal constants. -/

/- Corollary 4.2 (2): the corrected deterministic objective threshold is
`Φ̄₁ᶜᵒʳ + Λ² / (2 * ρ)`. -/

/- Corollary 4.2 (3): the deterministic localization condition uses the
corrected buffer `χᶜᵒʳ * Δ`. -/

/-- Helper for Corollary 4.2: a natural ceiling of a fixed multiple of `ε⁻²`,
with two units of overhead, is `O(ε⁻²)` as `ε → 0⁺`. -/
private lemma natCeilQuadraticBudget_isBigO (C : ℝ) :
    (fun ε : ℝ≥0 ↦ ((Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) + 2 : ℕ) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Near zero from the right, `ε⁻²` absorbs both the ceiling error and overhead.
  refine Asymptotics.IsBigO.of_bound (|C| + 3) ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hinverse : 1 ≤ (ε : ℝ)⁻¹ := (one_le_inv₀ hεreal).2 hεrealOne
  have hinverseSq : 1 ≤ (ε : ℝ)⁻¹ ^ 2 := by nlinarith
  have hinverseSqNonneg : 0 ≤ (ε : ℝ)⁻¹ ^ 2 := sq_nonneg _
  -- The natural ceiling truncates negative coefficients, so split on the sign of `C`.
  by_cases hC : 0 ≤ C
  · have hargument : 0 ≤ C * (ε : ℝ)⁻¹ ^ 2 :=
      mul_nonneg hC hinverseSqNonneg
    have hceiling := Nat.ceil_lt_add_one hargument
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_add,
      Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg,
      abs_of_nonneg hC]
    have hcoefficient : 0 ≤ C + 3 := by positivity
    nlinarith [mul_nonneg hcoefficient (sub_nonneg.mpr hinverseSq)]
  · have hargument : C * (ε : ℝ)⁻¹ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hinverseSqNonneg
    have hceiling : Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) = 0 :=
      Nat.ceil_eq_zero.mpr hargument
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    rw [hceiling, Nat.zero_add, Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg htwo, Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg]
    have hcoefficient : 0 ≤ |C| + 3 := by positivity
    calc
      (2 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      _ = (|C| + 3) * 1 := (mul_one _).symm
      _ ≤ (|C| + 3) * (ε : ℝ)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hinverseSq hcoefficient

namespace Run

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
  rw [nextPoint_def, add_sub_cancel_left] at hcorrection
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
        add_le_add (le_refl _) hcorrectionSqScaled
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
  -- Put the corrected endpoint and both intermediate objectives in one spelling.
  have hpointSucc :
      run.point (k + 1) =
        trialPoint (run.point k) (run.baseStep k) +
          step c (run.point k) (run.baseStep k) := by
    rw [run.point_succ, nextPoint_def]
  rw [hpointSucc, trialPoint_def]
  rw [trialPoint_def] at hcorrection hinnerCorrection
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

/-- Helper for Corollary 4.2: along an admissible corrected transition, the
objective change is controlled by the total corrected path length. -/
private lemma normObjectiveChangeAlongCorrectedStep_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hadm : IsAdmissible h (run.point k) (run.baseStep k))
    (hstep : ‖run.baseStep k‖ ≤ params.delta) :
    ‖f (run.point (k + 1)) - f (run.point k)‖ ≤
      h.gradientBound * displacementFactor h params.delta * ‖run.baseStep k‖ := by
  -- Apply the segmentwise mean-value estimate to the base and correction legs.
  have hbaseObjective :
      ‖f (trialPoint (run.point k) (run.baseStep k)) - f (run.point k)‖ ≤
        h.gradientBound * ‖run.baseStep k‖ := by
    have hmean :
        ‖f (trialPoint (run.point k) (run.baseStep k)) - f (run.point k)‖ ≤
          h.gradientBound *
            ‖trialPoint (run.point k) (run.baseStep k) - run.point k‖ := by
      apply (convex_segment (run.point k)
        (trialPoint (run.point k) (run.baseStep k))).norm_image_sub_le_of_norm_fderiv_le
        (𝕜 := ℝ)
      · intro u hu
        exact h.differentiableAt_objective (hadm.1 hu)
      · intro u hu
        simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
          h.norm_gradient_le u (hadm.1 hu)
      · exact left_mem_segment ℝ (run.point k)
          (trialPoint (run.point k) (run.baseStep k))
      · exact right_mem_segment ℝ (run.point k)
          (trialPoint (run.point k) (run.baseStep k))
    simpa only [trialPoint_def, add_sub_cancel_left] using hmean
  have hcorrectionObjective :
      ‖f (nextPoint c (run.point k) (run.baseStep k)) -
          f (trialPoint (run.point k) (run.baseStep k))‖ ≤
        h.gradientBound * ‖step c (run.point k) (run.baseStep k)‖ := by
    have hmean :
        ‖f (nextPoint c (run.point k) (run.baseStep k)) -
            f (trialPoint (run.point k) (run.baseStep k))‖ ≤
          h.gradientBound *
            ‖nextPoint c (run.point k) (run.baseStep k) -
              trialPoint (run.point k) (run.baseStep k)‖ := by
      apply (convex_segment (trialPoint (run.point k) (run.baseStep k))
        (nextPoint c (run.point k) (run.baseStep k))).norm_image_sub_le_of_norm_fderiv_le
          (𝕜 := ℝ)
      · intro u hu
        exact h.differentiableAt_objective (hadm.2 hu)
      · intro u hu
        simpa only [← toDual_gradient, LinearIsometryEquiv.norm_map] using
          h.norm_gradient_le u (hadm.2 hu)
      · exact left_mem_segment ℝ (trialPoint (run.point k) (run.baseStep k))
          (nextPoint c (run.point k) (run.baseStep k))
      · exact right_mem_segment ℝ (trialPoint (run.point k) (run.baseStep k))
          (nextPoint c (run.point k) (run.baseStep k))
    simpa only [nextPoint_def, add_sub_cancel_left] using hmean
  -- The quadratic correction becomes linear after the base-step radius is used.
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  have hcorrectionLinear :
      ‖step c (run.point k) (run.baseStep k)‖ ≤
        stepConstant h * params.delta * ‖run.baseStep k‖ := by
    calc
      ‖step c (run.point k) (run.baseStep k)‖ ≤
          stepConstant h * ‖run.baseStep k‖ ^ 2 :=
        norm_step_le h (run.point k) (run.baseStep k) hadm
      _ = (stepConstant h * ‖run.baseStep k‖) * ‖run.baseStep k‖ := by ring
      _ ≤ (stepConstant h * params.delta) * ‖run.baseStep k‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep hstepConstantNonneg) (norm_nonneg _)
  have hdecomposition :
      f (nextPoint c (run.point k) (run.baseStep k)) - f (run.point k) =
        (f (nextPoint c (run.point k) (run.baseStep k)) -
          f (trialPoint (run.point k) (run.baseStep k))) +
        (f (trialPoint (run.point k) (run.baseStep k)) - f (run.point k)) := by
    ring
  rw [run.point_succ, hdecomposition]
  calc
    ‖(f (nextPoint c (run.point k) (run.baseStep k)) -
          f (trialPoint (run.point k) (run.baseStep k))) +
        (f (trialPoint (run.point k) (run.baseStep k)) - f (run.point k))‖ ≤
        ‖f (nextPoint c (run.point k) (run.baseStep k)) -
          f (trialPoint (run.point k) (run.baseStep k))‖ +
        ‖f (trialPoint (run.point k) (run.baseStep k)) - f (run.point k)‖ :=
      norm_add_le _ _
    _ ≤ h.gradientBound * ‖step c (run.point k) (run.baseStep k)‖ +
        h.gradientBound * ‖run.baseStep k‖ :=
      add_le_add hcorrectionObjective hbaseObjective
    _ ≤ h.gradientBound *
          (stepConstant h * params.delta * ‖run.baseStep k‖) +
        h.gradientBound * ‖run.baseStep k‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcorrectionLinear (NNReal.coe_nonneg _))
        (le_refl _)
    _ = h.gradientBound * displacementFactor h params.delta * ‖run.baseStep k‖ := by
      rw [displacementFactor_def]
      ring

/-- Helper for Corollary 4.2: containment of the base-to-trial segment suffices
for the quadratic base-linearization residual estimate. -/
private lemma normResidual_le_of_baseSegment
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hbase : segment ℝ x (trialPoint x p) ⊆ h.region) :
    ‖residual c x p‖ ≤ LALM.linearizationConstant h * ‖p‖ ^ 2 := by
  -- Taylor's theorem is used only on the base segment appearing in the hypothesis.
  have hremainder := LALM.norm_sub_sub_fderiv_le c
    h.constraintGradientLipschitz h.region x (trialPoint x p)
    (fun _ hz ↦ h.differentiableAt_constraint hz)
    h.lipschitzOn_constraintFDeriv hbase
  simpa only [residual_def, trialPoint_def, add_sub_cancel_left,
    LALM.linearizationConstant_def, NNReal.coe_div, NNReal.coe_ofNat] using hremainder

/-- Helper for Corollary 4.2: containment of the base-to-trial segment also
suffices for the quadratic correction-norm estimate. -/
private lemma normCorrection_le_of_baseSegment
    (h : EqualityConstrained.Regularity f c)
    (x p : EuclideanSpace ℝ (Fin n))
    (hbase : segment ℝ x (trialPoint x p) ⊆ h.region) :
    ‖step c x p‖ ≤ stepConstant h * ‖p‖ ^ 2 := by
  -- Use trial-point LICQ to convert the residual bound into a correction bound.
  let v := gramInverse c (trialPoint x p) (residual c x p)
  have hz : trialPoint x p ∈ h.region :=
    hbase (right_mem_segment ℝ x (trialPoint x p))
  have hvLower :
      (h.licqModulus : ℝ) * ‖v‖ ≤
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ :=
    h.licqLowerBound (trialPoint x p) hz v
  have hgram := comp_gramInverse h (trialPoint x p) hz (residual c x p)
  have hnormSq :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
        ⟪v, residual c x p⟫_ℝ := by
    calc
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
          ⟪ContinuousLinearMap.adjoint
              (EqualityConstrained.constraintGradient c (trialPoint x p))
                (EqualityConstrained.constraintGradient c (trialPoint x p) v), v⟫_ℝ := by
        simpa only [ContinuousLinearMap.comp_apply, RCLike.re_to_real] using
          ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left
            (EqualityConstrained.constraintGradient c (trialPoint x p)) v
      _ = ⟪gram c (trialPoint x p) v, v⟫_ℝ := by
        rw [gram_def]
        rfl
      _ = ⟪residual c x p, v⟫_ℝ := by rw [hgram]
      _ = ⟪v, residual c x p⟫_ℝ := real_inner_comm _ _
  have hscaledInner :
      (h.licqModulus : ℝ) *
          ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 ≤
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ *
          ‖residual c x p‖ := by
    calc
      (h.licqModulus : ℝ) *
          ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ^ 2 =
          (h.licqModulus : ℝ) * ⟪v, residual c x p⟫_ℝ := by rw [hnormSq]
      _ ≤ (h.licqModulus : ℝ) * (‖v‖ * ‖residual c x p‖) := by
        gcongr
        exact real_inner_le_norm v (residual c x p)
      _ = ((h.licqModulus : ℝ) * ‖v‖) * ‖residual c x p‖ := by ring
      _ ≤ ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ *
          ‖residual c x p‖ :=
        mul_le_mul_of_nonneg_right hvLower (norm_nonneg _)
  have hgradientBound :
      ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ≤
        ‖residual c x p‖ / (h.licqModulus : ℝ) := by
    by_cases hzero :
        ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ = 0
    · rw [hzero]
      positivity
    · have hpositive :
          0 < ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      apply (le_div_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)).mpr
      nlinarith
  have hresidual := normResidual_le_of_baseSegment h x p hbase
  rw [step_def]
  simp only [norm_neg]
  calc
    ‖EqualityConstrained.constraintGradient c (trialPoint x p) v‖ ≤
        ‖residual c x p‖ / (h.licqModulus : ℝ) := hgradientBound
    _ ≤ (LALM.linearizationConstant h * ‖p‖ ^ 2) /
        (h.licqModulus : ℝ) := by
      gcongr
    _ = stepConstant h * ‖p‖ ^ 2 := by
      rw [stepConstant_def, LALM.linearizationConstant_def]
      norm_num [NNReal.coe_div]
      ring


/-- Helper for Corollary 4.2: region membership and prior multiplier bounds
force the next corrected base step to stay within `params.delta`. -/
private lemma normBaseStep_le_of_mem_region_of_multiplier_bounds
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hx : run.point k ∈ h.region)
    (hMultiplier : ∀ j ≤ k, ‖run.multiplier j‖ ≤ params.multiplierBound) :
    ‖run.baseStep k‖ ≤ params.delta := by
  -- Route correction: use the canonical damped estimate from `DeterministicPrefix`
  -- instead of retaining a target-local duplicate of that owner API.
  have heffective := run.norm_effectiveMultiplier_le h params k hMultiplier
  have hestimate := normDampedNormalEquation_le
    (fderiv ℝ c (run.point k)) run.beta_pos run.rho_pos.le h.licqModulus_pos
    (h.licqLowerBound (run.point k) hx) (run.baseStep k) (gradient f (run.point k))
    (run.multiplier k + params.rho • c (run.point k)) (run.baseStepOptimality k)
  have hgradient := h.norm_gradient_le (run.point k) hx
  have hoperator :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ ≤
        h.constraintGradientBound := by
    simpa only [EqualityConstrained.constraintGradient_def] using
      h.norm_constraintGradient_le (run.point k) hx
  have hdenom :
      0 < (params.beta : ℝ) + params.rho * (h.licqModulus : ℝ) ^ 2 := by
    exact add_pos_of_pos_of_nonneg run.beta_pos
      (mul_nonneg run.rho_pos.le (sq_nonneg (h.licqModulus : ℝ)))
  have hgradientTerm :
      ‖gradient f (run.point k)‖ / params.beta ≤ h.gradientBound / params.beta :=
    (div_le_div_iff_of_pos_right run.beta_pos).2 hgradient
  have hproduct :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ *
          ‖run.multiplier k + params.rho • c (run.point k)‖ ≤
        h.constraintGradientBound * (3 * params.multiplierBound) :=
    mul_le_mul hoperator heffective (norm_nonneg _)
      (NNReal.coe_nonneg h.constraintGradientBound)
  have hconstraintTerm :
      ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ *
          ‖run.multiplier k + params.rho • c (run.point k)‖ /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) ≤
        3 * h.constraintGradientBound * params.multiplierBound /
            (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := by
    rw [div_le_div_iff_of_pos_right hdenom]
    nlinarith
  calc
    ‖run.baseStep k‖ ≤
        ‖gradient f (run.point k)‖ / params.beta +
          ‖ContinuousLinearMap.adjoint (fderiv ℝ c (run.point k))‖ *
            ‖run.multiplier k + params.rho • c (run.point k)‖ /
              (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) := hestimate
    _ ≤ h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * (h.licqModulus : ℝ) ^ 2) :=
      add_le_add hgradientTerm hconstraintTerm
    _ ≤ params.delta := params.comparisonBound_le

/-- Helper for Corollary 4.2: every positive corrected Lyapunov value in an
admissible finite prefix is bounded by the corrected initial potential. -/
private lemma lyapunov_le_initialPotentialBound_of_prefix
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (hPrefix : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ N) :
    run.lyapunov h params k ≤ initialPotentialBound h params := by
  have hOneLeN : 1 ≤ N := hk_pos.trans hk_le
  have hadm := (run.isAdmissiblePrefix_iff h N).1 hPrefix 0 (by omega)
  have hstep := run.norm_baseStep_le h params hPrefix (k := 0) (by omega)
  have hmultiplierZero := run.norm_multiplier_le h params hPrefix (k := 0) (by omega)
  have hmultiplierOne := run.norm_multiplier_le h params hPrefix (k := 1) hOneLeN
  -- The two corrected segments initialize the objective at the `χᶜᵒʳ Δ` scale.
  have hobjectiveIncrement :=
    normObjectiveChangeAlongCorrectedStep_le h params run 0 hadm hstep
  have hsignedObjective :
      f (run.point 1) - f (run.point 0) ≤
        ‖f (run.point 1) - f (run.point 0)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (run.point 1) - f (run.point 0))
  have hfactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hgradientFactorNonneg :
      0 ≤ (h.gradientBound : ℝ) * displacementFactor h params.delta :=
    mul_nonneg (NNReal.coe_nonneg _) hfactorNonneg
  have hgradientStep :
      h.gradientBound * displacementFactor h params.delta * ‖run.baseStep 0‖ ≤
        h.gradientBound * displacementFactor h params.delta * params.delta :=
    mul_le_mul_of_nonneg_left hstep hgradientFactorNonneg
  have hobjective :
      f (run.point 1) ≤
        f x₀ + h.gradientBound * displacementFactor h params.delta * params.delta := by
    rw [run.point_zero] at hobjectiveIncrement hsignedObjective
    linarith
  -- The multiplier update bounds the first scaled constraint residual by `2 Λ`.
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point 1) =
        run.multiplier 1 - run.multiplier 0 := by
    rw [run.multiplier_succ_eq_add 0]
    module
  have hscaledResidual :
      params.rho * ‖c (run.point 1)‖ ≤ 2 * params.multiplierBound := by
    calc
      params.rho * ‖c (run.point 1)‖ =
          ‖(params.rho : ℝ) • c (run.point 1)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
      _ = ‖run.multiplier 1 - run.multiplier 0‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier 1‖ + ‖run.multiplier 0‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinnerBound :
      ⟪run.multiplier 1, c (run.point 1)⟫_ℝ ≤
        params.multiplierBound * ‖c (run.point 1)‖ := by
    calc
      ⟪run.multiplier 1, c (run.point 1)⟫_ℝ ≤
          ‖run.multiplier 1‖ * ‖c (run.point 1)‖ := real_inner_le_norm _ _
      _ ≤ params.multiplierBound * ‖c (run.point 1)‖ :=
        mul_le_mul_of_nonneg_right hmultiplierOne (norm_nonneg _)
  have hinnerScaled :
      params.rho * ⟪run.multiplier 1, c (run.point 1)⟫_ℝ ≤
        2 * params.multiplierBound ^ 2 := by
    have hinnerRho := mul_le_mul_of_nonneg_left hinnerBound run.rho_pos.le
    have hresidualBound := mul_le_mul_of_nonneg_left hscaledResidual hboundNonneg
    nlinarith
  have hscaledResidualSq :
      (params.rho * ‖c (run.point 1)‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg run.rho_pos.le (norm_nonneg _))
      (mul_nonneg (by norm_num) hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪run.multiplier 1, c (run.point 1)⟫_ℝ +
          params.rho / 2 * ‖c (run.point 1)‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ run.rho_pos).2
    nlinarith
  -- The nonnegative Lyapunov correction is bounded at the base-step radius.
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖run.baseStep 0‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep 0‖ ^ 2 ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq
      (div_nonneg hconstantNonneg run.rho_pos.le)
  have hbase :
      run.lyapunov h params 1 ≤ initialPotentialBound h params := by
    rw [run.lyapunov_def, augmentedLagrangian_def, initialPotentialBound_def]
    norm_num only [Nat.reduceSub]
    linarith
  -- Lyapunov descent propagates the initialized bound across the prefix.
  revert hk_le
  induction k, hk_pos using Nat.le_induction with
  | base =>
      intro hk_le
      exact hbase
  | succ k hk_pos hprevious =>
      intro hkNextLe
      have hklt : k < N := by omega
      have hdescent := run.lyapunovDescent h params hPrefix hk_pos hklt
      have hdropNonneg :
          0 ≤ (params.beta / 4) * ‖run.baseStep k‖ ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      have hpreviousBound := hprevious (by omega)
      linarith

/-- Helper for Corollary 4.2: every point of an admissible corrected prefix
obeys the corrected deterministic objective threshold. -/
private lemma objective_le_deterministicBound_of_prefix
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (hPrefix : run.IsAdmissiblePrefix h N) (hk : k ≤ N) :
    f (run.point k) ≤ deterministicObjectiveBound h params := by
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  by_cases hkzero : k = 0
  · -- At index zero every correction in the deterministic bound is nonnegative.
    subst k
    rw [run.point_zero, deterministicObjectiveBound_def, initialPotentialBound_def]
    have hgradientTerm :
        0 ≤ (h.gradientBound : ℝ) * displacementFactor h params.delta *
          params.delta := by
      rw [displacementFactor_def, stepConstant_def]
      positivity
    have hresidualTerm :
        0 ≤ 4 * (params.multiplierBound : ℝ) ^ 2 / params.rho := by positivity
    have hcorrectionTerm :
        0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * (params.delta : ℝ) ^ 2 :=
      mul_nonneg (div_nonneg hconstantNonneg run.rho_pos.le) (sq_nonneg _)
    have hmultiplierTerm :
        0 ≤ (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) := by positivity
    linarith
  · -- At positive indices, complete the multiplier square in the Lyapunov bound.
    have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hkzero
    have hphi :=
      lyapunov_le_initialPotentialBound_of_prefix h params run hPrefix hk_pos hk
    have hmultiplier := run.norm_multiplier_le h params hPrefix hk
    have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
    have hinner :
        -(‖run.multiplier k‖ * ‖c (run.point k)‖) ≤
          ⟪run.multiplier k, c (run.point k)⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hyoung :
        2 * ‖c (run.point k)‖ * ‖run.multiplier k‖ ≤
          params.rho * ‖c (run.point k)‖ ^ 2 +
            (params.rho : ℝ)⁻¹ * ‖run.multiplier k‖ ^ 2 :=
      two_mul_le_add_mul_sq run.rho_pos
    have hyoungDivided :=
      div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
    have hyoungHalf :
        ‖run.multiplier k‖ * ‖c (run.point k)‖ ≤
          params.rho / 2 * ‖c (run.point k)‖ ^ 2 +
            ‖run.multiplier k‖ ^ 2 / (2 * params.rho) := by
      calc
        ‖run.multiplier k‖ * ‖c (run.point k)‖ =
            (2 * ‖c (run.point k)‖ * ‖run.multiplier k‖) / 2 := by ring
        _ ≤ (params.rho * ‖c (run.point k)‖ ^ 2 +
              (params.rho : ℝ)⁻¹ * ‖run.multiplier k‖ ^ 2) / 2 :=
          hyoungDivided
        _ = params.rho / 2 * ‖c (run.point k)‖ ^ 2 +
              ‖run.multiplier k‖ ^ 2 / (2 * params.rho) := by
          field_simp [run.rho_pos.ne']
    have hmultiplierSq :
        ‖run.multiplier k‖ ^ 2 ≤ (params.multiplierBound : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hboundNonneg).2 hmultiplier
    have hdiv :
        ‖run.multiplier k‖ ^ 2 / (2 * (params.rho : ℝ)) ≤
          (params.multiplierBound : ℝ) ^ 2 / (2 * (params.rho : ℝ)) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) run.rho_pos)).2
        hmultiplierSq
    have hcorrectionNonneg :
        0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) * ‖run.baseStep (k - 1)‖ ^ 2 :=
      mul_nonneg (div_nonneg hconstantNonneg run.rho_pos.le) (sq_nonneg _)
    rw [run.lyapunov_def, augmentedLagrangian_def] at hphi
    rw [deterministicObjectiveBound_def]
    linarith

/-- Helper for Corollary 4.2: every point in an admissible corrected prefix
satisfies the feasibility bound used by the deterministic localization set. -/
private lemma constraintNorm_le_localizationBound_of_prefix
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (hPrefix : run.IsAdmissiblePrefix h N) (hk : k ≤ N) :
    ‖c (run.point k)‖ ≤ 2 * params.multiplierBound / params.rho := by
  by_cases hkzero : k = 0
  · subst k
    rw [run.point_zero]
    apply (le_div_iff₀ run.rho_pos).2
    have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
    linarith [params.initialResidual_le]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
    have hj : j ≤ N := by omega
    have hprevious := run.norm_multiplier_le h params hPrefix hj
    have hcurrent := run.norm_multiplier_le h params hPrefix hk
    have hresidualIdentity :
        (params.rho : ℝ) • c (run.point (j + 1)) =
          run.multiplier (j + 1) - run.multiplier j := by
      rw [run.multiplier_succ_eq_add j]
      module
    apply (le_div_iff₀ run.rho_pos).2
    calc
      ‖c (run.point (j + 1))‖ * params.rho =
          params.rho * ‖c (run.point (j + 1))‖ := by ring
      _ = ‖(params.rho : ℝ) • c (run.point (j + 1))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
      _ = ‖run.multiplier (j + 1) - run.multiplier j‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier (j + 1)‖ + ‖run.multiplier j‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith

/-- Helper for Corollary 4.2: a corrected-sublevel point with a bounded base
step has both outgoing corrected segments in the regularity region. -/
private lemma correctedSegments_subset_region_of_point_mem_sublevel
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (x p : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ deterministicSublevel h params) (hp : ‖p‖ ≤ params.delta) :
    IsAdmissible h x p := by
  have hregionContainment :=
    (deterministicRegionCondition_iff h params).1 h_region
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  have hdeltaNonneg : (0 : ℝ) ≤ params.delta := NNReal.coe_nonneg _
  have hbaseDistance :
      dist x (trialPoint x p) ≤ localizationRadius h params := by
    calc
      dist x (trialPoint x p) = dist (trialPoint x p) x := dist_comm _ _
      _ = ‖p‖ := by
        rw [dist_eq_norm, trialPoint_def, add_sub_cancel_left]
      _ ≤ params.delta := hp
      _ ≤ localizationRadius h params := by
        rw [localizationRadius_def, displacementFactor_def]
        nlinarith [mul_nonneg hstepConstantNonneg (sq_nonneg (params.delta : ℝ))]
  -- The base segment lies in the corrected thickening around its left endpoint.
  have hbaseSegment : segment ℝ x (trialPoint x p) ⊆ h.region := by
    intro y hy
    apply hregionContainment
    apply Metric.mem_cthickening_of_dist_le y x (localizationRadius h params)
      (deterministicSublevel h params) hx
    exact (Metric.mem_closedBall.mp
      (segment_subset_closedBall_left x (trialPoint x p) hy)).trans hbaseDistance
  have hcorrection := normCorrection_le_of_baseSegment h x p hbaseSegment
  have hpSq : ‖p‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdeltaNonneg).2 hp
  have htotalDistance :
      dist (trialPoint x p) (nextPoint c x p) + dist (trialPoint x p) x ≤
        localizationRadius h params := by
    calc
      dist (trialPoint x p) (nextPoint c x p) + dist (trialPoint x p) x =
          ‖step c x p‖ + ‖p‖ := by
        rw [dist_comm (trialPoint x p) (nextPoint c x p), dist_eq_norm,
          nextPoint_def, add_sub_cancel_left, dist_eq_norm, trialPoint_def,
          add_sub_cancel_left]
      _ ≤ stepConstant h * ‖p‖ ^ 2 + ‖p‖ :=
        add_le_add hcorrection (le_refl _)
      _ ≤ stepConstant h * params.delta ^ 2 + params.delta := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpSq hstepConstantNonneg) hp
      _ = localizationRadius h params := by
        rw [localizationRadius_def, displacementFactor_def]
        ring
  -- Triangle inequality transfers the correction-segment ball back to the base point.
  have hcorrectionSegment :
      segment ℝ (trialPoint x p) (nextPoint c x p) ⊆ h.region := by
    intro y hy
    apply hregionContainment
    apply Metric.mem_cthickening_of_dist_le y x (localizationRadius h params)
      (deterministicSublevel h params) hx
    have hyTrial :
        dist y (trialPoint x p) ≤
          dist (trialPoint x p) (nextPoint c x p) :=
      Metric.mem_closedBall.mp
        (segment_subset_closedBall_left (trialPoint x p) (nextPoint c x p) hy)
    calc
      dist y x ≤ dist y (trialPoint x p) + dist (trialPoint x p) x :=
        dist_triangle _ _ _
      _ ≤ dist (trialPoint x p) (nextPoint c x p) +
          dist (trialPoint x p) x := add_le_add hyTrial (le_refl _)
      _ ≤ localizationRadius h params := htotalDistance
  exact ⟨hbaseSegment, hcorrectionSegment⟩

/-- Helper for Corollary 4.2: the corrected deterministic region condition
makes every finite corrected prefix admissible. -/
theorem allPrefixesAdmissible
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (N : ℕ) : run.IsAdmissiblePrefix h N := by
  -- Extend one prefix using its objective and multiplier invariants.
  induction N with
  | zero =>
      exact (run.isAdmissiblePrefix_iff h 0).2 fun k hk ↦ by omega
  | succ N hPrefix =>
      apply (run.isAdmissiblePrefix_iff h (N + 1)).2
      intro k hk
      by_cases hkOld : k < N
      · exact (run.isAdmissiblePrefix_iff h N).1 hPrefix k hkOld
      · have hkeq : k = N := by omega
        subst k
        have hobjective :=
          objective_le_deterministicBound_of_prefix h params run hPrefix
            (Nat.le_refl N)
        have hconstraint :=
          constraintNorm_le_localizationBound_of_prefix h params run hPrefix
            (Nat.le_refl N)
        have hsublevel : run.point N ∈ deterministicSublevel h params :=
          (mem_deterministicSublevel h params (run.point N)).2
            ⟨hobjective, hconstraint⟩
        have hxRegion : run.point N ∈ h.region := by
          apply (deterministicRegionCondition_iff h params).1 h_region
          exact Metric.self_subset_cthickening
            (deterministicSublevel h params) hsublevel
        have hMultiplier :
            ∀ j ≤ N, ‖run.multiplier j‖ ≤ params.multiplierBound :=
          fun j hj ↦ run.norm_multiplier_le h params hPrefix hj
        have hstep :=
          normBaseStep_le_of_mem_region_of_multiplier_bounds h params run N
            hxRegion hMultiplier
        exact correctedSegments_subset_region_of_point_mem_sublevel
          h params h_region (run.point N) (run.baseStep N) hsublevel hstep

/-- Helper for Corollary 4.2: the concrete corrected deterministic budget is at
least two and dominates its inverse-square residual threshold. -/
private lemma deterministicIterationBudget_spec
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (ε : ℝ≥0) :
    2 ≤ deterministicIterationBudget h params run ε ∧
      deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2 ≤
        (deterministicIterationBudget h params run ε : ℝ) - 1 := by
  -- The two-unit overhead gives the lower bound, while the ceiling gives the threshold.
  constructor
  · rw [deterministicIterationBudget_def]
    omega
  · rw [deterministicIterationBudget_def]
    have hceiling := Nat.le_ceil
      (deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2)
    norm_num at hceiling ⊢
    linarith

/-- Helper for Corollary 4.2: adjoining preceding terms of a nonnegative
sequence costs at most its initial term and one additional sampled sum. -/
private lemma sumAdjacent_le (a : ℕ → ℝ) (K : ℕ) (hK : 2 ≤ K)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1))) ≤
      a 0 + 2 * ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
  -- Normalize the closed interval to the half-open interval used by range sums.
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
  have hrange :
      (∑ k ∈ Finset.range (K - 1), a k) ≤ ∑ k ∈ Finset.range K, a k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun k _ _ ↦ ha k)
  have hrangeSplit :
      (∑ k ∈ Finset.range K, a k) =
        a 0 + ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
    rw [hinterval, Finset.sum_range_eq_add_Ico a (by omega)]
  -- Split the adjacent sum and use nonnegativity to enlarge the shifted range.
  rw [Finset.sum_add_distrib, hshift]
  linarith

/-- Helper for Corollary 4.2: a bounded admissible corrected base step controls
the penalty-scaled constraint-gradient image of its nonlinear error. -/
private lemma normStationarityError_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hadm : IsAdmissible h (run.point k) (run.baseStep k))
    (hstep : ‖run.baseStep k‖ ≤ params.delta) :
    ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
        (error c (run.point k) (run.baseStep k))‖ ≤
      params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta * ‖run.baseStep k‖ := by
  -- First pass through the operator norm and the corrected quadratic error estimate.
  have hx := base_mem_region h (run.point k) (run.baseStep k) hadm
  have hoperator := h.norm_constraintGradient_le (run.point k) hx
  have herror := norm_error_le_factor h params.delta
    (run.point k) (run.baseStep k) hadm hstep
  have happlication :
      ‖EqualityConstrained.constraintGradient c (run.point k)
          (error c (run.point k) (run.baseStep k))‖ ≤
        h.constraintGradientBound *
          ‖error c (run.point k) (run.baseStep k)‖ :=
    (EqualityConstrained.constraintGradient c (run.point k)).le_opNorm
      (error c (run.point k) (run.baseStep k)) |>.trans
        (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have herrorApplied :
      ‖EqualityConstrained.constraintGradient c (run.point k)
          (error c (run.point k) (run.baseStep k))‖ ≤
        h.constraintGradientBound *
          (errorFactor h params.delta * ‖run.baseStep k‖ ^ 2) :=
    happlication.trans
      (mul_le_mul_of_nonneg_left herror (NNReal.coe_nonneg h.constraintGradientBound))
  have hstepProduct :
      ‖run.baseStep k‖ * ‖run.baseStep k‖ ≤
        params.delta * ‖run.baseStep k‖ :=
    mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
  have hcoefficientNonneg :
      0 ≤ (params.rho : ℝ) * h.constraintGradientBound *
        errorFactor h params.delta := by
    rw [errorFactor_def, errorConstant_def]
    positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
  calc
    params.rho * ‖EqualityConstrained.constraintGradient c (run.point k)
        (error c (run.point k) (run.baseStep k))‖ ≤
        params.rho * (h.constraintGradientBound *
          (errorFactor h params.delta * ‖run.baseStep k‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left herrorApplied run.rho_pos.le
    _ = (params.rho * h.constraintGradientBound * errorFactor h params.delta) *
        (‖run.baseStep k‖ * ‖run.baseStep k‖) := by ring
    _ ≤ (params.rho * h.constraintGradientBound * errorFactor h params.delta) *
        (params.delta * ‖run.baseStep k‖) :=
      mul_le_mul_of_nonneg_left hstepProduct hcoefficientNonneg
    _ = params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta * ‖run.baseStep k‖ := by ring

/-- Helper for Corollary 4.2: corrected perturbed stationarity and displacement
bound stationarity at the next iterate by the corrected primal comparison constant. -/
private lemma normStationarityPointSucc_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N) (hk : k < N) :
    ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ≤
      primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.baseStep k‖ := by
  -- Extract the corrected transition, endpoint regularity, and prefix bounds.
  have hadm := (run.isAdmissiblePrefix_iff h N).1 h_admissible k hk
  have hxCurrent := base_mem_region h (run.point k) (run.baseStep k) hadm
  have hxNext := nextPoint_mem_region h (run.point k) (run.baseStep k) hadm
  rw [← run.point_succ k] at hxNext
  have hstep := run.norm_baseStep_le h params h_admissible hk
  have hmultiplier :=
    run.norm_multiplier_le h params h_admissible (show k + 1 ≤ N by omega)
  have herror := normStationarityError_le h params run k hadm hstep
  -- Rearrange base-model stationarity into the three next-iterate error terms.
  have hperturbed := perturbedMultiplierIdentity f c params.rho params.beta
    (run.point k) (run.multiplier k) (run.baseStep k) (run.minimizes_baseStep k)
  rw [← run.multiplier_succ k] at hperturbed
  have hstationarityIdentity :
      KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1)) =
        (-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))) +
        (gradient f (run.point (k + 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1)) := by
    rw [KKT.stationarity_def]
    simp only [sub_apply]
    linear_combination (norm := module) hperturbed
  -- The corrected displacement factor replaces the exact point-step identity.
  have hpointDisplacement :
      ‖run.point (k + 1) - run.point k‖ ≤
        displacementFactor h params.delta * ‖run.baseStep k‖ := by
    have hdisplacement := displacement_le h params.delta (run.point k)
      (run.baseStep k) hadm hstep
    rw [← run.point_succ k] at hdisplacement
    exact hdisplacement
  have hgradientDifference :
      ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖ ≤
        h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k‖ := by
    calc
      ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖ =
          dist (gradient f (run.point (k + 1))) (gradient f (run.point k)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz * dist (run.point (k + 1)) (run.point k) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k + 1)) hxNext (run.point k) hxCurrent
      _ = h.gradientLipschitz * ‖run.point (k + 1) - run.point k‖ := by
        rw [dist_eq_norm]
      _ ≤ h.gradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep k‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k‖ := by ring
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ ≤
        h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k‖ := by
    calc
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k)‖ =
          dist (EqualityConstrained.constraintGradient c (run.point (k + 1)))
            (EqualityConstrained.constraintGradient c (run.point k)) :=
        (dist_eq_norm _ _).symm
      _ ≤ h.constraintGradientLipschitz *
          dist (run.point (k + 1)) (run.point k) :=
        h.lipschitzOn_constraintGradient.dist_le_mul
          (run.point (k + 1)) hxNext (run.point k) hxCurrent
      _ = h.constraintGradientLipschitz *
          ‖run.point (k + 1) - run.point k‖ := by
        rw [dist_eq_norm]
      _ ≤ h.constraintGradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep k‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k‖ := by ring
  have hdisplacementFactorNonneg :
      0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep k‖ := by
    calc
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ ≤
          ‖EqualityConstrained.constraintGradient c (run.point (k + 1)) -
            EqualityConstrained.constraintGradient c (run.point k)‖ *
              ‖run.multiplier (k + 1)‖ :=
        (EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k)).le_opNorm
            (run.multiplier (k + 1))
      _ ≤ (h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k‖) * params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (NNReal.coe_nonneg _) hdisplacementFactorNonneg)
            (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep k‖ := by ring
  have hproximalError :
      ‖-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep k‖ := by
    calc
      ‖-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ ≤
          ‖-(params.beta : ℝ) • run.baseStep k‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
              (error c (run.point k) (run.baseStep k))‖ := norm_add_le _ _
      _ = params.beta * ‖run.baseStep k‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos run.beta_pos]
      _ ≤ params.beta * ‖run.baseStep k‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖run.baseStep k‖ := add_le_add_right herror _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep k‖ := by
        rw [primalConstant_def]
        ring
  -- Add the three termwise estimates and collect the corrected comparison constant.
  rw [hstationarityIdentity]
  calc
    ‖(-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))) +
        (gradient f (run.point (k + 1)) - gradient f (run.point k)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ ≤
        ‖-(params.beta : ℝ) • run.baseStep k +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
            (error c (run.point k) (run.baseStep k))‖ +
        ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖ +
        ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
          EqualityConstrained.constraintGradient c (run.point k))
            (run.multiplier (k + 1))‖ := by
      calc
        _ ≤ ‖(-(params.beta : ℝ) • run.baseStep k +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
                (error c (run.point k) (run.baseStep k))) +
              (gradient f (run.point (k + 1)) - gradient f (run.point k))‖ +
            ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
              EqualityConstrained.constraintGradient c (run.point k))
                (run.multiplier (k + 1))‖ := norm_add_le _ _
        _ ≤ (‖-(params.beta : ℝ) • run.baseStep k +
              (params.rho : ℝ) • EqualityConstrained.constraintGradient c (run.point k)
                (error c (run.point k) (run.baseStep k))‖ +
              ‖gradient f (run.point (k + 1)) - gradient f (run.point k)‖) +
            ‖(EqualityConstrained.constraintGradient c (run.point (k + 1)) -
              EqualityConstrained.constraintGradient c (run.point k))
                (run.multiplier (k + 1))‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ primalConstant h params.delta params.beta params.rho * ‖run.baseStep k‖ +
        h.gradientLipschitz * displacementFactor h params.delta * ‖run.baseStep k‖ +
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep k‖ :=
      add_le_add (add_le_add hproximalError hgradientDifference) hoperatorApplied
    _ = primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.baseStep k‖ := by
      rw [primalComparisonConstant_def]
      ring

/-- Helper for Corollary 4.2: the corrected multiplier update identifies squared
feasibility with the penalty-scaled squared multiplier increment. -/
private lemma constraintNormSq_eq_multiplierIncrementNormSqDiv
    {ρ β : ℝ} (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    ‖c (run.point (k + 1))‖ ^ 2 =
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / ρ ^ 2 := by
  -- Normalize the corrected-point multiplier update and cancel the positive penalty.
  rw [run.multiplier_succ_eq_add, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos run.rho_pos]
  field_simp [ne_of_gt run.rho_pos]

/-- Helper for Corollary 4.2: every positive transition in an admissible corrected
prefix has squared KKT residual controlled by two adjacent base-step squares. -/
private lemma residual_sq_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
      Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
        (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
  -- Square the stationarity estimate and enlarge it by the preceding-step square.
  have hstationarity := normStationarityPointSucc_le h params run h_admissible hk
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def, primalConstant_def, displacementFactor_def,
      stepConstant_def, errorFactor_def, errorConstant_def]
    positivity
  have hstationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 ≤
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 * ‖run.baseStep k‖ ^ 2 := by
    have hsquared :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hcomparisonNonneg (norm_nonneg _))).2 hstationarity
    simpa only [mul_pow] using hsquared
  have hstationarityExpanded :
      ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 ≤
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) :=
    hstationaritySquare.trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _))
  -- Transport feasibility through the corrected multiplier update and multiplier estimate.
  have hmultiplier :=
    run.norm_multiplier_succ_sub_sq_le h params h_admissible hk_pos hk
  have hfeasibility :
      ‖c (run.point (k + 1))‖ ^ 2 ≤
        multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho ^ 2 *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    calc
      ‖c (run.point (k + 1))‖ ^ 2 =
          ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ^ 2 :=
        constraintNormSq_eq_multiplierIncrementNormSqDiv run k
      _ ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2)) /
            params.rho ^ 2 :=
        div_le_div_of_nonneg_right hmultiplier (sq_nonneg _)
      _ = multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho ^ 2 *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by ring
  -- Expose the aggregate residual, add both component estimates, and factor.
  calc
    KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 =
        ‖KKT.stationarity f c (run.point (k + 1)) (run.multiplier (k + 1))‖ ^ 2 +
          ‖c (run.point (k + 1))‖ ^ 2 := by
      rw [KKT.residual_def,
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) +
        multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho ^ 2 *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) :=
      add_le_add hstationarityExpanded hfeasibility
    _ = Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
        (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
      rw [Residual.comparisonConstant_def]
      ring

/-- Helper for Corollary 4.2: global corrected Lyapunov descent and its lower
bound telescope to a bound on all sampled squared base steps. -/
private lemma summedBaseStepSq_le_lyapunovGap
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_descent : ∀ k, 1 ≤ k →
      run.lyapunov h params (k + 1) ≤
        run.lyapunov h params k -
          (params.beta / 4) * ‖run.baseStep k‖ ^ 2)
    (h_lower : ∀ k, 1 ≤ k →
      lyapunovLowerBound h params ≤ run.lyapunov h params k)
    (K : ℕ) (hK : 2 ≤ K) :
    (∑ k ∈ Finset.Icc 1 (K - 1), ‖run.baseStep k‖ ^ 2) ≤
      4 * (run.lyapunov h params 1 - lyapunovLowerBound h params) /
        params.beta := by
  have hinterval : Finset.Icc 1 (K - 1) = Finset.Ico 1 K := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  -- Sum the one-step rank decreases over the complete sampling interval.
  have hdescentSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
          (params.beta / 4) * ‖run.baseStep k‖ ^ 2) ≤
        ∑ k ∈ Finset.Icc 1 (K - 1),
          (run.lyapunov h params k - run.lyapunov h params (k + 1)) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Icc.mp hk
    have hstep := h_descent k hkBounds.1
    linarith
  -- Range telescoping leaves the initial-to-terminal Lyapunov gap.
  have htelescope :
      (∑ k ∈ Finset.Icc 1 (K - 1),
          (run.lyapunov h params k - run.lyapunov h params (k + 1))) =
        run.lyapunov h params 1 - run.lyapunov h params K := by
    have hendpointLeft : 1 + (K - 1) = K := by omega
    have hendpointRight : K - 1 + 1 = K := by omega
    rw [hinterval, Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov h params (k + 1)) (K - 1))
  have hlower := h_lower K (by omega)
  have henergy :
      (params.beta / 4) *
          (∑ k ∈ Finset.Icc 1 (K - 1), ‖run.baseStep k‖ ^ 2) ≤
        run.lyapunov h params 1 - lyapunovLowerBound h params := by
    rw [← Finset.mul_sum, htelescope] at hdescentSum
    linarith
  -- Divide by the positive proximal coefficient only after telescoping.
  have hscalingNonneg : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  calc
    (∑ k ∈ Finset.Icc 1 (K - 1), ‖run.baseStep k‖ ^ 2) =
        (4 / params.beta) *
          ((params.beta / 4) *
            ∑ k ∈ Finset.Icc 1 (K - 1), ‖run.baseStep k‖ ^ 2) := by
      field_simp [run.beta_pos.ne']
    _ ≤ (4 / params.beta) *
        (run.lyapunov h params 1 - lyapunovLowerBound h params) :=
      mul_le_mul_of_nonneg_left henergy hscalingNonneg
    _ = 4 * (run.lyapunov h params 1 - lyapunovLowerBound h params) /
        params.beta := by ring

/-- Helper for Corollary 4.2: global corrected admissibility and Lyapunov control
bound the sampled residual sum by the deterministic complexity constant. -/
private lemma sumResidualSq_le_deterministicComplexityConstant
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_prefix : ∀ N, run.IsAdmissiblePrefix h N)
    (h_descent : ∀ k, 1 ≤ k →
      run.lyapunov h params (k + 1) ≤
        run.lyapunov h params k -
          (params.beta / 4) * ‖run.baseStep k‖ ^ 2)
    (h_lower : ∀ k, 1 ≤ k →
      lyapunovLowerBound h params ≤ run.lyapunov h params k)
    (K : ℕ) (hK : 2 ≤ K) :
    (∑ k ∈ Finset.Icc 1 (K - 1),
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
        deterministicComplexityConstant h params run := by
  have hmultiplierComparison :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hresidualComparison :
      0 ≤ Residual.comparisonConstant
        (primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound)
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound) params.rho := by
    rw [Residual.comparisonConstant_def]
    exact add_nonneg (sq_nonneg _)
      (div_nonneg hmultiplierComparison (sq_nonneg _))
  -- Sum the pointwise corrected residual comparison over the admissible prefix.
  have hpointwise :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
      ∑ k ∈ Finset.Icc 1 (K - 1),
        Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Icc.mp hk
    have hklt : k < K := by omega
    exact residual_sq_le h params run (h_prefix K) hkBounds.1 hklt
  have hadjacent := sumAdjacent_le (fun k ↦ ‖run.baseStep k‖ ^ 2) K hK
    (fun k ↦ sq_nonneg ‖run.baseStep k‖)
  have hsteps := summedBaseStepSq_le_lyapunovGap h params run
    h_descent h_lower K hK
  have hdeltaNonneg : 0 ≤ (params.delta : ℝ) := by positivity
  have hinitial : ‖run.baseStep 0‖ ^ 2 ≤ params.delta ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hdeltaNonneg).2
      (run.norm_baseStep_le h params (h_prefix 1) (Nat.zero_lt_succ 0))
  -- Combine adjacency and energy estimates in the complexity-constant normal form.
  calc
    (∑ k ∈ Finset.Icc 1 (K - 1),
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
        ∑ k ∈ Finset.Icc 1 (K - 1),
          Residual.comparisonConstant
            (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound)
            (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound) params.rho *
            (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := hpointwise
    _ = Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
          ∑ k ∈ Finset.Icc 1 (K - 1),
            (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
          (‖run.baseStep 0‖ ^ 2 +
            2 * ∑ k ∈ Finset.Icc 1 (K - 1), ‖run.baseStep k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hadjacent hresidualComparison
    _ ≤ Residual.comparisonConstant
          (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound)
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound) params.rho *
          (params.delta ^ 2 +
            2 * (4 * (run.lyapunov h params 1 - lyapunovLowerBound h params) /
              params.beta)) := by
      gcongr
    _ = deterministicComplexityConstant h params run := by
      rw [deterministicComplexityConstant_def]
      ring

/-- Helper for Corollary 4.2: the uniform sampled squared residual is bounded by
the deterministic complexity constant divided by the sample count. -/
private lemma expectResidualSq_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_prefix : ∀ N, run.IsAdmissiblePrefix h N)
    (h_descent : ∀ k, 1 ≤ k →
      run.lyapunov h params (k + 1) ≤
        run.lyapunov h params k -
          (params.beta / 4) * ‖run.baseStep k‖ ^ 2)
    (h_lower : ∀ k, 1 ≤ k →
      lyapunovLowerBound h params ≤ run.lyapunov h params k)
    (K : ℕ) (hK : 2 ≤ K) :
    (𝔼 k ∈ Finset.Icc 1 (K - 1),
        KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2) ≤
      deterministicComplexityConstant h params run / ((K : ℝ) - 1) := by
  have hsum := sumResidualSq_le_deterministicComplexityConstant h params run
    h_prefix h_descent h_lower K hK
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hdenominator : 0 < (K : ℝ) - 1 := by
    have hKreal : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
    linarith
  -- Rewrite the finite expectation as a sum divided by its positive cardinality.
  rw [Finset.expect_eq_sum_div_card, hcard, Nat.cast_sub (by omega), Nat.cast_one]
  exact (div_le_div_iff_of_pos_right hdenominator).2 hsum

/-- Helper for Corollary 4.2: once the corrected deterministic analytic
interfaces and exact iteration threshold hold, a sampled iterate is an `ε`-KKT pair. -/
private lemma existsApproximatePair_of_iterationBound
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_prefix : ∀ N, run.IsAdmissiblePrefix h N)
    (h_descent : ∀ k, 1 ≤ k →
      run.lyapunov h params (k + 1) ≤
        run.lyapunov h params k -
          (params.beta / 4) * ‖run.baseStep k‖ ^ 2)
    (h_lower : ∀ k, 1 ≤ k →
      lyapunovLowerBound h params ≤ run.lyapunov h params k)
    (K : ℕ) (hK : 2 ≤ K) (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      deterministicComplexityConstant h params run * ε⁻¹ ^ 2 ≤ (K : ℝ) - 1) :
    ∃ k ∈ Finset.Icc 1 (K - 1),
      KKT.IsApproximatePair f c ε (run.point (k + 1)) (run.multiplier (k + 1)) := by
  have hsample : (Finset.Icc 1 (K - 1)).Nonempty :=
    Finset.nonempty_Icc.mpr (Nat.le_sub_of_add_le hK)
  obtain ⟨k, hk, hmin⟩ := (Finset.Icc 1 (K - 1)).exists_min_image
    (fun j ↦ KKT.residual f c (run.point (j + 1)) (run.multiplier (j + 1)) ^ 2)
    hsample
  refine ⟨k, hk, ?_⟩
  -- Minimality and the uniform expectation give the selected squared-residual rate.
  have hminExpectation := Finset.le_expect hsample hmin
  have hrate := expectResidualSq_le h params run h_prefix h_descent h_lower K hK
  have hsquaredRate :
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
        deterministicComplexityConstant h params run / ((K : ℝ) - 1) :=
    hminExpectation.trans hrate
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hdenominator : 0 < (K : ℝ) - 1 := by
    have hKreal : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
    linarith
  -- Cancel the inverse-square threshold only after casting it to `ℝ`.
  have hiterationsReal :
      deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2 ≤
        (K : ℝ) - 1 := by
    simpa only [NNReal.coe_inv] using h_iterations
  have hscaled := mul_le_mul_of_nonneg_right hiterationsReal (sq_nonneg (ε : ℝ))
  have hinverseCancellation :
      deterministicComplexityConstant h params run * (ε : ℝ)⁻¹ ^ 2 *
          (ε : ℝ) ^ 2 = deterministicComplexityConstant h params run := by
    field_simp [hεreal.ne']
  rw [hinverseCancellation] at hscaled
  have hconstantDiv :
      deterministicComplexityConstant h params run / ((K : ℝ) - 1) ≤
        (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    nlinarith
  have hsquared :
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
        (ε : ℝ) ^ 2 := hsquaredRate.trans hconstantDiv
  have hresidualNonneg :
      0 ≤ KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) := by
    rw [KKT.residual_def]
    positivity
  have hresidual :
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ≤
        (ε : ℝ) :=
    (sq_le_sq₀ hresidualNonneg ε.coe_nonneg).mp hsquared
  exact KKT.IsApproximatePair.of_residual_le hresidual

/-- Corollary 4.2 (4): the corrected deterministic budget attains an `ε`-KKT pair. -/
theorem existsApproximatePair
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (ε : ℝ≥0) (ε_pos : 0 < ε) :
    ∃ k ∈ Finset.Icc 1 (deterministicIterationBudget h params run ε - 1),
      KKT.IsApproximatePair f c ε (run.point (k + 1)) (run.multiplier (k + 1)) := by
  -- Global localization supplies every finite prefix needed by the analytic estimates.
  have hprefix : ∀ N, run.IsAdmissiblePrefix h N :=
    fun N ↦ run.allPrefixesAdmissible h params h_region N
  have hdescent : ∀ k, 1 ≤ k →
      run.lyapunov h params (k + 1) ≤
        run.lyapunov h params k -
          (params.beta / 4) * ‖run.baseStep k‖ ^ 2 := by
    intro k hk
    exact run.lyapunovDescent h params (hprefix (k + 1)) hk
      (Nat.lt_succ_self k)
  have hlower : ∀ k, 1 ≤ k →
      lyapunovLowerBound h params ≤ run.lyapunov h params k := by
    intro k hk
    exact run.lyapunovLowerBound_le h params (hprefix k) hk (Nat.le_refl k)
  have hbudget := deterministicIterationBudget_spec h params run ε
  -- Telescope the controlled base-step energy and select a minimal residual iterate.
  apply existsApproximatePair_of_iterationBound h params run hprefix hdescent hlower
    (deterministicIterationBudget h params run ε) hbudget.1 ε ε_pos
  simpa only [NNReal.coe_inv] using hbudget.2

/-- Corollary 4.2 (5): corrected deterministic iteration complexity is `O(ε⁻²)`. -/
theorem iterationCount_isBigO
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦
      (run.iterationCount (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Route correction: imported counters are opaque, so use their owner-side equations.
  simpa only [iterationCount_spec, deterministicIterationBudget_def] using
      natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

/-- Corollary 4.2 (6): corrected deterministic first-order oracle complexity is
`O(ε⁻²)`. -/
theorem firstOrderEvaluationCount_isBigO
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦ (run.firstOrderEvaluationCount
      (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Normalize the opaque counter and budget through their owner-side equations.
  simpa only [firstOrderEvaluationCount_spec, deterministicIterationBudget_def] using
      natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

/-- Corollary 4.2 (7): corrected deterministic primal linear-system solve
complexity is `O(ε⁻²)`. -/
theorem primalSolveCount_isBigO
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦
      (run.primalSolveCount (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Normalize the opaque counter and budget through their owner-side equations.
  simpa only [primalSolveCount_spec, deterministicIterationBudget_def] using
      natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

/-- Corollary 4.2 (8): corrected deterministic correction-solve complexity is
`O(ε⁻²)`. -/
theorem correctionSolveCount_isBigO
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    (fun ε : ℝ≥0 ↦ (run.correctionSolveCount
      (deterministicIterationBudget h params run ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Normalize the opaque counter and budget through their owner-side equations.
  simpa only [correctionSolveCount_spec, deterministicIterationBudget_def] using
      natCeilQuadraticBudget_isBigO (deterministicComplexityConstant h params run)

end Run

/- Corollary 4.2 (9): the corrected SPIDER inner batch replaces `Lₛ²` by
`Lₛ² * (χᶜᵒʳ)²`. -/

namespace StochasticRun

open SPIDER.Correction

variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

namespace Localization

namespace RegionCondition

/-- Helper for Corollary 4.2: corrected localization makes the initial
potential exceed the corrected Lyapunov lower bound. -/
private lemma initialPotentialGap_nonneg
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    0 ≤ initialPotentialBound h params - lyapunovLowerBound h params := by
  -- Transport the initial point through the corrected closed localization buffer.
  have hx₀ : x₀ ∈ h.region :=
    h_region.thickening_subset (Metric.self_subset_cthickening X initial_mem)
  have hobjective : h.objectiveLower ≤ f x₀ := h.objectiveLower_le x₀ hx₀
  -- Every correction in the displayed potential and lower bound is nonnegative.
  have hmultiplierConstant :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hdisplacement : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hgradientTerm :
      0 ≤ (h.gradientBound : ℝ) * displacementFactor h params.delta *
        params.delta := by
    positivity
  have hmultiplierTerm :
      0 ≤ 4 * (params.multiplierBound : ℝ) ^ 2 / params.rho := by
    positivity
  have hcorrectionTerm :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * (params.delta : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg hmultiplierConstant hrho.le) (sq_nonneg _)
  have hlowerCorrection :
      0 ≤ (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) := by
    positivity
  rw [initialPotentialBound_def, lyapunovLowerBound_def]
  linarith

/-- Helper for Corollary 4.2: corrected localization gives a strictly positive
initial stopped-step allowance. -/
private lemma initialStepBound_pos
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    0 < initialStepBound h params := by
  -- The positive radius term dominates the nonnegative initial potential gap.
  have hgap := initialPotentialGap_nonneg confidence X initial_mem h_region
  have hdelta : 0 < (params.delta : ℝ) := params.spec.1.1
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  rw [initialStepBound_def]
  positivity

end RegionCondition

/-- Helper for Corollary 4.2: the corrected SPIDER schedule bounds both stopped
estimator-error and stopped base-step energies by their canonical allowances. -/
theorem scheduledStoppedEnergyBounds
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    stoppedGradientErrorEnergy run X K ≤ errorAverageConstant h oracle params ∧
      stoppedBaseStepEnergy run X K ≤ stepAverageConstant h oracle params := by
  -- Specialize the two owner inequalities without unfolding either stopped energy.
  have hsteps := stoppedBaseStepEnergy_le K hK X hX initial_mem run h_region
  have herrors := stoppedGradientErrorEnergy_le run X hX initial_mem h_region K
  rw [SPIDER.refreshBatchSize_coe K hK] at herrors
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have hvariance :
      (K : ℝ) * oracle.noiseLevel ^ 2 / K = oracle.noiseLevel ^ 2 := by
    field_simp [hKzero]
  rw [hvariance] at herrors
  -- Record positivity once before dividing by the corrected coupling constant.
  have hDpos := LALM.Correction.errorStepConstant_pos h params
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hD₀pos := RegionCondition.initialStepBound_pos confidence X initial_mem h_region
  have hD₀nonneg : 0 ≤ initialStepBound h params := hD₀pos.le
  have herrorNonneg := stoppedGradientErrorEnergy_nonneg run X K
  have hcoefficientNonneg :
      0 ≤ (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
        displacementFactor h params.delta ^ 2 /
          (SPIDER.Correction.innerBatchSize h oracle params K : ℝ) := by
    positivity
  have hstepsScaled := mul_le_mul_of_nonneg_left hsteps hcoefficientNonneg
  have hcombined :
      stoppedGradientErrorEnergy run X K ≤
        oracle.noiseLevel ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 /
              (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
            (initialStepBound h params +
              errorStepConstant h params * stoppedGradientErrorEnergy run X K) :=
    herrors.trans (add_le_add (le_refl _) hstepsScaled)
  -- The canonical schedule certificate absorbs one half of the error energy.
  have habsorb := SPIDER.Correction.scheduledErrorStepCoefficient_le_half
    h oracle params K
  have habsorbCommuted :
      ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
          errorStepConstant h params ≤ (1 : ℝ) / 2 := by
    simpa only [mul_comm] using habsorb
  have habsorbError :=
    mul_le_mul_of_nonneg_right habsorbCommuted herrorNonneg
  have hcoefficientLe :
      (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ) ≤
        ((1 : ℝ) / 2) / errorStepConstant h params :=
    (le_div_iff₀ hDpos).2 habsorbCommuted
  have hinitialContribution :=
    mul_le_mul_of_nonneg_right hcoefficientLe hD₀nonneg
  have hinitialNormalized :
      ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
          initialStepBound h params ≤
        initialStepBound h params / (2 * errorStepConstant h params) := by
    calc
      ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
          initialStepBound h params ≤
          ((1 : ℝ) / 2) / errorStepConstant h params *
            initialStepBound h params := hinitialContribution
      _ = initialStepBound h params / (2 * errorStepConstant h params) := by
        field_simp [hDzero]
  have hbound :
      stoppedGradientErrorEnergy run X K ≤
        oracle.noiseLevel ^ 2 +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy run X K := by
    calc
      stoppedGradientErrorEnergy run X K ≤
          oracle.noiseLevel ^ 2 +
            ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
              displacementFactor h params.delta ^ 2 /
                (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
              (initialStepBound h params +
                errorStepConstant h params * stoppedGradientErrorEnergy run X K) :=
        hcombined
      _ = oracle.noiseLevel ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 /
              (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
            initialStepBound h params +
          (((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 /
              (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
            errorStepConstant h params) * stoppedGradientErrorEnergy run X K := by
        ring
      _ ≤ oracle.noiseLevel ^ 2 +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy run X K :=
        add_le_add (add_le_add (le_refl _) hinitialNormalized) habsorbError
  -- Solve the scalar inequality, then substitute it into the base-step bound.
  have hinitialDouble :
      2 * (initialStepBound h params / (2 * errorStepConstant h params)) =
        initialStepBound h params / errorStepConstant h params := by
    field_simp [hDzero]
  have herrorBound :
      stoppedGradientErrorEnergy run X K ≤
        errorAverageConstant h oracle params := by
    rw [errorAverageConstant_def]
    linarith [hbound, hinitialDouble]
  have hstepBound :
      stoppedBaseStepEnergy run X K ≤ stepAverageConstant h oracle params := by
    calc
      stoppedBaseStepEnergy run X K ≤
          initialStepBound h params +
            errorStepConstant h params * stoppedGradientErrorEnergy run X K := hsteps
      _ ≤ initialStepBound h params +
          errorStepConstant h params * errorAverageConstant h oracle params :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left herrorBound hDpos.le)
      _ = stepAverageConstant h oracle params := by
        rw [errorAverageConstant_def, stepAverageConstant_def]
        field_simp [hDzero]
        ring
  exact ⟨herrorBound, hstepBound⟩

/-- Helper for Corollary 4.2: the active corrected estimator-error energy through
a finite horizon, with every summand killed after localization exit. -/
private noncomputable def activeGradientErrorEnergy
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (omega : Ω) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range K,
    (survivalEvent run X k).indicator
      (fun omega' ↦ ENNReal.ofReal (‖run.gradientError k omega'‖ ^ 2)) omega

/-- Helper for Corollary 4.2: the real-valued active corrected estimator-error
energy corresponding to `activeGradientErrorEnergy`. -/
private noncomputable def activeGradientErrorEnergyReal
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (omega : Ω) : ℝ :=
  ∑ k ∈ Finset.range K,
    (survivalEvent run X k).indicator
      (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega

/-- Helper for Corollary 4.2: active corrected estimator energy is the
nonnegative-real embedding of its real-valued form. -/
private lemma activeGradientErrorEnergy_eq_ofReal
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (omega : Ω) :
    activeGradientErrorEnergy run X K omega =
      ENNReal.ofReal (activeGradientErrorEnergyReal run X K omega) := by
  -- Commute `ofReal` through the finite sum after exposing each indicator.
  unfold activeGradientErrorEnergy activeGradientErrorEnergyReal
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hactive : omega ∈ survivalEvent run X k
    · simp only [Set.indicator_of_mem hactive]
    · simp [hactive]
  · intro k hk
    by_cases hactive : omega ∈ survivalEvent run X k
    · simp only [Set.indicator_of_mem hactive]
      exact sq_nonneg _
    · simp [hactive]

/-- Helper for Corollary 4.2: active corrected estimator energy is almost
everywhere measurable for a measurable localization set. -/
private lemma aemeasurable_activeGradientErrorEnergy
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (confidence : ℝ)
    (h_region : RegionCondition h oracle params confidence X) (K : ℕ) :
    AEMeasurable (activeGradientErrorEnergy run X K) ℙ := by
  -- Each term inherits measurability from its pre-exit integrability certificate.
  unfold activeGradientErrorEnergy
  have hsum : AEMeasurable
      (∑ k ∈ Finset.range K, fun omega ↦
        (survivalEvent run X k).indicator
          (fun omega' ↦ ENNReal.ofReal (‖run.gradientError k omega'‖ ^ 2)) omega) ℙ := by
    apply Finset.aemeasurable_sum
    intro k hk
    have hactive := nullMeasurableSet_survivalEvent run X hX k
    have hintegrable :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact (aemeasurable_indicator_iff₀ hactive).mpr
      hintegrable.aemeasurable.ennreal_ofReal
  have hfun :
      (fun omega ↦
        ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ENNReal.ofReal (‖run.gradientError k omega'‖ ^ 2)) omega) =
        ∑ k ∈ Finset.range K, fun omega ↦
          (survivalEvent run X k).indicator
            (fun omega' ↦ ENNReal.ofReal (‖run.gradientError k omega'‖ ^ 2)) omega := by
    funext omega
    simp only [Finset.sum_apply]
  rw [hfun]
  exact hsum

/-- Helper for Corollary 4.2: integrating active corrected estimator energy
recovers the stopped estimator-error energy. -/
private lemma lintegral_activeGradientErrorEnergy
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (confidence : ℝ)
    (h_region : RegionCondition h oracle params confidence X) (K : ℕ) :
    ∫⁻ omega, activeGradientErrorEnergy run X K omega ∂ℙ =
      ENNReal.ofReal (stoppedGradientErrorEnergy run X K) := by
  -- Exchange the finite sum with the lintegral and convert each restricted term.
  unfold activeGradientErrorEnergy
  rw [lintegral_finsetSum']
  · rw [stoppedGradientErrorEnergy_def, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro k hk
      have hactive := nullMeasurableSet_survivalEvent run X hX k
      have hintegrable :=
        integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
      rw [lintegral_indicator₀ hactive]
      exact (ofReal_integral_eq_lintegral_ofReal hintegrable
        (ae_of_all _ fun omega ↦ sq_nonneg ‖run.gradientError k omega‖)).symm
    · intro k hk
      exact integral_nonneg fun omega ↦ sq_nonneg ‖run.gradientError k omega‖
  · intro k hk
    have hactive := nullMeasurableSet_survivalEvent run X hX k
    have hintegrable :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact (aemeasurable_indicator_iff₀ hactive).mpr
      hintegrable.aemeasurable.ennreal_ofReal

/-- Helper for Corollary 4.2: Markov's inequality bounds a positive active
estimator-energy threshold by the stopped expectation. -/
private lemma measure_activeGradientErrorEnergy_ge_le
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (confidence : ℝ)
    (h_region : RegionCondition h oracle params confidence X)
    (K : ℕ) (threshold : ℝ) (threshold_pos : 0 < threshold) :
    ℙ {omega | ENNReal.ofReal threshold ≤
      activeGradientErrorEnergy run X K omega} ≤
        ENNReal.ofReal (stoppedGradientErrorEnergy run X K / threshold) := by
  -- Apply the ENNReal Markov inequality and identify its two normalization terms.
  have hmarkov := meas_ge_le_lintegral_div
    (aemeasurable_activeGradientErrorEnergy run X hX initial_mem confidence h_region K)
    ((ENNReal.ofReal_ne_zero_iff).mpr threshold_pos) ENNReal.ofReal_ne_top
  rw [lintegral_activeGradientErrorEnergy run X hX initial_mem confidence h_region K]
    at hmarkov
  rw [ENNReal.ofReal_div_of_pos threshold_pos]
  exact hmarkov

/-- Helper for Corollary 4.2: the corrected scheduled estimator-error allowance
is strictly positive under localization. -/
private lemma errorAverageConstant_pos
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) :
    0 < errorAverageConstant h oracle params := by
  -- Its positive initial allowance quotient is independent of the noise term.
  have hinitial := RegionCondition.initialStepBound_pos confidence X initial_mem h_region
  have hcoefficient := LALM.Correction.errorStepConstant_pos h params
  rw [errorAverageConstant_def]
  positivity

/-- Helper for Corollary 4.2: the corrected Lyapunov coefficient multiplying
adjacent estimator errors is strictly positive. -/
private lemma lyapunovErrorConstant_pos :
    0 < lyapunovErrorConstant h params := by
  -- The positive inverse-`beta` term dominates the remaining nonnegative term.
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  rw [lyapunovErrorConstant_def]
  positivity

/-- Helper for Corollary 4.2: the active prefix length is the first exit time
truncated at the requested finite horizon. -/
private noncomputable def activePrefixLength
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (omega : Ω) : ℕ :=
  min K ((exitTime run X omega).untopD K)

/-- Helper for Corollary 4.2: the truncated corrected active-prefix length is
positive, bounded by its horizon, and characterizes active indices. -/
private lemma activePrefixLength_spec
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (hK : 1 ≤ K)
    (omega : Ω) :
    1 ≤ activePrefixLength run X K omega ∧
      activePrefixLength run X K omega ≤ K ∧
      ∀ k < K, (k < activePrefixLength run X K omega ↔
        omega ∈ survivalEvent run X k) := by
  -- Compare the natural truncation with the `WithTop`-valued hitting time.
  have hexitLower : (1 : WithTop ℕ) ≤ exitTime run X omega := by
    rw [exitTime_def]
    exact MeasureTheory.le_hittingAfter (u := run.point) (s := Xᶜ) (n := 1) omega
  have hdefaultLower : 1 ≤ (exitTime run X omega).untopD K := by
    rw [WithTop.le_untopD_iff (fun _ ↦ hK)]
    exact hexitLower
  refine ⟨(Nat.le_min).2 ⟨hK, hdefaultLower⟩, min_le_left _ _, ?_⟩
  intro k hk
  have hdefault :
      k < (exitTime run X omega).untopD K ↔
        (k : WithTop ℕ) < exitTime run X omega := by
    apply WithTop.lt_untopD_iff
    intro hexitTop
    simpa only [hexitTop, WithTop.untopD_top] using hk
  have hsurvival :
      omega ∈ survivalEvent run X k ↔
        (k : WithTop ℕ) < exitTime run X omega :=
    mem_survivalEvent_iff_lt_exitTime run X k omega
  rw [activePrefixLength, lt_min_iff, hdefault, hsurvival]
  simp only [hk, true_and]

/-- Helper for Corollary 4.2: a corrected survival-indicator sum is the
ordinary sum over the truncated active prefix. -/
private lemma activePrefixSum_eq
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (K : ℕ) (hK : 1 ≤ K)
    (omega : Ω) (g : ℕ → Ω → ℝ) :
    (∑ k ∈ Finset.range K,
        (survivalEvent run X k).indicator (g k) omega) =
      ∑ k ∈ Finset.range (activePrefixLength run X K omega), g k omega := by
  -- Replace indicators by their active-index test and trim the zero tail.
  have hindicator :
      (∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator (g k) omega) =
        ∑ k ∈ Finset.range K,
          if k < activePrefixLength run X K omega then g k omega else 0 := by
    apply Finset.sum_congr rfl
    intro k hkRange
    have hk : k < K := Finset.mem_range.mp hkRange
    have hactive := (activePrefixLength_spec run X K hK omega).2.2 k hk
    by_cases hkPrefix : k < activePrefixLength run X K omega
    · rw [Set.indicator_of_mem (hactive.mp hkPrefix), if_pos hkPrefix]
    · rw [Set.indicator_of_notMem (fun hmem ↦ hkPrefix (hactive.mpr hmem)),
        if_neg hkPrefix]
  rw [hindicator]
  have hsubset :
      Finset.range (activePrefixLength run X K omega) ⊆ Finset.range K :=
    Finset.range_mono (activePrefixLength_spec run X K hK omega).2.1
  have htrimmed :
      (∑ k ∈ Finset.range (activePrefixLength run X K omega),
          if k < activePrefixLength run X K omega then g k omega else 0) =
        ∑ k ∈ Finset.range K,
          if k < activePrefixLength run X K omega then g k omega else 0 :=
    Finset.sum_subset hsubset
      (fun k _hkRange hkPrefix ↦ by
        have hkNotLt : ¬k < activePrefixLength run X K omega := by
          simpa only [Finset.mem_range] using hkPrefix
        simp only [if_neg hkNotLt])
  calc
    (∑ k ∈ Finset.range K,
        if k < activePrefixLength run X K omega then g k omega else 0) =
        ∑ k ∈ Finset.range (activePrefixLength run X K omega),
          if k < activePrefixLength run X K omega then g k omega else 0 := htrimmed.symm
    _ = ∑ k ∈ Finset.range (activePrefixLength run X K omega), g k omega := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [if_pos (Finset.mem_range.mp hk)]

/-- Helper for Corollary 4.2: a bounded corrected multiplier lets the Lyapunov
rank control the objective at the same iterate. -/
private lemma objective_le_lyapunov
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω)
    (hmultiplier : ‖run.multiplier k omega‖ ≤ params.multiplierBound) :
    f (run.point k omega) ≤ run.lyapunov k omega +
      params.multiplierBound ^ 2 / (2 * params.rho) := by
  -- Complete the square in the augmented-Lagrangian constraint contribution.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hinner :
      -(‖run.multiplier k omega‖ * ‖c (run.point k omega)‖) ≤
        ⟪run.multiplier k omega, c (run.point k omega)⟫_ℝ :=
    neg_le_of_abs_le
      (abs_real_inner_le_norm (run.multiplier k omega) (c (run.point k omega)))
  have hyoung :
      2 * ‖c (run.point k omega)‖ * ‖run.multiplier k omega‖ ≤
        params.rho * ‖c (run.point k omega)‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖run.multiplier k omega‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have hyoungHalf :
      ‖run.multiplier k omega‖ * ‖c (run.point k omega)‖ ≤
        params.rho / 2 * ‖c (run.point k omega)‖ ^ 2 +
          ‖run.multiplier k omega‖ ^ 2 / (2 * params.rho) := by
    have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hdivided :=
      div_le_div_of_nonneg_right hyoung htwoNonneg
    calc
      ‖run.multiplier k omega‖ * ‖c (run.point k omega)‖ =
          (2 * ‖c (run.point k omega)‖ * ‖run.multiplier k omega‖) / 2 := by ring
      _ ≤ (params.rho * ‖c (run.point k omega)‖ ^ 2 +
          (params.rho : ℝ)⁻¹ * ‖run.multiplier k omega‖ ^ 2) / 2 := hdivided
      _ = params.rho / 2 * ‖c (run.point k omega)‖ ^ 2 +
          ‖run.multiplier k omega‖ ^ 2 / (2 * params.rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq :
      ‖run.multiplier k omega‖ ^ 2 ≤ (params.multiplierBound : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hboundNonneg).2 hmultiplier
  have htwoPos : (0 : ℝ) < 2 := by norm_num
  have hmultiplierDiv :
      ‖run.multiplier k omega‖ ^ 2 / (2 * (params.rho : ℝ)) ≤
        (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) :=
    (div_le_div_iff_of_pos_right (mul_pos htwoPos hrho)).2 hmultiplierSq
  have hconstraintLower :
      -(params.multiplierBound ^ 2 / (2 * (params.rho : ℝ))) ≤
        ⟪run.multiplier k omega, c (run.point k omega)⟫_ℝ +
          params.rho / 2 * ‖c (run.point k omega)‖ ^ 2 := by
    linarith
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
        ‖run.baseStep (k - 1) omega‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg hrho.le) (sq_nonneg _)
  rw [run.lyapunov_def, augmentedLagrangian_def]
  linarith

/-- Helper for Corollary 4.2: a positive bounded corrected path has terminal
Lyapunov rank controlled by the initial potential and its estimator errors. -/
private lemma terminalLyapunov_le
    {Q B b : ℕ+}
    {run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    (hN : 1 ≤ N) :
    run.lyapunov N omega ≤ initialPotentialBound h params +
      2 * lyapunovErrorConstant h params *
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
  -- Sum the one-step fixed-path inequalities and telescope the Lyapunov rank.
  have hdescent :
      (∑ k ∈ Finset.Ico 1 N,
          (params.beta / 4) * ‖run.baseStep k omega‖ ^ 2) ≤
        ∑ k ∈ Finset.Ico 1 N,
          ((run.lyapunov k omega - run.lyapunov (k + 1) omega) +
            lyapunovErrorConstant h params *
              (‖run.gradientError k omega‖ ^ 2 +
                ‖run.gradientError (k - 1) omega‖ ^ 2)) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Ico.mp hk
    have hstep := bounds.lyapunovDescent hkBounds.1 hkBounds.2
    linarith
  have hendpointLeft : 1 + (N - 1) = N := by omega
  have hendpointRight : N - 1 + 1 = N := by omega
  have htelescope :
      (∑ k ∈ Finset.Ico 1 N,
          (run.lyapunov k omega - run.lyapunov (k + 1) omega)) =
        run.lyapunov 1 omega - run.lyapunov N omega := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov (k + 1) omega) (N - 1))
  have hcurrentSubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError k omega‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k omega‖)
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) omega‖ ^ 2) =
        ∑ j ∈ Finset.range (N - 1), ‖run.gradientError j omega‖ ^ 2 := by
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
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) omega‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k omega‖)
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 N,
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2)) ≤
        2 * ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  have herrorCoefficientNonneg : 0 ≤ lyapunovErrorConstant h params := by
    rw [lyapunovErrorConstant_def, LALM.multiplierErrorConstant_def]
    positivity
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  have hstepContributionNonneg :
      0 ≤ (params.beta / 4) *
        ∑ k ∈ Finset.Ico 1 N, ‖run.baseStep k omega‖ ^ 2 := by
    positivity
  have hinitial := bounds.lyapunovOne_le_initialPotentialBound hN
  nlinarith

/-- Helper for Corollary 4.2: survival through a positive corrected prefix
controls its terminal objective by active estimator-error energy. -/
private lemma objectiveAtPrefixEnd_le_of_survival
    {Q B b : ℕ+}
    (N : ℕ) (hN : 1 ≤ N)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (confidence : ℝ)
    (h_region : RegionCondition h oracle params confidence X)
    (omega : Ω) (homega : omega ∈ survivalEvent run X (N - 1)) :
    f (run.point N omega) ≤ deterministicObjectiveBound h params +
      2 * lyapunovErrorConstant h params *
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
  -- Package all pre-exit bounds into the stable fixed-path interface.
  have hendpoint : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hraw := preExitPrefixBounds run X initial_mem h_region omega (N - 1) homega
  have bounds : run.BoundedAdmissiblePath N omega := by
    constructor
    · intro j hj
      have hj' : j < N - 1 + 1 := by
        simpa only [hendpoint] using hj
      exact hraw.1 j hj'
    · intro j hj
      have hj' : j < N - 1 + 1 := by
        simpa only [hendpoint] using hj
      exact hraw.2.1 j hj'
    · intro j hj
      have hj' : j ≤ N - 1 + 1 := by
        simpa only [hendpoint] using hj
      exact hraw.2.2 j hj'
  have hterminal := terminalLyapunov_le bounds hN
  have hobjective := objective_le_lyapunov run N omega
    (bounds.multiplier_le N (Nat.le_refl N))
  rw [deterministicObjectiveBound_def]
  linarith

/-- Helper for Corollary 4.2: an exit by the horizon has a first corrected
iterate whose objective is controlled by active estimator errors. -/
private lemma objectiveAtExit_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (omega : Ω) (homega : exitTime run X omega ≤ K) :
    ∃ j ∈ Set.Icc 1 K, run.point j omega ∉ X ∧
      f (run.point j omega) ≤ deterministicObjectiveBound h params +
        2 * lyapunovErrorConstant h params *
          activeGradientErrorEnergyReal run X K omega ∧
      ‖c (run.point j omega)‖ ≤
        2 * params.multiplierBound / params.rho := by
  -- Extract the finite first-exit index and the point witnessing exit.
  have hexitFinite : exitTime run X omega ≠ ⊤ := by
    intro hexitTop
    have htop : (⊤ : ℕ∞) ≤ (K : ℕ∞) := by
      simpa only [hexitTop] using homega
    exact ENat.coe_ne_top K (top_unique htop)
  have hhittingFinite :
      MeasureTheory.hittingAfter run.point Xᶜ 1 omega ≠ ⊤ := by
    intro hhittingTop
    have hexitAt := congrFun (exitTime_def run X) omega
    exact hexitFinite (hexitAt.trans hhittingTop)
  have hexitPoint :
      run.point (exitTime run X omega).untopA omega ∈ Xᶜ := by
    simpa only [exitTime_def] using
      (MeasureTheory.hittingAfter_mem_set_of_ne_top
        (u := run.point) (s := Xᶜ) (n := 1) (ω := omega) hhittingFinite)
  lift exitTime run X omega to ℕ using hexitFinite with j hj
  have hjUpper : j ≤ K := ENat.coe_le_coe.mp homega
  have hexitLower : (1 : WithTop ℕ) ≤ exitTime run X omega := by
    rw [exitTime_def]
    exact MeasureTheory.le_hittingAfter
      (u := run.point) (s := Xᶜ) (n := 1) omega
  have hjLowerTop : (1 : WithTop ℕ) ≤ (j : WithTop ℕ) :=
    hexitLower.trans_eq hj.symm
  have hjLower : 1 ≤ j := by
    exact_mod_cast hjLowerTop
  have hjOutside : run.point j omega ∉ X := by
    simpa [← ENat.some_eq_coe] using hexitPoint
  -- The predecessor of the first exit is the terminal surviving prefix.
  have hKone : 1 ≤ K := by omega
  have hactiveLength : activePrefixLength run X K omega = j := by
    rw [activePrefixLength, ← hj, untopD_coe_enat, min_eq_right hjUpper]
  have hjPredLtK : j - 1 < K := by omega
  have hjSurvival : omega ∈ survivalEvent run X (j - 1) := by
    have hspec := (activePrefixLength_spec run X K hKone omega).2.2
      (j - 1) hjPredLtK
    apply hspec.mp
    rw [hactiveLength]
    omega
  have hobjective := objectiveAtPrefixEnd_le_of_survival j hjLower X initial_mem
    run confidence h_region omega hjSurvival
  have hconstraint := constraintNorm_le_of_survival run X initial_mem h_region
    omega j hjLower hjSurvival
  have hactiveError :
      activeGradientErrorEnergyReal run X K omega =
        ∑ k ∈ Finset.range j, ‖run.gradientError k omega‖ ^ 2 := by
    unfold activeGradientErrorEnergyReal
    rw [activePrefixSum_eq run X K hKone omega
      (fun k omega' ↦ ‖run.gradientError k omega'‖ ^ 2), hactiveLength]
  refine ⟨j, ⟨hjLower, hjUpper⟩, hjOutside, ?_, hconstraint⟩
  rw [hactiveError]
  exact hobjective

/-- Helper for Corollary 4.2: exit by the horizon forces corrected active
estimator energy above the confidence-scaled scheduled allowance. -/
private lemma exit_imp_activeGradientErrorEnergy_ge
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (omega : Ω) (homega : exitTime run X omega ≤ K) :
    ENNReal.ofReal (errorAverageConstant h oracle params / confidence) ≤
      activeGradientErrorEnergy run X K omega := by
  -- Compare the controlled first-exit objective with sublevel containment.
  obtain ⟨j, hj, hjOutside, hobjectiveUpper, hconstraint⟩ :=
    objectiveAtExit_le K hK confidence X initial_mem run h_region omega homega
  have hjNotSublevel : run.point j omega ∉ sublevel h oracle params confidence := by
    intro hjSublevel
    exact hjOutside (h_region.sublevel_subset hjSublevel)
  have hobjectiveLower :
      objectiveBound h oracle params confidence < f (run.point j omega) := by
    apply lt_of_not_ge
    intro hobjective
    exact hjNotSublevel
      ((mem_sublevel h oracle params confidence _).2 ⟨hobjective, hconstraint⟩)
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
        activeGradientErrorEnergyReal run X K omega := by
    nlinarith
  rw [activeGradientErrorEnergy_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal hactiveLower.le

/-- Helper for Corollary 4.2: corrected localization exit by `K` has
probability at most the prescribed confidence. -/
private theorem exitProbability_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    ℙ {omega | exitTime run X omega ≤ K} ≤ ENNReal.ofReal confidence := by
  -- Insert the first-exit energy threshold into Markov's inequality.
  have herrorPos := errorAverageConstant_pos confidence X initial_mem h_region
  have hthresholdPos :
      0 < errorAverageConstant h oracle params / confidence :=
    div_pos herrorPos confidence_pos
  have hexitSubset :
      {omega | exitTime run X omega ≤ K} ⊆
        {omega | ENNReal.ofReal
            (errorAverageConstant h oracle params / confidence) ≤
          activeGradientErrorEnergy run X K omega} := by
    intro omega homega
    exact exit_imp_activeGradientErrorEnergy_ge K hK confidence X initial_mem
      run h_region omega homega
  have hmarkov := measure_activeGradientErrorEnergy_ge_le run X hX initial_mem
    confidence h_region K (errorAverageConstant h oracle params / confidence) hthresholdPos
  have hstopped :=
    (scheduledStoppedEnergyBounds K hK confidence X hX initial_mem run h_region).1
  have hquotient :
      stoppedGradientErrorEnergy run X K /
          (errorAverageConstant h oracle params / confidence) ≤
        errorAverageConstant h oracle params /
          (errorAverageConstant h oracle params / confidence) :=
    (div_le_div_iff_of_pos_right hthresholdPos).2 hstopped
  have hcancel :
      errorAverageConstant h oracle params /
          (errorAverageConstant h oracle params / confidence) = confidence := by
    field_simp [herrorPos.ne', confidence_pos.ne']
  calc
    ℙ {omega | exitTime run X omega ≤ K} ≤
        ℙ {omega | ENNReal.ofReal
            (errorAverageConstant h oracle params / confidence) ≤
          activeGradientErrorEnergy run X K omega} := measure_mono hexitSubset
    _ ≤ ENNReal.ofReal
        (stoppedGradientErrorEnergy run X K /
          (errorAverageConstant h oracle params / confidence)) := hmarkov
    _ ≤ ENNReal.ofReal
        (errorAverageConstant h oracle params /
          (errorAverageConstant h oracle params / confidence)) :=
      ENNReal.ofReal_le_ofReal hquotient
    _ = ENNReal.ofReal confidence := by rw [hcancel]

/-- Helper for Corollary 4.2: every corrected scheduled attempt survives its
localization test with probability at least `1 - confidence`. -/
theorem survivalProbability_ge
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    ENNReal.ofReal (1 - confidence) ≤ ℙ (survivalEvent run X K) := by
  let exitEvent : Set Ω := {omega | exitTime run X omega ≤ K}
  have hexitEvent :
      exitEvent = ⋃ j ∈ Finset.Icc 1 K, run.point j ⁻¹' Xᶜ := by
    ext omega
    simp only [exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  have hexitNullMeasurable : NullMeasurableSet exitEvent ℙ := by
    rw [hexitEvent]
    exact (Finset.Icc 1 K).nullMeasurableSet_biUnion fun j _hj ↦
      (run.aemeasurable_point j).nullMeasurableSet_preimage hX.compl
  have hsurvival : survivalEvent run X K = exitEventᶜ := by
    ext omega
    rw [mem_survivalEvent]
    simp only [Set.mem_compl_iff, exitEvent, Set.mem_setOf_eq, exitTime_le_iff]
    simp
  have hexit : ℙ exitEvent ≤ ENNReal.ofReal confidence :=
    exitProbability_le K hK confidence confidence_pos X hX initial_mem run h_region
  -- Convert the exit upper bound through probability complementation.
  rw [hsurvival, prob_compl_eq_one_sub₀ hexitNullMeasurable,
    ENNReal.ofReal_sub 1 confidence_pos.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hexit 1

end Localization

/-- Helper for Corollary 4.2: every corrected base-step mean square is
nonnegative. -/
private lemma baseStepMeanSquare_nonneg
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.baseStepMeanSquare k := by
  -- Integrate the pointwise nonnegative squared norm.
  rw [run.baseStepMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.baseStep k ω‖

/-- Helper for Corollary 4.2: every corrected gradient-error mean square is
nonnegative. -/
private lemma gradientErrorMeanSquare_nonneg
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.gradientErrorMeanSquare k := by
  -- Integrate the pointwise nonnegative squared norm.
  rw [run.gradientErrorMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.gradientError k ω‖

/-- Helper for Corollary 4.2: a corrected stochastic multiplier update changes
the augmented Lagrangian by the penalty-scaled squared multiplier increment. -/
private lemma augmentedLagrangian_multiplier_succ_eq
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier (k + 1) ω) =
      ℒ[f, c; params.rho](run.point (k + 1) ω, run.multiplier k ω) +
        ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho := by
  -- Normalize both corrected owner updates before expanding the multiplier term.
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) := by
    rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
  rw [augmentedLagrangian_def, augmentedLagrangian_def, hupdate,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  field_simp [params.spec.1.2.2.1.ne']
  ring

/-- Helper for Corollary 4.2: the corrected parameter inequality absorbs the
multiplier-primal coefficient after division by the penalty. -/
private lemma multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  -- Clear the two positive denominators in the stored parameter inequality.
  have hscaled :
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Corollary 4.2: a pathwise admissible corrected stochastic
transition decreases the Lyapunov rank up to its two adjacent estimator errors. -/
private lemma lyapunovDescent
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k < N) (ω : Ω) :
    run.lyapunov (k + 1) ω ≤
      run.lyapunov k ω - (params.beta / 4) * ‖run.baseStep k ω‖ ^ 2 +
        lyapunovErrorConstant h params *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- Combine fixed-multiplier descent with the corrected multiplier estimate.
  have hlagrangian := run.augmentedLagrangianDescent h_admissible hk ω
  have hmultiplier :=
    run.norm_multiplier_succ_sub_sq_le h_admissible hk_pos hk ω
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierDivided :=
    (div_le_div_iff_of_pos_right hrho).2 hmultiplier
  have hmultiplierDiv :
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
        (LALM.multiplierErrorConstant h / params.rho) *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 / params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
                (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
            LALM.multiplierErrorConstant h *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) / params.rho :=
        hmultiplierDivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / params.rho) *
            (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
          (LALM.multiplierErrorConstant h / params.rho) *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  have hcoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have hcurrent :
      2 * (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep k ω‖ ^ 2 ≤
        (params.beta / 4) * ‖run.baseStep k ω‖ ^ 2 := by
    have htwiceCoefficient :
        2 * (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) ≤ params.beta / 4 := by
      linarith
    exact mul_le_mul_of_nonneg_right htwiceCoefficient (sq_nonneg _)
  have hpreviousErrorNonneg :
      (0 : ℝ) ≤ (2 / params.beta) * ‖run.gradientError (k - 1) ω‖ ^ 2 := by
    positivity
  -- The preceding base-step term cancels after exposing the two Lyapunov values.
  rw [run.lyapunov_def, run.lyapunov_def,
    augmentedLagrangian_multiplier_succ_eq run, Nat.add_sub_cancel,
    lyapunovErrorConstant_def]
  nlinarith

/-- Helper for Corollary 4.2: a bounded multiplier gives the uniform corrected
augmented-Lagrangian lower bound on the regularity region. -/
private lemma augmentedLagrangian_lowerBound_of_norm_multiplier_le
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
  have hyoungDivided :=
    div_le_div_of_nonneg_right hyoung (by norm_num : (0 : ℝ) ≤ 2)
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
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * rho) ≤ bound ^ 2 / (2 * rho) :=
    (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hrho)).2 hmultiplierSq
  rw [augmentedLagrangian_def]
  have hobjective := h.objectiveLower_le x hx
  linarith

/-- Helper for Corollary 4.2: every positive corrected stochastic Lyapunov
value in a pathwise admissible prefix is above the uniform lower bound. -/
private lemma lyapunovLowerBound_le
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N)
    (hk_pos : 1 ≤ k) (hk : k ≤ N) (ω : Ω) :
    LALM.Correction.lyapunovLowerBound h params ≤ run.lyapunov k ω := by
  -- Recover the endpoint from the preceding corrected admissible transition.
  have hkPrevious : k - 1 < N := by omega
  have hadm := (run.isAdmissiblePrefix_iff N).1 h_admissible
    (k - 1) hkPrevious ω
  have hx := nextPoint_mem_region h (run.point (k - 1) ω)
    (run.baseStep (k - 1) ω) hadm
  rw [← run.point_succ (k - 1) ω, Nat.sub_add_cancel hk_pos] at hx
  have hmultiplier :=
    (run.admissiblePrefix_normBounds N h_admissible).2 k hk ω
  have hlower := augmentedLagrangian_lowerBound_of_norm_multiplier_le h params.rho
    (run.point k ω) (run.multiplier k ω) params.multiplierBound
    params.spec.1.2.2.1 hx hmultiplier (by positivity)
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            ‖run.baseStep (k - 1) ω‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg params.spec.1.2.2.1.le) (sq_nonneg _)
  rw [LALM.Correction.lyapunovLowerBound_def, run.lyapunov_def]
  linarith

/-- Helper for Corollary 4.2: the objective change across both corrected
admissible legs is bounded by the corrected displacement factor. -/
private lemma normObjectiveChangeAlongCorrectedStep_le
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
      ‖step c x p‖ ≤ stepConstant h * ‖p‖ ^ 2 :=
        norm_step_le h x p hadm
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

/-- Helper for Corollary 4.2: the first corrected stochastic Lyapunov value is
bounded by the corrected initial potential on every admissible sample path. -/
private lemma lyapunovOne_le_initialPotentialBound
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N : ℕ} (hN : 1 ≤ N) (h_admissible : run.IsAdmissiblePrefix N)
    (ω : Ω) :
    run.lyapunov 1 ω ≤ initialPotentialBound h params := by
  have hzeroLt : 0 < N := by omega
  have hadm := (run.isAdmissiblePrefix_iff N).1 h_admissible 0 hzeroLt ω
  have hnormBounds := run.admissiblePrefix_normBounds N h_admissible
  have hstep := hnormBounds.1 0 hzeroLt ω
  have hmultiplierZero := hnormBounds.2 0 (Nat.zero_le N) ω
  have hmultiplierOne := hnormBounds.2 1 hN ω
  -- The two corrected legs give exactly the objective allowance in `Φbar₁`.
  have hobjectiveChange :=
    normObjectiveChangeAlongCorrectedStep_le h params
      (run.point 0 ω) (run.baseStep 0 ω) hadm hstep
  have hsignedObjective :
      f (run.point 1 ω) - f (run.point 0 ω) ≤
        ‖f (run.point 1 ω) - f (run.point 0 ω)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (run.point 1 ω) - f (run.point 0 ω))
  have hobjective :
      f (run.point 1 ω) ≤
        f x₀ + h.gradientBound * displacementFactor h params.delta * params.delta := by
    have hgradientStep :
        h.gradientBound * displacementFactor h params.delta * ‖run.baseStep 0 ω‖ ≤
          h.gradientBound * displacementFactor h params.delta * params.delta := by
      have hfactorNonneg :
          0 ≤ (h.gradientBound : ℝ) * displacementFactor h params.delta := by
        rw [displacementFactor_def, stepConstant_def]
        positivity
      exact mul_le_mul_of_nonneg_left hstep hfactorNonneg
    rw [← run.point_succ 0] at hobjectiveChange
    rw [run.point_zero] at hsignedObjective hobjectiveChange
    linarith
  -- The multiplier update controls the constraint part by the stored dual bound.
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point 1 ω) =
        run.multiplier 1 ω - run.multiplier 0 ω := by
    have hupdate :
        run.multiplier 1 ω = run.multiplier 0 ω +
          (params.rho : ℝ) • c (run.point 1 ω) := by
      rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
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
  have hscaledResidualSq :
      (params.rho * ‖c (run.point 1 ω)‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hrho.le (norm_nonneg _))
      (mul_nonneg (by norm_num) hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪run.multiplier 1 ω, c (run.point 1 ω)⟫_ℝ +
          params.rho / 2 * ‖c (run.point 1 ω)‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ hrho).2
    nlinarith
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖run.baseStep 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstep
  have hcorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep 0 ω‖ ^ 2 ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq (div_nonneg hconstantNonneg hrho.le)
  -- Expose the rank and corrected potential only after all four terms are bounded.
  rw [run.lyapunov_def, augmentedLagrangian_def, initialPotentialBound_def]
  norm_num only [Nat.reduceSub]
  linarith

/-- Helper for Corollary 4.2: pathwise corrected Lyapunov telescoping bounds
all base-step squares by the initial allowance and accumulated estimator error. -/
private lemma sumBaseStepSq_le_pathwise
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K)
    (ω : Ω) :
    ∑ k ∈ Finset.range K, ‖run.baseStep k ω‖ ^ 2 ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
  -- Sum the one-step descent inequality over all positive transition indices.
  have hdescent :
      (∑ k ∈ Finset.Ico 1 K,
          (params.beta / 4) * ‖run.baseStep k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.Ico 1 K,
          ((run.lyapunov k ω - run.lyapunov (k + 1) ω) +
            lyapunovErrorConstant h params *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Ico.mp hk
    have hstep := lyapunovDescent run h_admissible hkBounds.1 hkBounds.2 ω
    linarith
  have htelescope :
      (∑ k ∈ Finset.Ico 1 K,
          (run.lyapunov k ω - run.lyapunov (k + 1) ω)) =
        run.lyapunov 1 ω - run.lyapunov K ω := by
    have hendpointLeft : 1 + (K - 1) = K := by omega
    have hendpointRight : K - 1 + 1 = K := by omega
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov (k + 1) ω) (K - 1))
  -- Both adjacent error sums embed in the full prefix error sum.
  have hcurrentSubset : Finset.Ico 1 K ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 K, ‖run.gradientError k ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 K, ‖run.gradientError (k - 1) ω‖ ^ 2) =
        ∑ j ∈ Finset.range (K - 1), ‖run.gradientError j ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hindex : 1 + j - 1 = j := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (K - 1) ⊆ Finset.range K := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 K, ‖run.gradientError (k - 1) ω‖ ^ 2) ≤
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k ω‖)
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 K,
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2)) ≤
        2 * ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  -- Replace the terminal rank by its lower bound and normalize the coefficient.
  have hOne : 1 ≤ K := by omega
  have hzeroLt : 0 < K := by omega
  have hlower :=
    lyapunovLowerBound_le run h_admissible hOne (Nat.le_refl K) ω
  have herrorCoefficientNonneg : 0 ≤ lyapunovErrorConstant h params := by
    rw [lyapunovErrorConstant_def, LALM.multiplierErrorConstant_def]
    positivity
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  have henergy :
      (params.beta / 4) *
          (∑ k ∈ Finset.Ico 1 K, ‖run.baseStep k ω‖ ^ 2) ≤
        run.lyapunov 1 ω - lyapunovLowerBound h params +
          2 * lyapunovErrorConstant h params *
            ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    nlinarith
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hscalingNonneg : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  have hsumIco :
      (∑ k ∈ Finset.Ico 1 K, ‖run.baseStep k ω‖ ^ 2) ≤
        4 * (run.lyapunov 1 ω - lyapunovLowerBound h params) / params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by
    calc
      (∑ k ∈ Finset.Ico 1 K, ‖run.baseStep k ω‖ ^ 2) =
          (4 / params.beta) *
            ((params.beta / 4) *
              ∑ k ∈ Finset.Ico 1 K, ‖run.baseStep k ω‖ ^ 2) := by
        field_simp [hbeta.ne']
      _ ≤ (4 / params.beta) *
          (run.lyapunov 1 ω - lyapunovLowerBound h params +
            2 * lyapunovErrorConstant h params *
              ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hscalingNonneg
      _ = 4 * (run.lyapunov 1 ω - lyapunovLowerBound h params) /
            params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 := by ring
  have hupper := lyapunovOne_le_initialPotentialBound run hOne h_admissible ω
  have hgap := sub_le_sub_right hupper (lyapunovLowerBound h params)
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hscalingNonneg
  have hgapScaledNormalized :
      4 * (run.lyapunov 1 ω - lyapunovLowerBound h params) / params.beta ≤
        4 * (initialPotentialBound h params - lyapunovLowerBound h params) /
          params.beta := by
    calc
      4 * (run.lyapunov 1 ω - lyapunovLowerBound h params) / params.beta =
          (4 / params.beta) *
            (run.lyapunov 1 ω - lyapunovLowerBound h params) := by ring
      _ ≤ (4 / params.beta) *
          (initialPotentialBound h params - lyapunovLowerBound h params) :=
        hgapScaled
      _ = 4 * (initialPotentialBound h params - lyapunovLowerBound h params) /
          params.beta := by ring
  -- Restore index zero and absorb its radius bound into `initialStepBound`.
  have hnormBounds := run.admissiblePrefix_normBounds K h_admissible
  have hstepZero := hnormBounds.1 0 hzeroLt ω
  have hstepZeroSq :
      ‖run.baseStep 0 ω‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg _)).2 hstepZero
  have hdecomposition :
      (∑ k ∈ Finset.range K, ‖run.baseStep k ω‖ ^ 2) =
        ‖run.baseStep 0 ω‖ ^ 2 +
          ∑ k ∈ Finset.Ico 1 K, ‖run.baseStep k ω‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hOne]
    simp
  rw [hdecomposition, initialStepBound_def, errorStepConstant_def]
  linarith

/-- Helper for Corollary 4.2: integrating the corrected pathwise telescope
bounds accumulated base-step mean square by accumulated estimator error. -/
private lemma accumulatedBaseStepMeanSquare_le
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K) :
    ∑ k ∈ Finset.range K, run.baseStepMeanSquare k ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
  -- Integrate both finite sums using the owner-side moment integrability API.
  have hstepIntegrable (k : ℕ) (hk : k ∈ Finset.range K) :
      Integrable (fun ω ↦ ‖run.baseStep k ω‖ ^ 2) ℙ :=
    run.integrable_baseStepSquare h_admissible (Finset.mem_range.mp hk)
  have hstepsIntegrable :
      Integrable (fun ω ↦
        ∑ k ∈ Finset.range K, ‖run.baseStep k ω‖ ^ 2) ℙ :=
    integrable_finsetSum (Finset.range K) hstepIntegrable
  have herrorIntegrable (k : ℕ) (hk : k ∈ Finset.range K) :
      Integrable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) ℙ :=
    run.integrable_gradientErrorSquare h_admissible (Finset.mem_range.mp hk)
  have herrorsIntegrable :
      Integrable (fun ω ↦
        ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2) ℙ :=
    integrable_finsetSum (Finset.range K) herrorIntegrable
  have hrightIntegrable :
      Integrable (fun ω ↦ initialStepBound h params +
        errorStepConstant h params *
          ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2) ℙ :=
    (integrable_const _).add
      (herrorsIntegrable.const_mul (errorStepConstant h params))
  have hintegral := integral_mono hstepsIntegrable hrightIntegrable
    (sumBaseStepSq_le_pathwise run K hK h_admissible)
  have hstepIntegral :
      (∫ ω, ∑ k ∈ Finset.range K, ‖run.baseStep k ω‖ ^ 2 ∂ℙ) =
        ∑ k ∈ Finset.range K, run.baseStepMeanSquare k := by
    rw [integral_finsetSum (Finset.range K) hstepIntegrable]
    apply Finset.sum_congr rfl
    intro k hk
    rw [run.baseStepMeanSquare_def]
  have herrorIntegral :
      (∫ ω, ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
        ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
    rw [integral_finsetSum (Finset.range K) herrorIntegrable]
    apply Finset.sum_congr rfl
    intro k hk
    rw [run.gradientErrorMeanSquare_def]
  have hrightIntegral :
      (∫ ω, initialStepBound h params + errorStepConstant h params *
          ∑ k ∈ Finset.range K, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
        initialStepBound h params + errorStepConstant h params *
          ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
    rw [integral_add (integrable_const _)
      (herrorsIntegrable.const_mul (errorStepConstant h params)),
      integral_const, integral_const_mul, herrorIntegral]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hstepIntegral, hrightIntegral] at hintegral
  exact hintegral

/-- Helper for Corollary 4.2: the corrected initial base-step allowance is
nonnegative on every admissible prefix of length at least two. -/
private lemma initialStepBound_nonneg
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K) :
    0 ≤ initialStepBound h params := by
  -- Compare the first Lyapunov value with its uniform lower and upper bounds.
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure ℙ
  have hOne : 1 ≤ K := by omega
  have hlower :=
    lyapunovLowerBound_le run h_admissible (Nat.le_refl 1) hOne ω
  have hupper := lyapunovOne_le_initialPotentialBound run hOne h_admissible ω
  have hgap :
      0 ≤ initialPotentialBound h params - lyapunovLowerBound h params := by
    linarith
  rw [initialStepBound_def]
  positivity

/-- Helper for Corollary 4.2: among the first `K` indices, at most `q` are
divisible by `q` when `K ≤ q ^ 2`. -/
private lemma refreshIndexCard_le
    (K q : ℕ) (hq : 0 < q) (hKq : K ≤ q * q) :
    ((Finset.range K).filter (fun k ↦ k % q = 0)).card ≤ q := by
  -- Division by `q` injects the refresh indices into `Finset.range q`.
  have hcard :
      ((Finset.range K).filter (fun k ↦ k % q = 0)).card ≤
        (Finset.range q).card := by
    apply Finset.card_le_card_of_injOn (fun k ↦ k / q)
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul hq]
      exact lt_of_lt_of_le (Finset.mem_range.mp hk'.1) hKq
    · intro x hx y hy hxy
      change x / q = y / q at hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have hxrepr := Nat.div_add_mod x q
      have hyrepr := Nat.div_add_mod y q
      calc
        x = q * (x / q) + x % q := hxrepr.symm
        _ = q * (x / q) := by rw [hx'.2, Nat.add_zero]
        _ = q * (y / q) := by rw [hxy]
        _ = q * (y / q) + y % q := by rw [hy'.2, Nat.add_zero]
        _ = y := hyrepr
  simpa only [Finset.card_range] using hcard

/-- Helper for Corollary 4.2: the scheduled refresh period squared covers the
iteration horizon. -/
private lemma iteration_le_refreshPeriod_sq (K : ℕ) (hK : 2 ≤ K) :
    K ≤ (SPIDER.refreshPeriod K : ℕ) * (SPIDER.refreshPeriod K : ℕ) := by
  -- The ceiling of `sqrt K` has square at least `K`.
  have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
  have hsqrtSquare := Real.sq_sqrt (Nat.cast_nonneg K)
  have hsqrtCeil := Nat.le_ceil (Real.sqrt K)
  have hceilNonneg :
      (0 : ℝ) ≤ (Nat.ceil (Real.sqrt K) : ℝ) := Nat.cast_nonneg _
  have hreal :
      (K : ℝ) ≤ (Nat.ceil (Real.sqrt K) : ℝ) * Nat.ceil (Real.sqrt K) := by
    nlinarith
  rw [SPIDER.refreshPeriod_coe K hK]
  exact_mod_cast hreal

/-- Helper for Corollary 4.2: the scheduled refresh period is at most one plus
the square root of the horizon. -/
private lemma refreshPeriod_le_sqrt_add_one (K : ℕ) (hK : 2 ≤ K) :
    ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := by
  -- Apply the strict upper bound for a natural ceiling.
  rw [SPIDER.refreshPeriod_coe K hK]
  exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg (K : ℝ))).le

/-- Helper for Corollary 4.2: any corrected batch coefficient absorbed by one
half yields the standard average estimator-error bound. -/
private lemma averageGradientErrorMeanSquare_le_of_batchCoefficient
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K)
    (h_batch :
      errorStepConstant h params *
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) ≤
        (1 : ℝ) / 2) :
    (∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K ≤
      2 * oracle.noiseLevel ^ 2 / B +
        initialStepBound h params / (errorStepConstant h params * K) := by
  -- Couple estimator recursion to the accumulated base-step energy estimate.
  have hspider := run.accumulatedGradientErrorMeanSquare_le K h_admissible
  have hsteps := accumulatedBaseStepMeanSquare_le run K hK h_admissible
  have hDpos := errorStepConstant_pos h params
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hD0nonneg := initialStepBound_nonneg run K hK h_admissible
  have herrorSumNonneg :
      0 ≤ ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k :=
    Finset.sum_nonneg fun k _ ↦ gradientErrorMeanSquare_nonneg run k
  have hcoefficientNonneg :
      0 ≤ (Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
        displacementFactor h params.delta ^ 2 / (b : ℝ) := by
    positivity
  have hstepsScaled :=
    mul_le_mul_of_nonneg_left hsteps hcoefficientNonneg
  have hspiderCombined :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        K * oracle.noiseLevel ^ 2 / B +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            (initialStepBound h params + errorStepConstant h params *
              ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) := by
    exact hspider.trans (add_le_add (le_refl _) hstepsScaled)
  have habsorbCommuted :
      ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          errorStepConstant h params ≤ (1 : ℝ) / 2 := by
    simpa only [mul_comm] using h_batch
  have habsorbError :=
    mul_le_mul_of_nonneg_right habsorbCommuted herrorSumNonneg
  have hcoefficientLe :
      (Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 / (b : ℝ) ≤
        ((1 : ℝ) / 2) / errorStepConstant h params :=
    (le_div_iff₀ hDpos).2 habsorbCommuted
  have hinitialContribution :=
    mul_le_mul_of_nonneg_right hcoefficientLe hD0nonneg
  -- Expand once, absorb half the error sum, and solve the scalar inequality.
  have hspiderExpanded :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        K * oracle.noiseLevel ^ 2 / B +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            initialStepBound h params +
          (((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
              displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            errorStepConstant h params) *
              ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by
    calc
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
          K * oracle.noiseLevel ^ 2 / B +
            ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
              displacementFactor h params.delta ^ 2 / (b : ℝ)) *
              (initialStepBound h params + errorStepConstant h params *
                ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) :=
        hspiderCombined
      _ = K * oracle.noiseLevel ^ 2 / B +
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            initialStepBound h params +
          (((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
              displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            errorStepConstant h params) *
              ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k := by ring
  have hinitialNormalized :
      ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          initialStepBound h params ≤
        initialStepBound h params / (2 * errorStepConstant h params) := by
    calc
      ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
          displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          initialStepBound h params ≤
          ((1 : ℝ) / 2) / errorStepConstant h params *
            initialStepBound h params := hinitialContribution
      _ = initialStepBound h params /
          (2 * errorStepConstant h params) := by
        field_simp [hDzero]
  have hboundExpanded :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        K * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) *
            ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k :=
    hspiderExpanded.trans
      (add_le_add
        (add_le_add (le_refl _) hinitialNormalized) habsorbError)
  have hpretotal :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        2 * (K * oracle.noiseLevel ^ 2 / B) +
          2 * (initialStepBound h params /
            (2 * errorStepConstant h params)) := by
    linarith
  have htotal :
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        2 * (K * oracle.noiseLevel ^ 2 / B) +
          initialStepBound h params / errorStepConstant h params := by
    calc
      ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
          2 * (K * oracle.noiseLevel ^ 2 / B) +
            2 * (initialStepBound h params /
              (2 * errorStepConstant h params)) := hpretotal
      _ = 2 * (K * oracle.noiseLevel ^ 2 / B) +
          initialStepBound h params / errorStepConstant h params := by
        field_simp [hDzero]
  have hKreal : 0 < (K : ℝ) := by positivity
  apply (div_le_iff₀ hKreal).2
  calc
    ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k ≤
        2 * (K * oracle.noiseLevel ^ 2 / B) +
          initialStepBound h params / errorStepConstant h params := htotal
    _ = (2 * oracle.noiseLevel ^ 2 / B +
        initialStepBound h params / (errorStepConstant h params * K)) * K := by
      field_simp [hDzero]

/-- Helper for Corollary 4.2: an absorbed corrected batch coefficient also
yields the standard average base-step bound. -/
private lemma averageBaseStepMeanSquare_le_of_batchCoefficient
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K) (h_admissible : run.IsAdmissiblePrefix K)
    (h_batch :
      errorStepConstant h params *
          ((Q : ℝ) * oracle.meanSquareLipschitz ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) ≤
        (1 : ℝ) / 2) :
    (∑ k ∈ Finset.range K, run.baseStepMeanSquare k) / K ≤
      2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
        2 * initialStepBound h params / K := by
  -- Divide accumulated energy by the horizon and insert the error average.
  have hsteps := accumulatedBaseStepMeanSquare_le run K hK h_admissible
  have herrors := averageGradientErrorMeanSquare_le_of_batchCoefficient
    run K hK h_admissible h_batch
  have hDpos := errorStepConstant_pos h params
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have hstepsDivided := (div_le_div_iff_of_pos_right hKreal).2 hsteps
  have hstepsNormalized :
      (∑ k ∈ Finset.range K, run.baseStepMeanSquare k) / K ≤
        initialStepBound h params / K + errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) := by
    calc
      (∑ k ∈ Finset.range K, run.baseStepMeanSquare k) / K ≤
          (initialStepBound h params + errorStepConstant h params *
            ∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K :=
        hstepsDivided
      _ = initialStepBound h params / K + errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) := by
        ring
  have herrorsScaledRaw := mul_le_mul_of_nonneg_left herrors hDpos.le
  have herrorsScaled :
      errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) ≤
        2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / K := by
    calc
      errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) ≤
          errorStepConstant h params *
            (2 * oracle.noiseLevel ^ 2 / B +
              initialStepBound h params /
                (errorStepConstant h params * K)) := herrorsScaledRaw
      _ = 2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / K := by
        field_simp [hDzero, hKzero]
  calc
    (∑ k ∈ Finset.range K, run.baseStepMeanSquare k) / K ≤
        initialStepBound h params / K + errorStepConstant h params *
          ((∑ k ∈ Finset.range K, run.gradientErrorMeanSquare k) / K) :=
      hstepsNormalized
    _ ≤ initialStepBound h params / K +
        (2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
          initialStepBound h params / K) :=
      add_le_add (le_refl _) herrorsScaled
    _ = 2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / B +
        2 * initialStepBound h params / K := by ring

/-- Helper for Corollary 4.2: stochastic model optimality rewrites corrected
next-iterate stationarity as a deterministic comparison core minus estimator error. -/
private lemma stochasticStationarityIdentity
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    KKT.stationarity f c (run.point (k + 1) ω)
        (run.multiplier (k + 1) ω) =
      ((-(params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)) - run.gradientError k ω := by
  -- Normalize model optimality and the corrected multiplier update exactly once.
  have hminimizes :
      IsMinOn (LALM.stepModelWithGradient c
        (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
        params.rho params.beta (run.point k ω) (run.multiplier k ω))
        Set.univ (run.baseStep k ω) :=
    run.minimizes_baseStep k ω
  have hperturbedRaw :
      SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω +
        EqualityConstrained.constraintGradient c
          (run.point k ω) (nextMultiplier c params.rho (run.point k ω)
            (run.multiplier k ω) (run.baseStep k ω)) +
          (params.beta : ℝ) • run.baseStep k ω =
        (params.rho : ℝ) • EqualityConstrained.constraintGradient c
          (run.point k ω) (error c (run.point k ω) (run.baseStep k ω)) :=
    perturbedMultiplierIdentityWithGradient
      (SPIDER.estimate h.gradientBound oracle run.point run.sample Q B b k ω)
      params.rho params.beta
      (run.point k ω) (run.multiplier k ω) (run.baseStep k ω) hminimizes
  have hperturbed :
      run.gradientEstimate k ω + EqualityConstrained.constraintGradient c
          (run.point k ω) (nextMultiplier c params.rho (run.point k ω)
            (run.multiplier k ω) (run.baseStep k ω)) +
          (params.beta : ℝ) • run.baseStep k ω =
        (params.rho : ℝ) • EqualityConstrained.constraintGradient c
          (run.point k ω) (error c (run.point k ω) (run.baseStep k ω)) := by
    rw [run.gradientEstimate_apply]
    exact hperturbedRaw
  rw [← run.multiplier_succ k ω] at hperturbed
  rw [KKT.stationarity_def, run.gradientError_apply]
  simp only [sub_apply]
  linear_combination (norm := module) hperturbed

/-- Helper for Corollary 4.2: corrected stochastic stationarity at the next
iterate is controlled by the current base step and estimator error. -/
private lemma normStationaritySucc_le
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} {ω : Ω} (bounds : run.BoundedAdmissiblePath N ω)
    (hk : k < N) :
    ‖KKT.stationarity f c (run.point (k + 1) ω)
        (run.multiplier (k + 1) ω)‖ ≤
      primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep k ω‖ +
        ‖run.gradientError k ω‖ := by
  -- Extract the corrected transition and endpoint bounds from the fixed path.
  have hadm := bounds.admissible k hk
  have hxCurrent :=
    base_mem_region h (run.point k ω) (run.baseStep k ω) hadm
  have hxNext := nextPoint_mem_region h (run.point k ω) (run.baseStep k ω) hadm
  rw [← run.point_succ k ω] at hxNext
  have hstep := bounds.baseStep_le k hk
  have hmultiplierIndex : k + 1 ≤ N := by omega
  have hmultiplier := bounds.multiplier_le (k + 1) hmultiplierIndex
  have herror := normScaledConstraintGradientError_le_mul_norm h params
    (run.point k ω) (run.baseStep k ω) hadm hstep
  -- Model optimality supplies the normalized comparison identity.
  have hstationarityIdentity := stochasticStationarityIdentity run k ω
  -- Corrected displacement replaces the exact point-plus-step identity.
  have hpointDisplacement :
      ‖run.point (k + 1) ω - run.point k ω‖ ≤
        displacementFactor h params.delta * ‖run.baseStep k ω‖ := by
    have hdisplacement := displacement_le h params.delta (run.point k ω)
      (run.baseStep k ω) hadm hstep
    rw [← run.point_succ k ω] at hdisplacement
    exact hdisplacement
  have hgradientDifference :
      ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ ≤
        h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k ω‖ := by
    calc
      ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ =
          dist (gradient f (run.point (k + 1) ω))
            (gradient f (run.point k ω)) := (dist_eq_norm _ _).symm
      _ ≤ h.gradientLipschitz *
          dist (run.point (k + 1) ω) (run.point k ω) :=
        h.lipschitzOn_gradient.dist_le_mul
          (run.point (k + 1) ω) hxNext (run.point k ω) hxCurrent
      _ = h.gradientLipschitz *
          ‖run.point (k + 1) ω - run.point k ω‖ := by rw [dist_eq_norm]
      _ ≤ h.gradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep k ω‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.gradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k ω‖ := by ring
  have hoperatorDifference :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω)‖ ≤
        h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k ω‖ := by
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
      _ = h.constraintGradientLipschitz *
          ‖run.point (k + 1) ω - run.point k ω‖ := by rw [dist_eq_norm]
      _ ≤ h.constraintGradientLipschitz *
          (displacementFactor h params.delta * ‖run.baseStep k ω‖) :=
        mul_le_mul_of_nonneg_left hpointDisplacement (NNReal.coe_nonneg _)
      _ = h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k ω‖ := by ring
  have hdisplacementFactorNonneg :
      0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hoperatorApplied :
      ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
        h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep k ω‖ := by
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
      _ ≤ (h.constraintGradientLipschitz * displacementFactor h params.delta *
          ‖run.baseStep k ω‖) * params.multiplierBound :=
        mul_le_mul hoperatorDifference hmultiplier (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (NNReal.coe_nonneg _) hdisplacementFactorNonneg)
            (norm_nonneg _))
      _ = h.constraintGradientLipschitz * params.multiplierBound *
          displacementFactor h params.delta * ‖run.baseStep k ω‖ := by ring
  have hproximalError :
      ‖-(params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))‖ ≤
        primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep k ω‖ := by
    calc
      ‖-(params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))‖ ≤
          ‖-(params.beta : ℝ) • run.baseStep k ω‖ +
            ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))‖ :=
        norm_add_le _ _
      _ = params.beta * ‖run.baseStep k ω‖ +
          ‖(params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg,
          abs_of_pos params.spec.1.2.1]
      _ ≤ params.beta * ‖run.baseStep k ω‖ +
          params.rho * h.constraintGradientBound * errorFactor h params.delta *
            params.delta * ‖run.baseStep k ω‖ := add_le_add_right herror _
      _ = primalConstant h params.delta params.beta params.rho *
          ‖run.baseStep k ω‖ := by
        rw [primalConstant_def]
        ring
  -- Collect the deterministic comparison before adding the estimator error once.
  have hdeterministic :
      ‖(-(params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
        primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep k ω‖ := by
    calc
      ‖(-(params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)‖ ≤
          ‖-(params.beta : ℝ) • run.baseStep k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))‖ +
          ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖ +
          ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)‖ := by
        calc
          _ ≤ ‖(-(params.beta : ℝ) • run.baseStep k ω +
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))) +
              (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω))‖ +
              ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
                EqualityConstrained.constraintGradient c (run.point k ω))
                  (run.multiplier (k + 1) ω)‖ := norm_add_le _ _
          _ ≤ (‖-(params.beta : ℝ) • run.baseStep k ω +
                (params.rho : ℝ) • EqualityConstrained.constraintGradient c
                  (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))‖ +
              ‖gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)‖) +
              ‖(EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
                EqualityConstrained.constraintGradient c (run.point k ω))
                  (run.multiplier (k + 1) ω)‖ :=
            add_le_add (norm_add_le _ _) (le_refl _)
      _ ≤ primalConstant h params.delta params.beta params.rho *
            ‖run.baseStep k ω‖ +
          h.gradientLipschitz * displacementFactor h params.delta *
            ‖run.baseStep k ω‖ +
          h.constraintGradientLipschitz * params.multiplierBound *
            displacementFactor h params.delta * ‖run.baseStep k ω‖ :=
        add_le_add (add_le_add hproximalError hgradientDifference) hoperatorApplied
      _ = primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep k ω‖ := by
        rw [primalComparisonConstant_def]
        ring
  rw [hstationarityIdentity]
  calc
    ‖((-(params.beta : ℝ) • run.baseStep k ω +
          (params.rho : ℝ) • EqualityConstrained.constraintGradient c
            (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))) +
        (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
        (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
          EqualityConstrained.constraintGradient c (run.point k ω))
            (run.multiplier (k + 1) ω)) - run.gradientError k ω‖ ≤
        ‖(-(params.beta : ℝ) • run.baseStep k ω +
            (params.rho : ℝ) • EqualityConstrained.constraintGradient c
              (run.point k ω) (error c (run.point k ω) (run.baseStep k ω))) +
          (gradient f (run.point (k + 1) ω) - gradient f (run.point k ω)) +
          (EqualityConstrained.constraintGradient c (run.point (k + 1) ω) -
            EqualityConstrained.constraintGradient c (run.point k ω))
              (run.multiplier (k + 1) ω)‖ + ‖run.gradientError k ω‖ :=
      norm_sub_le _ _
    _ ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound * ‖run.baseStep k ω‖ +
          ‖run.gradientError k ω‖ :=
      add_le_add hdeterministic (le_refl _)

/-- Helper for Corollary 4.2: the corrected stochastic multiplier update
identifies squared feasibility with the scaled multiplier increment. -/
private lemma stochasticConstraintNormSq_eq_multiplierIncrementNormSqDiv
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    ‖c (run.point (k + 1) ω)‖ ^ 2 =
      ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 /
        (params.rho : ℝ) ^ 2 := by
  -- Normalize the corrected-point multiplier update and cancel its positive square.
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hupdate :
      run.multiplier (k + 1) ω = run.multiplier k ω +
        (params.rho : ℝ) • c (run.point (k + 1) ω) := by
    rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
  rw [hupdate, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hrho]
  field_simp [hrho.ne']

/-- Helper for Corollary 4.2: every positive corrected stochastic transition
has squared KKT residual controlled by adjacent base steps and estimator errors. -/
private lemma stochasticResidual_sq_le
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {N k : ℕ} {ω : Ω} (bounds : run.BoundedAdmissiblePath N ω)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 ≤
      stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
  -- Square stationarity and separate the current base step from estimator error.
  have hstationarity := normStationaritySucc_le run bounds hk
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [primalComparisonConstant_def, primalConstant_def,
      displacementFactor_def, stepConstant_def, errorFactor_def, errorConstant_def]
    positivity
  have hstationarityRightNonneg :
      0 ≤ primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound * ‖run.baseStep k ω‖ +
        ‖run.gradientError k ω‖ :=
    add_nonneg (mul_nonneg hcomparisonNonneg (norm_nonneg _)) (norm_nonneg _)
  have hstationaritySquared :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        (primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound * ‖run.baseStep k ω‖ +
          ‖run.gradientError k ω‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hstationarityRightNonneg).2 hstationarity
  have hstationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        2 * primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 * ‖run.baseStep k ω‖ ^ 2 +
          2 * ‖run.gradientError k ω‖ ^ 2 := by
    calc
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
          (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.baseStep k ω‖ +
            ‖run.gradientError k ω‖) ^ 2 := hstationaritySquared
      _ ≤ 2 *
          (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.baseStep k ω‖) ^ 2 +
            2 * ‖run.gradientError k ω‖ ^ 2 := by
        nlinarith [sq_nonneg
          (primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound * ‖run.baseStep k ω‖ -
            ‖run.gradientError k ω‖)]
      _ = 2 * primalComparisonConstant h params.delta params.beta params.rho
          params.multiplierBound ^ 2 * ‖run.baseStep k ω‖ ^ 2 +
        2 * ‖run.gradientError k ω‖ ^ 2 := by ring
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hstationarityExpanded :
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
        2 * primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 *
          (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
        2 * (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖KKT.stationarity f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω)‖ ^ 2 ≤
          2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 * ‖run.baseStep k ω‖ ^ 2 +
            2 * ‖run.gradientError k ω‖ ^ 2 := hstationaritySquare
      _ ≤ 2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 *
            (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
          2 * (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
        have hstepCoefficientNonneg :
            0 ≤ 2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 := mul_nonneg htwo (sq_nonneg _)
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) hstepCoefficientNonneg)
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (sq_nonneg _)) htwo)
  -- Transport the multiplier-increment estimate to feasibility.
  have hmultiplier := bounds.norm_multiplier_succ_sub_sq_le hk_pos hk
  have hfeasibility :
      ‖c (run.point (k + 1) ω)‖ ^ 2 ≤
        multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 *
          (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
        LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
    calc
      ‖c (run.point (k + 1) ω)‖ ^ 2 =
          ‖run.multiplier (k + 1) ω - run.multiplier k ω‖ ^ 2 /
            (params.rho : ℝ) ^ 2 :=
        stochasticConstraintNormSq_eq_multiplierIncrementNormSqDiv run k ω
      _ ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
            (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
          LALM.multiplierErrorConstant h *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2)) /
            (params.rho : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmultiplier (sq_nonneg _)
      _ = multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2 *
            (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
          LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
  -- Each grouped coefficient is below the corresponding branch of the maximum.
  have hprimalCoefficient :
      2 * primalComparisonConstant h params.delta params.beta params.rho
            params.multiplierBound ^ 2 +
          multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / (params.rho : ℝ) ^ 2 ≤
        stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound := by
    rw [stochasticResidualConstant_def]
    exact le_max_left _ _
  have herrorCoefficient :
      2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 ≤
        stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound := by
    rw [stochasticResidualConstant_def]
    exact le_max_right _ _
  have hstepSumNonneg :
      0 ≤ ‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have herrorSumNonneg :
      0 ≤ ‖run.gradientError k ω‖ ^ 2 +
        ‖run.gradientError (k - 1) ω‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    KKT.residual f c (run.point (k + 1) ω) (run.multiplier (k + 1) ω) ^ 2 =
        ‖KKT.stationarity f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω)‖ ^ 2 +
          ‖c (run.point (k + 1) ω)‖ ^ 2 := by
      rw [KKT.residual_def,
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ (2 * primalComparisonConstant h params.delta params.beta params.rho
              params.multiplierBound ^ 2 +
            multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / (params.rho : ℝ) ^ 2) *
          (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
        (2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
          (‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by
      calc
        ‖KKT.stationarity f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω)‖ ^ 2 +
            ‖c (run.point (k + 1) ω)‖ ^ 2 ≤
            (2 * primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2 *
              (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
            2 * (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2)) +
            (multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2 *
              (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
            LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 *
              (‖run.gradientError k ω‖ ^ 2 +
                ‖run.gradientError (k - 1) ω‖ ^ 2)) :=
          add_le_add hstationarityExpanded hfeasibility
        _ = (2 * primalComparisonConstant h params.delta params.beta params.rho
                params.multiplierBound ^ 2 +
              multiplierPrimalConstant h params.delta params.beta params.rho
                params.multiplierBound / (params.rho : ℝ) ^ 2) *
            (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
          (2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2) *
            (‖run.gradientError k ω‖ ^ 2 +
              ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring
    _ ≤ stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2) +
      stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.gradientError k ω‖ ^ 2 +
          ‖run.gradientError (k - 1) ω‖ ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hprimalCoefficient hstepSumNonneg)
        (mul_le_mul_of_nonneg_right herrorCoefficient herrorSumNonneg)
    _ = stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2 +
          ‖run.gradientError k ω‖ ^ 2 +
            ‖run.gradientError (k - 1) ω‖ ^ 2) := by ring

/-- Helper for Corollary 4.2: the corrected stochastic residual comparison
constant is nonnegative under the positive algorithm parameters. -/
private lemma stochasticResidualConstant_nonneg
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    0 ≤ stochasticResidualConstant h params.delta params.beta params.rho
      params.multiplierBound := by
  -- The second branch of the defining maximum is visibly nonnegative.
  rw [stochasticResidualConstant_def]
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hsecond :
      0 ≤ 2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 := by
    positivity
  exact hsecond.trans (le_max_right _ _)

/-- Helper for Corollary 4.2: a fixed corrected stochastic residual mean square
is controlled by its two neighboring base-step and estimator-error moments. -/
private lemma fixedResidualMeanSquare_le
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {K k : ℕ} (h_admissible : run.IsAdmissiblePrefix K)
    (hk_pos : 1 ≤ k) (hk : k < K) :
    KKT.Stochastic.residualMeanSquare ℙ f c
        (run.point (k + 1)) (run.multiplier (k + 1)) ≤
      ENNReal.ofReal
        (stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run.baseStepMeanSquare k + run.baseStepMeanSquare (k - 1) +
            run.gradientErrorMeanSquare k +
              run.gradientErrorMeanSquare (k - 1))) := by
  let C := stochasticResidualConstant h params.delta params.beta params.rho
    params.multiplierBound
  let moments : Ω → ℝ := fun ω ↦
    ‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2 +
      ‖run.gradientError k ω‖ ^ 2 + ‖run.gradientError (k - 1) ω‖ ^ 2
  -- Package the four integrable moment components before applying monotonicity.
  have hstepK := run.integrable_baseStepSquare h_admissible hk
  have hkPrev : k - 1 < K := by omega
  have hstepPrev := run.integrable_baseStepSquare h_admissible hkPrev
  have herrorK := run.integrable_gradientErrorSquare h_admissible hk
  have herrorPrev := run.integrable_gradientErrorSquare h_admissible hkPrev
  have hmoments : Integrable moments ℙ :=
    ((hstepK.add hstepPrev).add herrorK).add herrorPrev
  have hright : Integrable (fun ω ↦ C * moments ω) ℙ :=
    hmoments.const_mul C
  have hC : 0 ≤ C := stochasticResidualConstant_nonneg h params
  have hmomentsNonneg (ω : Ω) : 0 ≤ moments ω := by
    dsimp only [moments]
    positivity
  have hrightNonneg : 0 ≤ᵐ[ℙ] fun ω ↦ C * moments ω :=
    ae_of_all ℙ fun ω ↦ mul_nonneg hC (hmomentsNonneg ω)
  have hpath (ω : Ω) : run.BoundedAdmissiblePath K ω := by
    -- Repackage the global admissible-prefix certificate at this sample path.
    constructor
    · intro j hj
      exact (run.isAdmissiblePrefix_iff K).1 h_admissible j hj ω
    · intro j hj
      exact (run.admissiblePrefix_normBounds K h_admissible).1 j hj ω
    · intro j hj
      exact (run.admissiblePrefix_normBounds K h_admissible).2 j hj ω
  -- Normalize the integral of the four-term moment sum through public definitions.
  have hmomentsIntegral :
      (∫ ω, moments ω ∂ℙ) =
        run.baseStepMeanSquare k + run.baseStepMeanSquare (k - 1) +
          run.gradientErrorMeanSquare k +
            run.gradientErrorMeanSquare (k - 1) := by
    have hfirst := integral_add hstepK hstepPrev
    have hsecond := integral_add (hstepK.add hstepPrev) herrorK
    have hthird := integral_add ((hstepK.add hstepPrev).add herrorK) herrorPrev
    have hsecond' :
        (∫ ω, ‖run.baseStep k ω‖ ^ 2 + ‖run.baseStep (k - 1) ω‖ ^ 2 +
            ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
          (∫ ω, ‖run.baseStep k ω‖ ^ 2 +
              ‖run.baseStep (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂ℙ := by
      simpa only [Pi.add_apply] using hsecond
    calc
      (∫ ω, moments ω ∂ℙ) =
          (∫ ω, ‖run.baseStep k ω‖ ^ 2 +
              ‖run.baseStep (k - 1) ω‖ ^ 2 +
              ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        simpa only [moments, Pi.add_apply] using hthird
      _ = ((∫ ω, ‖run.baseStep k ω‖ ^ 2 +
              ‖run.baseStep (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
          ∫ ω, ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        rw [hsecond']
      _ = (((∫ ω, ‖run.baseStep k ω‖ ^ 2 ∂ℙ) +
              ∫ ω, ‖run.baseStep (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
          ∫ ω, ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        rw [hfirst]
      _ = run.baseStepMeanSquare k + run.baseStepMeanSquare (k - 1) +
          run.gradientErrorMeanSquare k +
            run.gradientErrorMeanSquare (k - 1) := by
        rw [run.baseStepMeanSquare_def, run.baseStepMeanSquare_def,
          run.gradientErrorMeanSquare_def, run.gradientErrorMeanSquare_def]
  rw [KKT.Stochastic.residualMeanSquare_def]
  calc
    (∫⁻ ω, ENNReal.ofReal
        (KKT.residual f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω) ^ 2) ∂ℙ) ≤
        ∫⁻ ω, ENNReal.ofReal (C * moments ω) ∂ℙ := by
      refine lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal ?_
      exact stochasticResidual_sq_le run (hpath ω) hk_pos hk
    _ = ENNReal.ofReal (∫ ω, C * moments ω ∂ℙ) :=
      (ofReal_integral_eq_lintegral_ofReal hright hrightNonneg).symm
    _ = ENNReal.ofReal (C * ∫ ω, moments ω ∂ℙ) := by
      rw [integral_const_mul]
    _ = ENNReal.ofReal
        (stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run.baseStepMeanSquare k + run.baseStepMeanSquare (k - 1) +
            run.gradientErrorMeanSquare k +
              run.gradientErrorMeanSquare (k - 1))) := by
      rw [hmomentsIntegral]

/-- Helper for Corollary 4.2: adjacent pairs of any nonnegative moment sequence
are bounded by twice its full prefix sum. -/
private lemma sumAdjacentMoment_le_two_range
    (a : ℕ → ℝ) (K : ℕ) (hK : 2 ≤ K) (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1))) ≤
      2 * ∑ k ∈ Finset.range K, a k := by
  -- Shift the preceding-index sum and compare both pieces with the full range.
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
  have hrange :
      (∑ k ∈ Finset.range (K - 1), a k) ≤
        ∑ k ∈ Finset.range K, a k :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun k _ _ ↦ ha k)
  have hrangeSplit :
      (∑ k ∈ Finset.range K, a k) =
        a 0 + ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
    rw [hinterval, Finset.sum_range_eq_add_Ico a (by omega)]
  rw [Finset.sum_add_distrib, hshift]
  rw [hrangeSplit]
  linarith [ha 0]

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: stochastic residual mean square depends only on
the almost-everywhere classes of the point and multiplier maps. -/
private lemma residualMeanSquare_congr
    {x x' : Ω → EuclideanSpace ℝ (Fin n)}
    {multiplier multiplier' : Ω → EuclideanSpace ℝ (Fin m)}
    (hx : x =ᵐ[ℙ] x') (hmultiplier : multiplier =ᵐ[ℙ] multiplier') :
    KKT.Stochastic.residualMeanSquare ℙ f c x multiplier =
      KKT.Stochastic.residualMeanSquare ℙ f c x' multiplier' := by
  -- Rewrite the defining lintegrals and use pointwise AE equality of both inputs.
  rw [KKT.Stochastic.residualMeanSquare_def,
    KKT.Stochastic.residualMeanSquare_def]
  exact lintegral_congr_ae
    (hx.comp₂
      (fun point dual ↦ ENNReal.ofReal (KKT.residual f c point dual ^ 2))
      hmultiplier)

/-- Helper for Corollary 4.2: the corrected scheduled inner batch is bounded by
its real linear expression in the refresh period. -/
private lemma innerBatchSize_le_linear
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : Parameters h x₀ multiplier₀) (K : ℕ) :
    ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
      2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2 *
        displacementFactor h params.delta ^ 2 * (SPIDER.refreshPeriod K : ℕ) + 1 := by
  -- Bound both branches of the defining maximum by the ceiling expression plus one.
  let A : ℝ :=
    2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2 *
      displacementFactor h params.delta ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [errorStepConstant_pos h params]
  have hargument :
      0 ≤ A * (SPIDER.refreshPeriod K : ℕ) :=
    mul_nonneg hA (Nat.cast_nonneg _)
  have hceiling := Nat.ceil_lt_add_one hargument
  have honeLe :
      (1 : ℝ) ≤ A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
    linarith
  rw [SPIDER.Correction.innerBatchSize_coe, Nat.cast_max]
  apply max_le
  · simpa only [A, Nat.cast_one] using honeLe
  · dsimp only [A] at hceiling ⊢
    exact hceiling.le

/-- Helper for Corollary 4.2: the corrected scheduled gradient counter is
bounded by the refresh work plus all inner-update work. -/
private lemma gradientEvaluationCount_le_schedule
    (K : ℕ) (hK : 2 ≤ K)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K) :
    run.gradientEvaluationCount K ≤
      (SPIDER.refreshPeriod K : ℕ) * K +
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
  -- Count refresh indices and then bound every nonrefresh transition uniformly.
  have hq : 0 < (SPIDER.refreshPeriod K : ℕ) :=
    (SPIDER.refreshPeriod K).pos
  have hrefreshCard := refreshIndexCard_le K (SPIDER.refreshPeriod K)
    hq (iteration_le_refreshPeriod_sq K hK)
  calc
    run.gradientEvaluationCount K =
        ∑ k ∈ Finset.range K,
          if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
            (SPIDER.refreshBatchSize K : ℕ)
          else 2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) :=
      run.gradientEvaluationCount_spec K
    _ ≤ ∑ k ∈ Finset.range K,
        ((if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
            (SPIDER.refreshBatchSize K : ℕ) else 0) +
          2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) := by
      apply Finset.sum_le_sum
      intro k hk
      split
      · omega
      · omega
    _ = ((Finset.range K).filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card *
          (SPIDER.refreshBatchSize K : ℕ) +
        K * (2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range, Nat.cast_id]
    _ ≤ (SPIDER.refreshPeriod K : ℕ) * K +
        K * (2 * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ)) := by
      rw [SPIDER.refreshBatchSize_coe K hK]
      exact add_le_add (Nat.mul_le_mul_right K hrefreshCard) le_rfl
    _ = (SPIDER.refreshPeriod K : ℕ) * K +
        2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
      ring

/-- Helper for Corollary 4.2: every corrected successor point that can be
selected by the uniform output law lies in the regularity region almost surely. -/
def UniformOutput.HasRegularOutputPoints
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) : Prop :=
  ∀ᵐ ω ∂ℙ, ∀ k ∈ Finset.Icc 1 (K - 1), run.point (k + 1) ω ∈ h.region

/-- Helper for Corollary 4.2: almost-sure corrected prefix admissibility
supplies regularity-region support for the uniform output law. -/
theorem UniformOutput.hasRegularOutputPoints_of_isAEAdmissiblePrefix
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (h_admissible : run.IsAEAdmissiblePrefix K) :
    UniformOutput.HasRegularOutputPoints run K := by
  have hAdmissibleAE := (isAEAdmissiblePrefix_iff run K).mp h_admissible
  filter_upwards [hAdmissibleAE] with ω hω
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  have hkOne : 1 ≤ k := hkBounds.1
  have hkLe : k ≤ K - 1 := hkBounds.2
  have hKNe : K ≠ 0 := by
    intro hKZero
    subst K
    omega
  have hKPos : 0 < K := Nat.pos_of_ne_zero hKNe
  have hkLt : k < K :=
    (Nat.le_sub_one_iff_lt hKPos).mp hkLe
  have hadmissible :
      IsAdmissible h (run.point k ω) (run.baseStep k ω) :=
    (isAdmissible_iff h _ _).mpr (hω k hkLt)
  rw [run.point_succ]
  exact nextPoint_mem_region h (run.point k ω) (run.baseStep k ω) hadmissible

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: countably indexed almost-everywhere measurable
sections assemble measurably over a product measure. -/
private lemma aemeasurableIndexedProduct
    {E : Type*} [MeasurableSpace E] (μ : Measure ℕ)
    (g : ℕ → Ω → E) (hg : ∀ k, AEMeasurable (g k) ℙ) :
    AEMeasurable (fun output : ℕ × Ω ↦ g output.1 output.2) (μ.prod ℙ) := by
  -- Replace every section by a measurable representative.
  let g' : ℕ → Ω → E := fun k ↦ (hg k).mk (g k)
  have hg'Measurable (k : ℕ) : Measurable (g' k) :=
    (hg k).measurable_mk
  have hglobalMeasurable :
      Measurable (fun output : ℕ × Ω ↦ g' output.1 output.2) :=
    measurable_from_prod_countable_right hg'Measurable
  have hsections : ∀ᵐ ω ∂ℙ, ∀ k, g' k ω = g k ω := by
    apply ae_all_iff.mpr
    intro k
    exact (hg k).ae_eq_mk.symm
  -- Lift simultaneous section equality through the product projection.
  have hlifted :
      ∀ᵐ output ∂μ.prod ℙ, ∀ k, g' k output.2 = g k output.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ℙ)).ae hsections
  have hglobalAE :
      (fun output : ℕ × Ω ↦ g' output.1 output.2) =ᵐ[μ.prod ℙ]
        fun output ↦ g output.1 output.2 := by
    filter_upwards [hlifted] with output houtput
    exact houtput output.1
  exact hglobalMeasurable.aemeasurable.congr hglobalAE

/-- Helper for Corollary 4.2: the corrected product-law residual mean square is
the uniform finite average of the fixed-index corrected residual mean squares. -/
theorem UniformOutput.residualMeanSquare_eq_expect
    {Q B b : ℕ+}
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    (K : ℕ) (hK : 2 ≤ K)
    (h_support : UniformOutput.HasRegularOutputPoints run K) :
    KKT.Stochastic.residualMeanSquare
        (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
        (UniformOutput.point run) (UniformOutput.multiplier run) =
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run.point (k + 1)) (run.multiplier (k + 1))) /
        (Finset.Icc 1 (K - 1)).card := by
  -- Name the finite index law and the residual sections used by Tonelli.
  let s := Finset.Icc 1 (K - 1)
  let p := LALM.StochasticRun.UniformOutput.indexLaw K hK
  let residualSquare : ℕ → Ω → ℝ≥0∞ := fun k ω ↦
    ENNReal.ofReal
      (KKT.residualExtension h
        (run.point (k + 1) ω, run.multiplier (k + 1) ω) ^ 2)
  have hResidualSquare (k : ℕ) : AEMeasurable (residualSquare k) ℙ := by
    have hpair :
        AEMeasurable
          (fun ω ↦ (run.point (k + 1) ω, run.multiplier (k + 1) ω)) ℙ :=
      (run.aemeasurable_point (k + 1)).prodMk
        (run.aemeasurable_multiplier (k + 1))
    have hresidual :=
      (KKT.measurable_residualExtension h).comp_aemeasurable hpair
    exact hresidual.pow_const 2 |>.ennreal_ofReal
  have hglobal :
      AEMeasurable
        (fun output : ℕ × Ω ↦ residualSquare output.1 output.2)
        (p.toMeasure.prod ℙ) :=
    aemeasurableIndexedProduct p.toMeasure residualSquare hResidualSquare
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ s := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hk' : k ∉ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hpZero : p k = 0 := by
      simp only [p, LALM.StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk']
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod ℙ, output.1 ∈ s :=
    (Measure.quasiMeasurePreserving_fst (μ := p.toMeasure) (ν := ℙ)).ae hpSupport
  have hrunSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod ℙ,
        ∀ k ∈ Finset.Icc 1 (K - 1),
          run.point (k + 1) output.2 ∈ h.region :=
    (Measure.quasiMeasurePreserving_snd (μ := p.toMeasure) (ν := ℙ)).ae h_support
  have hresidualEq :
      (fun output : ℕ × Ω ↦ ENNReal.ofReal
        (KKT.residual f c (run.point (output.1 + 1) output.2)
          (run.multiplier (output.1 + 1) output.2) ^ 2)) =ᵐ[p.toMeasure.prod ℙ]
        fun output ↦ residualSquare output.1 output.2 := by
    filter_upwards [hpSupportLifted, hrunSupportLifted] with output hk houtput
    have hk' : output.1 ∈ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hextension :
        KKT.residualExtension h
            (run.point (output.1 + 1) output.2,
              run.multiplier (output.1 + 1) output.2) =
          KKT.residual f c (run.point (output.1 + 1) output.2)
            (run.multiplier (output.1 + 1) output.2) :=
      KKT.residualExtension_eq h (houtput output.1 hk')
    simp only [residualSquare, hextension]
  have hpoint : UniformOutput.point run =
      fun output : ℕ × Ω ↦ run.point (output.1 + 1) output.2 := by
    funext output
    exact UniformOutput.point_apply run output
  have hmultiplier : UniformOutput.multiplier run =
      fun output : ℕ × Ω ↦ run.multiplier (output.1 + 1) output.2 := by
    funext output
    exact UniformOutput.multiplier_apply run output
  -- Expand the product integral and use the finite support of the uniform law.
  rw [hpoint, hmultiplier, LALM.StochasticRun.UniformOutput.measure,
    KKT.Stochastic.residualMeanSquare_def]
  change (∫⁻ output : ℕ × Ω,
    ENNReal.ofReal
      (KKT.residual f c (run.point (output.1 + 1) output.2)
        (run.multiplier (output.1 + 1) output.2) ^ 2)
      ∂p.toMeasure.prod ℙ) = _
  rw [lintegral_congr_ae hresidualEq]
  change (∫⁻ output : ℕ × Ω,
    residualSquare output.1 output.2 ∂p.toMeasure.prod ℙ) = _
  rw [lintegral_prod _ hglobal, lintegral_countable']
  simp_rw [PMF.toMeasure_apply_singleton p _ (MeasurableSet.singleton _)]
  have hp (k : ℕ) :
      p k = if k ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
    change (PMF.uniformOfFinset s _) k = _
    by_cases hk : k ∈ s
    · simp only [PMF.uniformOfFinset_apply, if_pos hk]
    · simp only [PMF.uniformOfFinset_apply, if_neg hk]
  have hsectionEq (k : ℕ) (hk : k ∈ s) :
      (∫⁻ ω, residualSquare k ω ∂ℙ) =
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run.point (k + 1)) (run.multiplier (k + 1)) := by
    have hk' : k ∈ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    rw [KKT.Stochastic.residualMeanSquare_def]
    apply lintegral_congr_ae
    filter_upwards [h_support] with ω hω
    have hextension :
        KKT.residualExtension h
            (run.point (k + 1) ω, run.multiplier (k + 1) ω) =
          KKT.residual f c (run.point (k + 1) ω)
            (run.multiplier (k + 1) ω) :=
      KKT.residualExtension_eq h (hω k hk')
    simp only [residualSquare, hextension]
  have hsumResidual :
      (∑ k ∈ s, ∫⁻ ω, residualSquare k ω ∂ℙ) =
        ∑ k ∈ s, KKT.Stochastic.residualMeanSquare ℙ f c
          (run.point (k + 1)) (run.multiplier (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hsectionEq k hk
  simp_rw [hp]
  rw [tsum_eq_sum (s := s)]
  · have hsum :
        (∑ k ∈ s, (∫⁻ ω, residualSquare k ω ∂ℙ) *
          (if k ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0)) =
          ∑ k ∈ s,
            (∫⁻ ω, residualSquare k ω ∂ℙ) *
              (s.card : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos hk]
    rw [hsum, ← Finset.sum_mul, hsumResidual]
    simp only [ENNReal.div_eq_inv_mul, mul_comm]
    dsimp only [s]
  · intro k hk
    rw [if_neg hk, mul_zero]

/-- Helper for Corollary 4.2: the corrected point selected at an independent
uniform successor index is almost-everywhere measurable. -/
theorem UniformOutput.aemeasurable_point
    (K : ℕ) (hK : 2 ≤ K)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K) :
    AEMeasurable (UniformOutput.point run)
      (LALM.StochasticRun.UniformOutput.measure K hK ℙ) := by
  -- Rewrite the opaque corrected selector through its owner computation theorem.
  have hpoint : UniformOutput.point run =
      fun output : ℕ × Ω ↦ run.point (output.1 + 1) output.2 := by
    funext output
    exact UniformOutput.point_apply run output
  rw [hpoint, LALM.StochasticRun.UniformOutput.measure]
  -- Assemble the countable family of measurable point sections on the product.
  exact aemeasurableIndexedProduct
    (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure
    (fun k ↦ run.point (k + 1))
    (fun k ↦ run.aemeasurable_point (k + 1))

/-- Helper for Corollary 4.2: the corrected multiplier selected at an
independent uniform successor index is almost-everywhere measurable. -/
theorem UniformOutput.aemeasurable_multiplier
    (K : ℕ) (hK : 2 ≤ K)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K) :
    AEMeasurable (UniformOutput.multiplier run)
      (LALM.StochasticRun.UniformOutput.measure K hK ℙ) := by
  -- Rewrite the opaque corrected selector through its owner computation theorem.
  have hmultiplier : UniformOutput.multiplier run =
      fun output : ℕ × Ω ↦ run.multiplier (output.1 + 1) output.2 := by
    funext output
    exact UniformOutput.multiplier_apply run output
  rw [hmultiplier, LALM.StochasticRun.UniformOutput.measure]
  -- Assemble the countable family of measurable multiplier sections on the product.
  exact aemeasurableIndexedProduct
    (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure
    (fun k ↦ run.multiplier (k + 1))
    (fun k ↦ run.aemeasurable_multiplier (k + 1))

/-- Helper for Corollary 4.2: with the corrected SPIDER schedule and an
almost-surely admissible prefix, the uniform output satisfies the corrected
inverse-iteration residual rate. -/
theorem UniformOutput.residualMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_admissible : run.IsAEAdmissiblePrefix K) :
    KKT.Stochastic.residualMeanSquare
        (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
        (UniformOutput.point run) (UniformOutput.multiplier run) ≤
      ENNReal.ofReal
        (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) := by
  -- Replace the almost-surely admissible run by a pathwise admissible version.
  obtain ⟨run', hrun'Admissible, hpointAE, hmultiplierAE, _, _⟩ :=
    h_admissible.exists_pathwiseVersion run K
  have hrunSupport :=
    UniformOutput.hasRegularOutputPoints_of_isAEAdmissiblePrefix
      run K h_admissible
  have hrun'Support :=
    UniformOutput.hasRegularOutputPoints_of_isAEAdmissiblePrefix
      run' K hrun'Admissible.isAE
  have hbatch := SPIDER.Correction.scheduledErrorStepCoefficient_le_half
    h oracle params K
  have herrorAverage :=
    averageGradientErrorMeanSquare_le_of_batchCoefficient
      run' K hK hrun'Admissible hbatch
  have hstepAverage :=
    averageBaseStepMeanSquare_le_of_batchCoefficient
      run' K hK hrun'Admissible hbatch
  rw [SPIDER.refreshBatchSize_coe K hK] at herrorAverage hstepAverage
  -- Remove the common horizon denominator from both averaged moment bounds.
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have herrorTotalRaw := (div_le_iff₀ hKreal).mp herrorAverage
  have hstepTotalRaw := (div_le_iff₀ hKreal).mp hstepAverage
  have herrorTotal :
      (∑ k ∈ Finset.range K, run'.gradientErrorMeanSquare k) ≤
        errorAverageConstant h oracle params := by
    calc
      (∑ k ∈ Finset.range K, run'.gradientErrorMeanSquare k) ≤
          (2 * oracle.noiseLevel ^ 2 / K +
            initialStepBound h params / (errorStepConstant h params * K)) * K :=
        herrorTotalRaw
      _ = errorAverageConstant h oracle params := by
        rw [errorAverageConstant_def]
        field_simp [hKzero]
  have hstepTotal :
      (∑ k ∈ Finset.range K, run'.baseStepMeanSquare k) ≤
        stepAverageConstant h oracle params := by
    calc
      (∑ k ∈ Finset.range K, run'.baseStepMeanSquare k) ≤
          (2 * errorStepConstant h params * oracle.noiseLevel ^ 2 / K +
            2 * initialStepBound h params / K) * K := hstepTotalRaw
      _ = stepAverageConstant h oracle params := by
        rw [stepAverageConstant_def]
        field_simp [hKzero]
  -- Combine base-step and gradient-error moments into one nonnegative sequence.
  let a : ℕ → ℝ := fun k ↦
    run'.baseStepMeanSquare k + run'.gradientErrorMeanSquare k
  have ha (k : ℕ) : 0 ≤ a k := by
    exact add_nonneg (baseStepMeanSquare_nonneg run' k)
      (gradientErrorMeanSquare_nonneg run' k)
  have htotalRange :
      (∑ k ∈ Finset.range K, a k) ≤
        stepAverageConstant h oracle params + errorAverageConstant h oracle params := by
    rw [Finset.sum_add_distrib]
    exact add_le_add hstepTotal herrorTotal
  have hadjacent := sumAdjacentMoment_le_two_range a K hK ha
  have hC := stochasticResidualConstant_nonneg h params
  -- Sum the fixed-index real residual majorants over adjacent moment pairs.
  have hrealSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run'.baseStepMeanSquare k + run'.baseStepMeanSquare (k - 1) +
            run'.gradientErrorMeanSquare k +
              run'.gradientErrorMeanSquare (k - 1))) ≤
        stochasticComplexityConstant h oracle params := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
        stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run'.baseStepMeanSquare k + run'.baseStepMeanSquare (k - 1) +
            run'.gradientErrorMeanSquare k +
              run'.gradientErrorMeanSquare (k - 1))) =
          stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
            ∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp only [a]
        ring
      _ ≤ stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
            (2 * ∑ k ∈ Finset.range K, a k) :=
        mul_le_mul_of_nonneg_left hadjacent hC
      _ ≤ stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
            (2 * (stepAverageConstant h oracle params +
              errorAverageConstant h oracle params)) := by
        gcongr
      _ = stochasticComplexityConstant h oracle params := by
        rw [stochasticComplexityConstant_def]
        ring
  have htermNonneg (k : ℕ) (_hk : k ∈ Finset.Icc 1 (K - 1)) :
      0 ≤ stochasticResidualConstant h params.delta params.beta params.rho
        params.multiplierBound *
        (run'.baseStepMeanSquare k + run'.baseStepMeanSquare (k - 1) +
          run'.gradientErrorMeanSquare k +
            run'.gradientErrorMeanSquare (k - 1)) := by
    apply mul_nonneg hC
    exact add_nonneg
      (add_nonneg
        (add_nonneg (baseStepMeanSquare_nonneg run' k)
          (baseStepMeanSquare_nonneg run' (k - 1)))
        (gradientErrorMeanSquare_nonneg run' k))
      (gradientErrorMeanSquare_nonneg run' (k - 1))
  -- Lift every fixed-index bound to `ℝ≥0∞` and add the finite family.
  have hfixedSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run'.point (k + 1)) (run'.multiplier (k + 1))) ≤
        ENNReal.ofReal (stochasticComplexityConstant h oracle params) := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run'.point (k + 1)) (run'.multiplier (k + 1))) ≤
          ∑ k ∈ Finset.Icc 1 (K - 1), ENNReal.ofReal
            (stochasticResidualConstant h params.delta params.beta params.rho
              params.multiplierBound *
              (run'.baseStepMeanSquare k + run'.baseStepMeanSquare (k - 1) +
                run'.gradientErrorMeanSquare k +
                  run'.gradientErrorMeanSquare (k - 1))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkbounds := Finset.mem_Icc.mp hk
        have hklt : k < K := by omega
        exact fixedResidualMeanSquare_le run' hrun'Admissible hkbounds.1 hklt
      _ = ENNReal.ofReal
          (∑ k ∈ Finset.Icc 1 (K - 1),
            stochasticResidualConstant h params.delta params.beta params.rho
              params.multiplierBound *
              (run'.baseStepMeanSquare k + run'.baseStepMeanSquare (k - 1) +
                run'.gradientErrorMeanSquare k +
                  run'.gradientErrorMeanSquare (k - 1))) :=
        (ENNReal.ofReal_sum_of_nonneg htermNonneg).symm
      _ ≤ ENNReal.ofReal (stochasticComplexityConstant h oracle params) :=
        ENNReal.ofReal_le_ofReal hrealSum
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hKnatOne : 1 < K := by omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnatOne
  have hdenominator : 0 < (K : ℝ) - 1 := by
    linarith
  have hOneNonneg : (0 : ℝ) ≤ 1 := by norm_num
  -- Divide the finite residual total by the exact number of output indices.
  have hrun'Rate :
      KKT.Stochastic.residualMeanSquare
          (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
          (UniformOutput.point run') (UniformOutput.multiplier run') ≤
        ENNReal.ofReal
          (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) := by
    rw [UniformOutput.residualMeanSquare_eq_expect run' K hK hrun'Support, hcard,
      ENNReal.natCast_sub, Nat.cast_one]
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
          KKT.Stochastic.residualMeanSquare ℙ f c
            (run'.point (k + 1)) (run'.multiplier (k + 1))) /
            ((K : ℝ≥0∞) - 1) ≤
          ENNReal.ofReal (stochasticComplexityConstant h oracle params) /
            ((K : ℝ≥0∞) - 1) :=
        ENNReal.div_le_div_right hfixedSum _
      _ = ENNReal.ofReal
          (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) := by
        rw [ENNReal.ofReal_div_of_pos hdenominator,
          ENNReal.ofReal_sub (K : ℝ) hOneNonneg,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  -- Return from the pathwise version using almost-everywhere residual invariance.
  have houtputEq :
      KKT.Stochastic.residualMeanSquare
          (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
          (UniformOutput.point run) (UniformOutput.multiplier run) =
        KKT.Stochastic.residualMeanSquare
          (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
          (UniformOutput.point run') (UniformOutput.multiplier run') := by
    rw [UniformOutput.residualMeanSquare_eq_expect run K hK hrunSupport,
      UniformOutput.residualMeanSquare_eq_expect run' K hK hrun'Support]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact residualMeanSquare_congr (hpointAE (k + 1)).symm
      (hmultiplierAE (k + 1)).symm
  exact houtputEq.trans_le hrun'Rate

/-- Helper for Corollary 4.2: measurable corrected outputs, the residual rate,
and the iteration threshold imply the stochastic approximate-pair certificate. -/
theorem UniformOutput.isApproximatePair_of_residualRate
    (K : ℕ) (hK : 2 ≤ K)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      stochasticComplexityConstant h oracle params * ε⁻¹ ^ 2 ≤ (K : ℝ) - 1)
    (hpointMeasurable : AEMeasurable (UniformOutput.point run)
      (LALM.StochasticRun.UniformOutput.measure K hK ℙ))
    (hmultiplierMeasurable : AEMeasurable (UniformOutput.multiplier run)
      (LALM.StochasticRun.UniformOutput.measure K hK ℙ))
    (h_residualRate :
      KKT.Stochastic.residualMeanSquare
          (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
          (UniformOutput.point run) (UniformOutput.multiplier run) ≤
        ENNReal.ofReal
          (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1))) :
    KKT.Stochastic.IsApproximatePair
      (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c ε
      (UniformOutput.point run) (UniformOutput.multiplier run) := by
  -- Convert the iteration threshold into the real inverse-square rate.
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hεzero : (ε : ℝ) ≠ 0 := hεreal.ne'
  have hKnatOne : 1 < K := by omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnatOne
  have hdenominator : 0 < (K : ℝ) - 1 := by
    linarith
  have hrealRate :
      stochasticComplexityConstant h oracle params / ((K : ℝ) - 1) ≤
        (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    calc
      stochasticComplexityConstant h oracle params =
          (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) *
            (ε : ℝ) ^ 2 := by
        field_simp [hεzero]
      _ ≤ ((K : ℝ) - 1) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h_iterations (sq_nonneg (ε : ℝ))
      _ = (ε : ℝ) ^ 2 * ((K : ℝ) - 1) := by ring
  -- Transport the real rate once through `ENNReal.ofReal`.
  have hresidual :
      KKT.Stochastic.residualMeanSquare
          (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
          (UniformOutput.point run) (UniformOutput.multiplier run) ≤
        (ε : ℝ≥0∞) ^ 2 := by
    calc
      KKT.Stochastic.residualMeanSquare
          (LALM.StochasticRun.UniformOutput.measure K hK ℙ) f c
          (UniformOutput.point run) (UniformOutput.multiplier run) ≤
          ENNReal.ofReal
            (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) :=
        h_residualRate
      _ ≤ ENNReal.ofReal ((ε : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal hrealRate
      _ = (ε : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  -- Supply the two output-measurability companions to the canonical constructor.
  exact KKT.Stochastic.IsApproximatePair.of_residualMeanSquare_le
    hpointMeasurable hmultiplierMeasurable hresidual

/-- Corollary 4.2 (10): with almost-sure corrected admissibility, the independent
uniform output at the corrected threshold is a stochastic `ε`-KKT pair. -/
theorem UniformOutput.isApproximatePair_of_iterationBound
    (K : ℕ) (hK : 2 ≤ K)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_admissible : run.IsAEAdmissiblePrefix K)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      stochasticComplexityConstant h oracle params * ε⁻¹ ^ 2 ≤ (K : ℝ) - 1) :
    KKT.Stochastic.IsApproximatePair
      (measure K hK ℙ) f c ε
      (UniformOutput.point run) (UniformOutput.multiplier run) := by
  -- Route correction: fresh-batch adaptedness now comes from the repaired owner;
  -- the checked final assembly leaves only the corrected coupled moment rate.
  refine UniformOutput.isApproximatePair_of_residualRate K hK run ε ε_pos
    h_iterations (UniformOutput.aemeasurable_point K hK run)
    (UniformOutput.aemeasurable_multiplier K hK run) ?_
  -- Apply the corrected telescoped-moment and uniform-averaging residual bound.
  exact UniformOutput.residualMeanSquare_le K hK run h_admissible

/-- Corollary 4.2 (11): the corrected stochastic-gradient count under the SPIDER
schedule is `O(ε⁻³)`. -/
theorem gradientEvaluationCount_isBigO
    (run : ∀ ε : ℝ≥0, ScheduledRun h oracle ℙ x₀ multiplier₀
      params (stochasticIterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦ ((run ε).gradientEvaluationCount
      (stochasticIterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
  -- Package the fixed corrected schedule coefficients into one asymptotic bound.
  let C : ℝ := stochasticComplexityConstant h oracle params
  let D : ℝ := |C| + 3
  let A : ℝ :=
    2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2 *
      displacementFactor h params.delta ^ 2
  let M : ℝ := D * ((D + 1) + 2 * (A * (D + 1) + 1))
  refine Asymptotics.IsBigO.of_bound M ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  let x : ℝ := (ε : ℝ)⁻¹
  let K : ℕ := stochasticIterationBudget h oracle params ε
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact (one_le_inv₀ hεreal).2 hεrealOne
  have hxNonneg : 0 ≤ x := le_trans zero_le_one hx
  have hxSq : 1 ≤ x ^ 2 := by nlinarith
  have hxSqNonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [abs_nonneg C]
  have hDNonneg : 0 ≤ D := le_trans zero_le_one hD
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [errorStepConstant_pos h params]
  have hK : 2 ≤ K := by
    dsimp only [K]
    rw [stochasticIterationBudget_def]
    omega
  have hKNonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hzeroOne : (0 : ℝ) ≤ 1 := by norm_num
  -- The ceiling budget is at most a fixed multiple of `ε⁻²` near zero.
  have hKBound : (K : ℝ) ≤ D * x ^ 2 := by
    dsimp only [K]
    rw [stochasticIterationBudget_def]
    by_cases hC : 0 ≤ C
    · have hargument : 0 ≤ C * x ^ 2 := mul_nonneg hC hxSqNonneg
      have hceiling := Nat.ceil_lt_add_one hargument
      have hCplus : 0 ≤ C + 3 := by positivity
      rw [Nat.cast_add, Nat.cast_ofNat]
      dsimp only [D]
      rw [abs_of_nonneg hC]
      nlinarith [mul_nonneg hCplus (sub_nonneg.mpr hxSq)]
    · have hargument : C * x ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hxSqNonneg
      have hceiling : Nat.ceil (C * x ^ 2) = 0 :=
        Nat.ceil_eq_zero.mpr hargument
      rw [hceiling, Nat.zero_add, Nat.cast_ofNat]
      dsimp only [D]
      have hcoefficient : 0 ≤ |C| + 3 := by positivity
      have hthree : (3 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      have hproduct : (3 : ℝ) * 1 ≤ (|C| + 3) * x ^ 2 :=
        mul_le_mul hthree hxSq hzeroOne hcoefficient
      nlinarith
  -- Convert the quadratic horizon bound into linear refresh and inner-batch bounds.
  have hrefreshRaw := refreshPeriod_le_sqrt_add_one K hK
  have hDsq : D ≤ D ^ 2 := by nlinarith
  have hKSquare : (K : ℝ) ≤ (D * x) ^ 2 := by
    calc
      (K : ℝ) ≤ D * x ^ 2 := hKBound
      _ ≤ D ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hDsq hxSqNonneg
      _ = (D * x) ^ 2 := by ring
  have hsqrtK : Real.sqrt K ≤ D * x := by
    have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
    have hsqrtSquare := Real.sq_sqrt hKNonneg
    have hDxNonneg : 0 ≤ D * x := mul_nonneg hDNonneg hxNonneg
    nlinarith
  have hrefreshBound :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ (D + 1) * x := by
    calc
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := hrefreshRaw
      _ ≤ D * x + 1 := by
        simpa only [add_comm] using add_le_add_right hsqrtK 1
      _ ≤ (D + 1) * x := by nlinarith
  have hinnerRaw := innerBatchSize_le_linear h oracle params K
  have hinnerBound :
      ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
        (A * (D + 1) + 1) * x := by
    calc
      ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
          A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
        simpa only [A] using hinnerRaw
      _ ≤ A * ((D + 1) * x) + 1 := by
        gcongr
      _ ≤ (A * (D + 1) + 1) * x := by
        nlinarith [mul_nonneg hA (add_nonneg hDNonneg zero_le_one)]
  -- Insert the combinatorial counter bound and collect the cubic terms.
  have hcountNat := gradientEvaluationCount_le_schedule K hK (run ε)
  have hcountReal :
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤
        ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
          2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
    exact_mod_cast hcountNat
  have hrefreshNonneg :
      0 ≤ ((SPIDER.refreshPeriod K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hinnerNonneg :
      0 ≤ ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hrefreshWork :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K ≤
        ((D + 1) * x) * (D * x ^ 2) := by
    exact mul_le_mul hrefreshBound hKBound hKNonneg
      (mul_nonneg (add_nonneg hDNonneg zero_le_one) hxNonneg)
  have hinnerCoefficientNonneg : 0 ≤ A * (D + 1) + 1 := by positivity
  have hinnerWork :
      (2 : ℝ) * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) ≤
        2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) := by
    gcongr
  have hcountBound :
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤ M * x ^ 3 := by
    calc
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤
          ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
            2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) :=
        hcountReal
      _ ≤ ((D + 1) * x) * (D * x ^ 2) +
          2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) :=
        add_le_add hrefreshWork hinnerWork
      _ = M * x ^ 3 := by
        dsimp only [M]
        ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxNonneg 3)]
  simpa only [K, x] using hcountBound

/-- Corollary 4.2 (12): the corrected stochastic constraint-evaluation count is
`O(ε⁻²)`. -/
theorem constraintEvaluationCount_isBigO
    (run : ∀ ε : ℝ≥0, ScheduledRun h oracle ℙ x₀ multiplier₀
      params (stochasticIterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦ ((run ε).constraintEvaluationCount
      (stochasticIterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Insert the two deterministic constraint evaluations charged per transition.
  have hbudget :=
    natCeilQuadraticBudget_isBigO (stochasticComplexityConstant h oracle params)
  have hscaled := hbudget.const_mul_left (2 : ℝ)
  simpa only [constraintEvaluationCount_spec, stochasticIterationBudget_def,
    Nat.cast_mul, Nat.cast_ofNat] using hscaled

/-- Corollary 4.2 (13): the corrected stochastic Jacobian-evaluation count is
`O(ε⁻²)`. -/
theorem jacobianEvaluationCount_isBigO
    (run : ∀ ε : ℝ≥0, ScheduledRun h oracle ℙ x₀ multiplier₀
      params (stochasticIterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦ ((run ε).jacobianEvaluationCount
      (stochasticIterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Insert the two deterministic Jacobian evaluations charged per transition.
  have hbudget :=
    natCeilQuadraticBudget_isBigO (stochasticComplexityConstant h oracle params)
  have hscaled := hbudget.const_mul_left (2 : ℝ)
  simpa only [jacobianEvaluationCount_spec, stochasticIterationBudget_def,
    Nat.cast_mul, Nat.cast_ofNat] using hscaled

/-- Corollary 4.2 (14): the corrected stochastic primal-solve count is
`O(ε⁻²)`. -/
theorem primalSolveCount_isBigO
    (run : ∀ ε : ℝ≥0, ScheduledRun h oracle ℙ x₀ multiplier₀
      params (stochasticIterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦ ((run ε).primalSolveCount
      (stochasticIterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Normalize the opaque counter and budget through their owner-side equations.
  simpa only [primalSolveCount_spec, stochasticIterationBudget_def] using
      natCeilQuadraticBudget_isBigO (stochasticComplexityConstant h oracle params)

/-- Corollary 4.2 (15): the corrected stochastic correction-solve count is
`O(ε⁻²)`. -/
theorem correctionSolveCount_isBigO
    (run : ∀ ε : ℝ≥0, ScheduledRun h oracle ℙ x₀ multiplier₀
      params (stochasticIterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦ ((run ε).correctionSolveCount
      (stochasticIterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Normalize the opaque counter and budget through their owner-side equations.
  simpa only [correctionSolveCount_spec, stochasticIterationBudget_def] using
      natCeilQuadraticBudget_isBigO (stochasticComplexityConstant h oracle params)

namespace UniformOutput

open Localization

/-- Helper for Corollary 4.2: restricting the corrected product integral to a
finite uniform first coordinate is bounded by the average of its sections. -/
private lemma setLIntegral_uniform_le_sum
    (K : ℕ) (hK : 2 ≤ K) (S : Set Ω) (g : ℕ × Ω → ℝ≥0∞) :
    ∫⁻ output in Set.univ ×ˢ S, g output
        ∂LALM.StochasticRun.UniformOutput.measure K hK ℙ ≤
      (∑ k ∈ Finset.Icc 1 (K - 1), ∫⁻ omega in S, g (k, omega) ∂ℙ) /
        (Finset.Icc 1 (K - 1)).card := by
  -- Tonelli reduces the restricted product integral to countable sections.
  let s := Finset.Icc 1 (K - 1)
  let p := LALM.StochasticRun.UniformOutput.indexLaw K hK
  change (∫⁻ output in Set.univ ×ˢ S, g output ∂p.toMeasure.prod ℙ) ≤ _
  rw [← Measure.prod_restrict]
  calc
    (∫⁻ output, g output ∂
        (p.toMeasure.restrict Set.univ).prod (ℙ.restrict S)) ≤
        ∫⁻ k in Set.univ, ∫⁻ omega in S, g (k, omega) ∂ℙ ∂p.toMeasure :=
      lintegral_prod_le g
    _ = ∑' k, (∫⁻ omega in S, g (k, omega) ∂ℙ) * p.toMeasure {k} := by
      rw [Measure.restrict_univ, lintegral_countable']
    _ = ∑ k ∈ s,
        (∫⁻ omega in S, g (k, omega) ∂ℙ) * (s.card : ℝ≥0∞)⁻¹ := by
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
    _ = (∑ k ∈ Finset.Icc 1 (K - 1),
        ∫⁻ omega in S, g (k, omega) ∂ℙ) /
          (Finset.Icc 1 (K - 1)).card := by
      rw [ENNReal.div_eq_inv_mul, mul_comm, Finset.sum_mul]

/-- Helper for Corollary 4.2: terminal corrected survival supplies the
fixed-path residual comparison at every sampled index. -/
private lemma residualSq_le_of_survival
    (K : ℕ) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (omega : Ω) (homega : omega ∈ survivalEvent run X K)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk : k < K) :
    KKT.residual f c (run.point (k + 1) omega)
        (run.multiplier (k + 1) omega) ^ 2 ≤
      stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2 +
          ‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2) := by
  -- Repackage the terminal pre-exit invariant as a bounded fixed path.
  have hraw := preExitPrefixBounds run X initial_mem h_region omega K homega
  have bounds : run.BoundedAdmissiblePath K omega := by
    constructor
    · intro j hj
      exact hraw.1 j (hj.trans (Nat.lt_succ_self K))
    · intro j hj
      exact hraw.2.1 j (hj.trans (Nat.lt_succ_self K))
    · intro j hj
      exact hraw.2.2 j (hj.trans (Nat.le_succ K))
  exact stochasticResidual_sq_le run bounds hk_pos hk

/-- Helper for Corollary 4.2: a surviving fixed-index corrected residual
section is controlled by its four neighboring restricted energy integrals. -/
private lemma survivalRestrictedResidualSection_le
    (K : ℕ) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk : k < K) :
    (∫⁻ omega in survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (run.point (k + 1) omega)
            (run.multiplier (k + 1) omega) ^ 2) ∂ℙ) ≤
      ENNReal.ofReal
        (stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
          ((∫ omega in survivalEvent run X K, ‖run.baseStep k omega‖ ^ 2 ∂ℙ) +
            (∫ omega in survivalEvent run X K,
              ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
            ((∫ omega in survivalEvent run X K,
              ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
              ∫ omega in survivalEvent run X K,
                ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ))) := by
  let C : ℝ := stochasticResidualConstant h params.delta params.beta params.rho
    params.multiplierBound
  let moments : Ω → ℝ := fun omega ↦
    ‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2 +
      ‖run.gradientError k omega‖ ^ 2 +
        ‖run.gradientError (k - 1) omega‖ ^ 2
  have hkPrev : k - 1 < K := by omega
  have hsurvivalK := nullMeasurableSet_survivalEvent run X hX K
  have hsubsetK : survivalEvent run X K ⊆ survivalEvent run X k :=
    survivalEvent_antitone run X (Nat.le_of_lt hk)
  have hsubsetPrev : survivalEvent run X K ⊆ survivalEvent run X (k - 1) :=
    survivalEvent_antitone run X (Nat.le_of_lt hkPrev)
  -- Obtain every restricted integrability fact from the stopped-process API.
  have hstepK : IntegrableOn (fun omega ↦ ‖run.baseStep k omega‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_baseStepSquare_preExit run X hX initial_mem h_region k).mono_set
      hsubsetK
  have hstepPrev : IntegrableOn (fun omega ↦ ‖run.baseStep (k - 1) omega‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_baseStepSquare_preExit run X hX initial_mem h_region (k - 1)).mono_set
      hsubsetPrev
  have herrorK : IntegrableOn (fun omega ↦ ‖run.gradientError k omega‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k).mono_set
      hsubsetK
  have herrorPrev : IntegrableOn
      (fun omega ↦ ‖run.gradientError (k - 1) omega‖ ^ 2)
      (survivalEvent run X K) ℙ :=
    (integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region (k - 1)).mono_set
      hsubsetPrev
  have hmoments : IntegrableOn moments (survivalEvent run X K) ℙ :=
    ((hstepK.add hstepPrev).add herrorK).add herrorPrev
  have hC : 0 ≤ C := stochasticResidualConstant_nonneg h params
  have hright : IntegrableOn (fun omega ↦ C * moments omega)
      (survivalEvent run X K) ℙ := hmoments.const_mul C
  have hmomentsNonneg (omega : Ω) : 0 ≤ moments omega := by
    dsimp only [moments]
    positivity
  have hrightNonneg :
      0 ≤ᵐ[ℙ.restrict (survivalEvent run X K)] fun omega ↦ C * moments omega :=
    ae_of_all _ fun omega ↦ mul_nonneg hC (hmomentsNonneg omega)
  -- Normalize the integral of the four-term moment sum once.
  have hmomentsIntegral :
      (∫ omega in survivalEvent run X K, moments omega ∂ℙ) =
        (∫ omega in survivalEvent run X K, ‖run.baseStep k omega‖ ^ 2 ∂ℙ) +
          (∫ omega in survivalEvent run X K,
            ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
          ((∫ omega in survivalEvent run X K,
            ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ) := by
    have hfirst := integral_add hstepK hstepPrev
    have hsecond := integral_add (hstepK.add hstepPrev) herrorK
    have hthird := integral_add ((hstepK.add hstepPrev).add herrorK) herrorPrev
    have hsecond' :
        (∫ omega in survivalEvent run X K,
          ‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2 +
            ‖run.gradientError k omega‖ ^ 2 ∂ℙ) =
          (∫ omega in survivalEvent run X K,
            ‖run.baseStep k omega‖ ^ 2 +
              ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError k omega‖ ^ 2 ∂ℙ := by
      simpa only [Pi.add_apply] using hsecond
    calc
      (∫ omega in survivalEvent run X K, moments omega ∂ℙ) =
          (∫ omega in survivalEvent run X K,
            ‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2 +
              ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ := by
        simpa only [moments, Pi.add_apply] using hthird
      _ = ((∫ omega in survivalEvent run X K,
              ‖run.baseStep k omega‖ ^ 2 +
                ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ := by
        rw [hsecond']
      _ = (((∫ omega in survivalEvent run X K,
              ‖run.baseStep k omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ := by
        rw [hfirst]
      _ = (∫ omega in survivalEvent run X K, ‖run.baseStep k omega‖ ^ 2 ∂ℙ) +
          (∫ omega in survivalEvent run X K,
            ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
          ((∫ omega in survivalEvent run X K,
            ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
            ∫ omega in survivalEvent run X K,
              ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ) := by ring
  calc
    (∫⁻ omega in survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (run.point (k + 1) omega)
            (run.multiplier (k + 1) omega) ^ 2) ∂ℙ) ≤
        ∫⁻ omega in survivalEvent run X K,
          ENNReal.ofReal (C * moments omega) ∂ℙ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem₀ hsurvivalK] with omega homega
      apply ENNReal.ofReal_le_ofReal
      exact residualSq_le_of_survival K confidence X initial_mem run h_region
        omega homega k hk_pos hk
    _ = ENNReal.ofReal
        (∫ omega in survivalEvent run X K, C * moments omega ∂ℙ) :=
      (ofReal_integral_eq_lintegral_ofReal hright hrightNonneg).symm
    _ = ENNReal.ofReal
        (stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
          ((∫ omega in survivalEvent run X K, ‖run.baseStep k omega‖ ^ 2 ∂ℙ) +
            (∫ omega in survivalEvent run X K,
              ‖run.gradientError k omega‖ ^ 2 ∂ℙ) +
            ((∫ omega in survivalEvent run X K,
              ‖run.baseStep (k - 1) omega‖ ^ 2 ∂ℙ) +
              ∫ omega in survivalEvent run X K,
                ‖run.gradientError (k - 1) omega‖ ^ 2 ∂ℙ))) := by
      rw [integral_const_mul, hmomentsIntegral]

/-- Helper for Corollary 4.2: the terminal-survival restricted corrected
uniform residual numerator has the canonical inverse-iteration bound. -/
lemma survivalRestrictedResidualLIntegral_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_region : RegionCondition h oracle params confidence X) :
    (∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (point run output) (multiplier run output) ^ 2)
          ∂LALM.StochasticRun.UniformOutput.measure K hK ℙ) ≤
      ENNReal.ofReal
        (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) := by
  -- Use one common terminal survival set for all fixed-index sections.
  let S : Set Ω := survivalEvent run X K
  let C : ℝ := stochasticResidualConstant h params.delta params.beta params.rho
    params.multiplierBound
  let a : ℕ → ℝ := fun k ↦
    (∫ omega in S, ‖run.baseStep k omega‖ ^ 2 ∂ℙ) +
      ∫ omega in S, ‖run.gradientError k omega‖ ^ 2 ∂ℙ
  have hC : 0 ≤ C := stochasticResidualConstant_nonneg h params
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp only [a]
    exact add_nonneg (integral_nonneg fun omega ↦ sq_nonneg _)
      (integral_nonneg fun omega ↦ sq_nonneg _)
  -- Terminally restricted moments are dominated by their stopped energies.
  have hstepRestricted :
      (∑ k ∈ Finset.range K, ∫ omega in S, ‖run.baseStep k omega‖ ^ 2 ∂ℙ) ≤
        stoppedBaseStepEnergy run X K := by
    rw [stoppedBaseStepEnergy_def]
    apply Finset.sum_le_sum
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    have hsubset : S ⊆ survivalEvent run X k :=
      survivalEvent_antitone run X (Nat.le_of_lt hklt)
    have hintegrable :=
      integrableOn_baseStepSquare_preExit run X hX initial_mem h_region k
    exact setIntegral_mono_set hintegrable
      (ae_of_all _ fun omega ↦ sq_nonneg ‖run.baseStep k omega‖)
      (ae_of_all _ hsubset)
  have herrorRestricted :
      (∑ k ∈ Finset.range K,
        ∫ omega in S, ‖run.gradientError k omega‖ ^ 2 ∂ℙ) ≤
        stoppedGradientErrorEnergy run X K := by
    rw [stoppedGradientErrorEnergy_def]
    apply Finset.sum_le_sum
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    have hsubset : S ⊆ survivalEvent run X k :=
      survivalEvent_antitone run X (Nat.le_of_lt hklt)
    have hintegrable :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact setIntegral_mono_set hintegrable
      (ae_of_all _ fun omega ↦ sq_nonneg ‖run.gradientError k omega‖)
      (ae_of_all _ hsubset)
  have htotalRange :
      (∑ k ∈ Finset.range K, a k) ≤
        stoppedBaseStepEnergy run X K + stoppedGradientErrorEnergy run X K := by
    dsimp only [a]
    rw [Finset.sum_add_distrib]
    exact add_le_add hstepRestricted herrorRestricted
  have hstopped :=
    scheduledStoppedEnergyBounds K hK confidence X hX initial_mem run h_region
  have htotalAllowance :
      (∑ k ∈ Finset.range K, a k) ≤
        stepAverageConstant h oracle params + errorAverageConstant h oracle params :=
    htotalRange.trans (add_le_add hstopped.2 hstopped.1)
  have hadjacent := sumAdjacentMoment_le_two_range a K hK ha
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hrealSum :
      (∑ k ∈ Finset.Icc 1 (K - 1), C * (a k + a (k - 1))) ≤
        stochasticComplexityConstant h oracle params := by
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
      _ = stochasticComplexityConstant h oracle params := by
        rw [stochasticComplexityConstant_def]
        ring
  -- Sum the fixed-section estimates before dividing by the uniform cardinality.
  have htermNonneg (k : ℕ) (_hk : k ∈ Finset.Icc 1 (K - 1)) :
      0 ≤ C * (a k + a (k - 1)) :=
    mul_nonneg hC (add_nonneg (ha k) (ha (k - 1)))
  have hfixedSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        ∫⁻ omega in S,
          ENNReal.ofReal
            (KKT.residual f c (point run (k, omega))
              (multiplier run (k, omega)) ^ 2) ∂ℙ) ≤
        ENNReal.ofReal (stochasticComplexityConstant h oracle params) := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
        ∫⁻ omega in S,
          ENNReal.ofReal
            (KKT.residual f c (point run (k, omega))
              (multiplier run (k, omega)) ^ 2) ∂ℙ) ≤
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
      _ ≤ ENNReal.ofReal (stochasticComplexityConstant h oracle params) :=
        ENNReal.ofReal_le_ofReal hrealSum
  have huniform := setLIntegral_uniform_le_sum (ℙ := ℙ) K hK S
    (fun output ↦ ENNReal.ofReal
      (KKT.residual f c (point run output) (multiplier run output) ^ 2))
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast (show 1 < K by omega)
  have hdenominator : 0 < (K : ℝ) - 1 := by linarith
  have hOneNonneg : (0 : ℝ) ≤ 1 := by norm_num
  calc
    (∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c (point run output) (multiplier run output) ^ 2)
          ∂LALM.StochasticRun.UniformOutput.measure K hK ℙ) ≤
        (∑ k ∈ Finset.Icc 1 (K - 1),
          ∫⁻ omega in S,
            ENNReal.ofReal
              (KKT.residual f c (point run (k, omega))
                (multiplier run (k, omega)) ^ 2) ∂ℙ) /
          (Finset.Icc 1 (K - 1)).card := by
      simpa only [S] using huniform
    _ ≤ ENNReal.ofReal (stochasticComplexityConstant h oracle params) /
        (Finset.Icc 1 (K - 1)).card :=
      ENNReal.div_le_div_right hfixedSum _
    _ = ENNReal.ofReal
        (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) := by
      rw [hcard, ENNReal.natCast_sub, Nat.cast_one,
        ENNReal.ofReal_div_of_pos hdenominator,
        ENNReal.ofReal_sub (K : ℝ) hOneNonneg,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]

end UniformOutput

end StochasticRun

namespace SafeguardedRestart

open StochasticRun.Localization

variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

/-- Helper for Corollary 4.2: the complete observable record of one corrected
restart attempt. -/
private abbrev AttemptObservable (Ξ : Type u) (n m : ℕ) :=
  ℕ × ((ℕ → ℕ → Ξ) ×
    (ℕ → EuclideanSpace ℝ (Fin n)) ×
    (ℕ → EuclideanSpace ℝ (Fin m)) ×
    (ℕ → EuclideanSpace ℝ (Fin n)))

/-- Helper for Corollary 4.2: corrected attempt records whose point trajectory
fails at least one safeguard test. -/
private def attemptFailureRecords
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (AttemptObservable Ξ n m) :=
  {z | ∀ j ∈ Finset.Icc 1 K, z.2.2.1 j ∈ X}ᶜ

/-- Helper for Corollary 4.2: the corrected record-level failure event is
measurable. -/
private lemma measurableSet_attemptFailureRecords
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    MeasurableSet (attemptFailureRecords (Ξ := Ξ) (m := m) K X) := by
  -- Assemble finite coordinate membership and then complement the success event.
  have hcoordinate (j : ℕ) : MeasurableSet
      {z : AttemptObservable Ξ n m | z.2.2.1 j ∈ X} :=
    hX.preimage (measurable_pi_apply j |>.comp measurable_snd.snd.fst)
  have hsuccess : MeasurableSet
      {z : AttemptObservable Ξ n m | ∀ j ∈ Finset.Icc 1 K, z.2.2.1 j ∈ X} := by
    induction Finset.Icc 1 K using Finset.induction with
    | empty =>
        simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          Set.setOf_true, MeasurableSet.univ]
    | insert a s ha hs =>
        simpa only [Finset.forall_mem_insert, Set.setOf_and] using
          (hcoordinate a).inter hs
  exact hsuccess.compl

/-- Helper for Corollary 4.2: pulling corrected record failure back along an
attempt observable gives the corresponding attempt-failure event. -/
private lemma attemptFailureRecords_preimage
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    (fun omega ↦
      (restart.outputIndex i omega,
        fun k j ↦ (restart.attempt i).sample k j omega,
        fun k ↦ (restart.attempt i).point k omega,
        fun k ↦ (restart.attempt i).multiplier k omega,
        fun k ↦ (restart.attempt i).baseStep k omega)) ⁻¹'
        attemptFailureRecords (Ξ := Ξ) (m := m) K X =
      (restart.successEvent i)ᶜ := by
  -- Both sides are the negation of the public corrected completion criterion.
  ext omega
  simp only [Set.mem_preimage, attemptFailureRecords, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  rw [restart.successEvent_eq_survivalEvent, mem_survivalEvent]
  simp only [Finset.mem_Icc, Set.mem_Icc]

/-- Helper for Corollary 4.2: exceeding `t` corrected attempts is equivalent
to failure of every attempt with index below `t`. -/
private lemma attemptCount_tail_eq_failureInter
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (t : ℕ) :
    {omega | (t : ℕ∞) < restart.attemptCount omega} =
      ⋂ i ∈ Finset.range t, (restart.successEvent i)ᶜ := by
  -- Split on finite versus infinite first acceptance and compare natural indices.
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
    Set.mem_compl_iff]
  cases hfirst : restart.firstAccepted omega using ENat.recTopCoe with
  | top =>
      have hall := (restart.firstAccepted_eq_top_iff omega).mp hfirst
      simp only [restart.attemptCount_eq, hfirst, top_add, ENat.coe_lt_top,
        true_iff]
      exact fun i _hi ↦ hall i
  | coe a =>
      have hcharacterization :=
        (restart.firstAccepted_eq_coe_iff a omega).mp hfirst
      simp only [restart.attemptCount_eq, hfirst, ← ENat.coe_one,
        ← ENat.coe_add, ENat.coe_lt_coe]
      constructor
      · intro ht i hit
        apply hcharacterization.2 i
        omega
      · intro hall
        have hta : t ≤ a := by
          by_contra hnot
          have hat : a < t := Nat.lt_of_not_ge hnot
          exact hall a hat hcharacterization.1
        omega

/-- Helper for Corollary 4.2: the corrected attempt-count tail is dominated
by the geometric failure probability. -/
theorem attemptCount_tail_le
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (t : ℕ) :
    ℙ {omega | (t : ℕ∞) < restart.attemptCount omega} ≤
      ENNReal.ofReal confidence ^ t := by
  -- Bound each corrected failure event by the common confidence level.
  have hfailure (i : ℕ) :
      ℙ (restart.successEvent i)ᶜ ≤ ENNReal.ofReal confidence := by
    have hsuccessNull : NullMeasurableSet (restart.successEvent i) ℙ := by
      rw [restart.successEvent_eq_survivalEvent]
      exact nullMeasurableSet_survivalEvent (restart.attempt i) X hX K
    have hsuccessLower : ENNReal.ofReal (1 - confidence) ≤
        ℙ (restart.successEvent i) := by
      rw [restart.successEvent_eq_survivalEvent]
      exact survivalProbability_ge K hK confidence confidence_pos X hX initial_mem
        (restart.attempt i) h_region
    have hconfidence : ENNReal.ofReal confidence ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal confidence_lt_one.le
    calc
      ℙ (restart.successEvent i)ᶜ = 1 - ℙ (restart.successEvent i) :=
        prob_compl_eq_one_sub₀ hsuccessNull
      _ ≤ 1 - ENNReal.ofReal (1 - confidence) :=
        tsub_le_tsub_left hsuccessLower 1
      _ = ENNReal.ofReal confidence := by
        rw [ENNReal.ofReal_sub 1 confidence_pos.le, ENNReal.ofReal_one,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hconfidence]
  -- Mutual independence factors the finite intersection of record failures.
  have hfactor := restart.independent_attempt.measure_inter_preimage_eq_mul
    (Finset.range t)
    (sets := fun _ ↦ attemptFailureRecords (Ξ := Ξ) (m := m) K X)
    (fun _ _ ↦ measurableSet_attemptFailureRecords K X hX)
  rw [attemptCount_tail_eq_failureInter restart t]
  calc
    ℙ (⋂ i ∈ Finset.range t, (restart.successEvent i)ᶜ) =
        ∏ i ∈ Finset.range t, ℙ (restart.successEvent i)ᶜ := by
      simpa only [attemptFailureRecords_preimage] using hfactor
    _ ≤ ∏ _i ∈ Finset.range t, ENNReal.ofReal confidence :=
      Finset.prod_le_prod' fun i _hi ↦ hfailure i
    _ = ENNReal.ofReal confidence ^ t := by simp

/-- Helper for Corollary 4.2: an extended natural is the sum of the indicators
of all strict natural lower bounds. -/
private lemma enatToENNReal_eq_tsum_lt (a : ℕ∞) :
    (a : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < a then 1 else 0 := by
  -- Separate the infinite count from a finite initial segment.
  cases a using ENat.recTopCoe with
  | top =>
      simp only [ENat.toENNReal_top, lt_top_iff_ne_top]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe a =>
      simp only [ENat.toENNReal_coe, ENat.coe_lt_coe]
      calc
        (a : ℝ≥0∞) = ∑ t ∈ Finset.range a, (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_one, Finset.card_range]
        _ = ∑' t : ℕ, if t < a then 1 else 0 := by
          rw [tsum_eq_sum (s := Finset.range a)]
          · apply Finset.sum_congr rfl
            intro t ht
            rw [if_pos (Finset.mem_range.mp ht)]
          · intro t ht
            rw [if_neg]
            simpa only [Finset.mem_range] using ht

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: the lower integral of an extended-natural random
variable is bounded by the sum of its outer tail probabilities. -/
private lemma lintegralENat_le_tsum_tail (count : Ω → ℕ∞) :
    ∫⁻ omega, (count omega : ℝ≥0∞) ∂ℙ ≤
      ∑' t : ℕ, ℙ {omega | (t : ℕ∞) < count omega} := by
  -- Measurable hull indicators preserve outer measure without a hitting-time API.
  have hpoint (omega : Ω) : (count omega : ℝ≥0∞) ≤
      ∑' t : ℕ,
        (toMeasurable ℙ {omega | (t : ℕ∞) < count omega}).indicator
          (fun _ ↦ 1) omega := by
    rw [enatToENNReal_eq_tsum_lt]
    apply ENNReal.tsum_le_tsum
    intro t
    by_cases ht : (t : ℕ∞) < count omega
    · have hmem : omega ∈
          toMeasurable ℙ {omega | (t : ℕ∞) < count omega} :=
        subset_toMeasurable ℙ _ ht
      simp only [ht, if_true, Set.indicator_of_mem hmem]
      exact le_rfl
    · simp only [ht, if_false, zero_le]
  calc
    (∫⁻ omega, (count omega : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ omega, ∑' t : ℕ,
          (toMeasurable ℙ {omega | (t : ℕ∞) < count omega}).indicator
            (fun _ ↦ 1) omega ∂ℙ := lintegral_mono hpoint
    _ = ∑' t : ℕ, ∫⁻ omega,
        (toMeasurable ℙ {omega | (t : ℕ∞) < count omega}).indicator
          (fun _ ↦ 1) omega ∂ℙ := by
      rw [lintegral_tsum]
      intro t
      exact (measurable_const.indicator
        (measurableSet_toMeasurable ℙ _)).aemeasurable
    _ = ∑' t : ℕ, ℙ {omega | (t : ℕ∞) < count omega} := by
      apply tsum_congr
      intro t
      calc
        (∫⁻ omega,
            (toMeasurable ℙ {omega | (t : ℕ∞) < count omega}).indicator
              (fun _ ↦ 1) omega ∂ℙ) =
            ℙ (toMeasurable ℙ {omega | (t : ℕ∞) < count omega}) :=
          lintegral_indicator_one (measurableSet_toMeasurable ℙ _)
        _ = ℙ {omega | (t : ℕ∞) < count omega} := measure_toMeasurable _

/-- Helper for Corollary 4.2: a pointwise corrected per-attempt budget controls
the expected accumulated extended-natural cost. -/
private lemma lintegralCost_le_attemptCount_mul
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (cost : Ω → ℕ∞) (budget : ℕ)
    (hcost : ∀ omega, cost omega ≤ restart.attemptCount omega * budget) :
    ∫⁻ omega, (cost omega : ℝ≥0∞) ∂ℙ ≤
      (∫⁻ omega, (restart.attemptCount omega : ℝ≥0∞) ∂ℙ) * budget := by
  -- Coerce the accounting inequality and extract the finite constant.
  have hcoerced (omega : Ω) :
      (cost omega : ℝ≥0∞) ≤
        (restart.attemptCount omega : ℝ≥0∞) * budget := by
    simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
      ENat.toENNReal_mono (hcost omega)
  calc
    (∫⁻ omega, (cost omega : ℝ≥0∞) ∂ℙ) ≤
        ∫⁻ omega, (restart.attemptCount omega : ℝ≥0∞) * budget ∂ℙ :=
      lintegral_mono hcoerced
    _ = (∫⁻ omega, (restart.attemptCount omega : ℝ≥0∞) ∂ℙ) * budget := by
      rw [lintegral_mul_const']
      exact ENNReal.natCast_ne_top budget

/-- Helper for Corollary 4.2: independent corrected safeguarded restarts
terminate almost surely. -/
theorem terminatesAE
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∀ᵐ omega ∂ℙ, restart.firstAccepted omega ≠ ⊤ := by
  -- Nontermination lies in every geometrically decaying attempt-count tail.
  rw [ae_iff]
  simp only [not_ne_iff]
  refine ENNReal.eq_zero_of_le_mul_pow (ε := 1)
    (ENNReal.ofReal_lt_one.mpr confidence_lt_one) ?_
  intro t
  calc
    ℙ {omega | restart.firstAccepted omega = ⊤} ≤
        ℙ {omega | (t : ℕ∞) < restart.attemptCount omega} := by
      apply measure_mono
      intro omega homega
      have hcount : restart.attemptCount omega = ⊤ :=
        (restart.attemptCount_eq_top_iff omega).2 homega
      simp only [Set.mem_setOf_eq, hcount, ENat.coe_lt_top]
    _ ≤ ENNReal.ofReal confidence ^ t :=
      restart.attemptCount_tail_le confidence confidence_pos confidence_lt_one
        hX initial_mem h_region t
    _ = (1 : ℝ≥0) * ENNReal.ofReal confidence ^ t := by simp

/-- Helper for Corollary 4.2: the expected number of corrected restart
attempts is at most `1 / (1 - confidence)`. -/
theorem expectedAttemptCount_le
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ omega, (restart.attemptCount omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (1 / (1 - confidence)) := by
  -- Sum the tail estimate and normalize the geometric series in `ENNReal`.
  calc
    (∫⁻ omega, (restart.attemptCount omega : ℝ≥0∞) ∂ℙ) ≤
        ∑' t : ℕ, ℙ {omega | (t : ℕ∞) < restart.attemptCount omega} :=
      lintegralENat_le_tsum_tail restart.attemptCount
    _ ≤ ∑' t : ℕ, ENNReal.ofReal confidence ^ t :=
      ENNReal.tsum_le_tsum fun t ↦
        restart.attemptCount_tail_le confidence confidence_pos confidence_lt_one
          hX initial_mem h_region t
    _ = (1 - ENNReal.ofReal confidence)⁻¹ := ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (1 / (1 - confidence)) := by
      rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr confidence_lt_one),
        ENNReal.ofReal_one, ENNReal.ofReal_sub 1 confidence_pos.le,
        ENNReal.ofReal_one, one_div]

/-- Helper for Corollary 4.2: coercion of a finite natural cost commutes with
the positive-denominator geometric expected-attempt factor. -/
private lemma geometricBudget_ofReal
    (confidence : ℝ) (confidence_lt_one : confidence < 1) (budget : ℕ) :
    ENNReal.ofReal (1 / (1 - confidence)) * budget =
      ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
  -- Move the finite budget into `ofReal` and commute the real factors.
  have honeMinusConfidence : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  calc
    ENNReal.ofReal (1 / (1 - confidence)) * budget =
        ENNReal.ofReal (1 / (1 - confidence)) *
          ENNReal.ofReal (budget : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((1 / (1 - confidence)) * (budget : ℝ)) :=
      (ENNReal.ofReal_mul (one_div_nonneg.mpr honeMinusConfidence.le)).symm
    _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
      rw [one_div, div_eq_mul_inv, mul_comm]

/-- Helper for Corollary 4.2: a deterministic corrected per-attempt budget
inherits the geometric expected-attempt factor. -/
private lemma expectedCost_le
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X)
    (cost : Ω → ℕ∞) (budget : ℕ)
    (hcost : ∀ omega, cost omega ≤ restart.attemptCount omega * budget) :
    ∫⁻ omega, (cost omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) := by
  -- Transfer the pointwise budget and insert the geometric attempt estimate.
  calc
    (∫⁻ omega, (cost omega : ℝ≥0∞) ∂ℙ) ≤
        (∫⁻ omega, (restart.attemptCount omega : ℝ≥0∞) ∂ℙ) * budget :=
      lintegralCost_le_attemptCount_mul restart cost budget hcost
    _ ≤ ENNReal.ofReal (1 / (1 - confidence)) * budget :=
      mul_le_mul_left (expectedAttemptCount_le confidence confidence_pos
        confidence_lt_one hX initial_mem restart h_region) budget
    _ = ENNReal.ofReal ((budget : ℝ) / (1 - confidence)) :=
      geometricBudget_ofReal confidence confidence_lt_one budget

/-- Helper for Corollary 4.2: expected corrected executed iterations are at
most the horizon times the geometric expected-attempt factor. -/
private lemma expectedTotalIterations_le
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    ∫⁻ omega, (restart.totalIterations omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) := by
  -- Apply the generic cost transfer to the public corrected iteration bound.
  exact expectedCost_le confidence confidence_pos confidence_lt_one hX initial_mem
    restart h_region restart.totalIterations K restart.totalIterations_le_attemptCount_mul

/-- Helper for Corollary 4.2: the squared residual selected within one fixed
corrected restart attempt. -/
private noncomputable def selectedAttemptResidualSq
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (KKT.residual f c
      ((restart.attempt i).point (restart.outputIndex i omega + 1) omega)
      ((restart.attempt i).multiplier (restart.outputIndex i omega + 1) omega) ^ 2)

/-- Helper for Corollary 4.2: the point and multiplier trajectories form the
attempt observable needed by the selected-residual calculation. -/
private def pointMultiplierObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) :
    (ℕ → EuclideanSpace ℝ (Fin n)) × (ℕ → EuclideanSpace ℝ (Fin m)) :=
  (fun k ↦ (restart.attempt i).point k omega,
    fun k ↦ (restart.attempt i).multiplier k omega)

/-- Helper for Corollary 4.2: every corrected point-multiplier trajectory
observable is almost-everywhere measurable. -/
private lemma aemeasurablePointMultiplierObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (pointMultiplierObservable restart i) ℙ := by
  -- Assemble the two corrected trajectories coordinatewise.
  exact (aemeasurable_pi_lambda _ fun k ↦
    (restart.attempt i).aemeasurable_point k).prodMk
      (aemeasurable_pi_lambda _ fun k ↦
        (restart.attempt i).aemeasurable_multiplier k)

/-- Helper for Corollary 4.2: the uniform selector is independent of the point
and multiplier trajectories in its corrected attempt. -/
private lemma outputIndex_indep_pointMultiplierObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : ProbabilityTheory.IndepFun (restart.outputIndex i)
      (pointMultiplierObservable restart i) ℙ := by
  -- Project the needed trajectories from the certified complete attempt record.
  have hprojection : Measurable
      (fun z :
        (ℕ → ℕ → Ξ) ×
          (ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m)) ×
          (ℕ → EuclideanSpace ℝ (Fin n)) ↦
        (z.2.1, z.2.2.1)) :=
    measurable_snd.fst.prodMk measurable_snd.snd.fst
  unfold pointMultiplierObservable
  simpa only [Function.comp_def, id_eq] using
    (restart.outputIndex_indep_attempt i).comp measurable_id hprojection

/-- Helper for Corollary 4.2: a corrected attempt selector lies almost surely
in the finite support of its prescribed uniform law. -/
private lemma outputIndex_mem_uniformRange
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    ∀ᵐ omega ∂ℙ, restart.outputIndex i omega ∈ Finset.Icc 1 (K - 1) := by
  let p := StochasticRun.UniformOutput.indexLaw K hK
  let s := Finset.Icc 1 (K - 1)
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ s := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hk' : k ∉ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hpZero : p k = 0 := by
      simp only [p, StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk']
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupport' :
      ∀ᵐ k ∂(StochasticRun.UniformOutput.indexLaw K hK).toMeasure,
        k ∈ Finset.Icc 1 (K - 1) := by
    simpa only [p, s] using hpSupport
  exact ((restart.outputIndex_hasLaw i).ae_iff (measurable_of_countable _)).mpr
    hpSupport'

/-- Helper for Corollary 4.2: the selected corrected residual restricted to
trajectory completion, expressed on selector-trajectory data. -/
private noncomputable def restrictedTrajectoryResidualSq
    (h : EqualityConstrained.Regularity f c)
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : ℕ ×
      ((ℕ → EuclideanSpace ℝ (Fin n)) ×
        (ℕ → EuclideanSpace ℝ (Fin m)))) : ℝ≥0∞ :=
  {output | output.1 ∈ Finset.Icc 1 (K - 1) ∧
      ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X}.indicator
    (fun output ↦ ENNReal.ofReal
      (KKT.residualExtension h
        (output.2.1 (output.1 + 1), output.2.2 (output.1 + 1)) ^ 2)) output

/-- Helper for Corollary 4.2: the trajectory-form corrected
success-restricted residual is measurable. -/
private lemma measurableRestrictedTrajectoryResidualSq
    (h : EqualityConstrained.Regularity f c)
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (restrictedTrajectoryResidualSq h K X) := by
  -- Completion is a finite intersection of measurable coordinate events.
  have hcoordinate (j : ℕ) : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) | output.2.1 j ∈ X} :=
    hX.preimage ((measurable_pi_apply j).comp measurable_snd.fst)
  have hsuccess : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) |
        ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
    have hfinite (s : Finset ℕ) : MeasurableSet
        {output : ℕ ×
          ((ℕ → EuclideanSpace ℝ (Fin n)) ×
            (ℕ → EuclideanSpace ℝ (Fin m))) |
          ∀ j ∈ s, output.2.1 j ∈ X} := by
      induction s using Finset.induction with
      | empty =>
          simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
            Set.setOf_true, MeasurableSet.univ]
      | insert a s ha hs =>
          simpa only [Finset.forall_mem_insert, Set.setOf_and] using
            (hcoordinate a).inter hs
    exact hfinite (Finset.Icc 1 K)
  -- Variable-index evaluation is measurable because the selector is countable.
  have hpoint : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.1 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_fst
  have hmultiplier : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.2 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_snd
  have hindex : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) |
        output.1 ∈ Finset.Icc 1 (K - 1)} :=
    (Finset.Icc 1 (K - 1)).measurableSet.preimage measurable_fst
  have hresidual :=
    (KKT.measurable_residualExtension h).comp (hpoint.prodMk hmultiplier)
  unfold restrictedTrajectoryResidualSq
  exact (hresidual.pow_const 2).ennreal_ofReal.indicator (hindex.inter hsuccess)

/-- Helper for Corollary 4.2: evaluating the corrected trajectory normal form
on an actual attempt gives its success-restricted selected residual almost surely. -/
private lemma restrictedTrajectoryResidualSq_actual
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    (fun omega ↦ restrictedTrajectoryResidualSq h K X
        (restart.outputIndex i omega, pointMultiplierObservable restart i omega)) =ᵐ[ℙ]
      fun omega ↦ (restart.successEvent i).indicator
        (selectedAttemptResidualSq restart i) omega := by
  filter_upwards [outputIndex_mem_uniformRange restart i] with omega hindex
  -- The trajectory condition is exactly the public corrected success event.
  have hsuccess :
      (∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j omega ∈ X) ↔
        omega ∈ restart.successEvent i := by
    rw [restart.successEvent_eq_survivalEvent, mem_survivalEvent]
    simp only [Finset.mem_Icc, Set.mem_Icc]
  by_cases homega : omega ∈ restart.successEvent i
  · have hall := hsuccess.mpr homega
    have hselectedIndex : restart.outputIndex i omega + 1 ∈ Finset.Icc 1 K := by
      have hindexBounds := Finset.mem_Icc.mp hindex
      simp only [Finset.mem_Icc]
      omega
    have hselectedRegion :
        (restart.attempt i).point (restart.outputIndex i omega + 1) omega ∈
          h.region :=
      hXregion (hall _ hselectedIndex)
    have hpair :
        (restart.outputIndex i omega, pointMultiplierObservable restart i omega) ∈
          {output : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            output.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using ⟨hindex, hall⟩
    have hextension :
        KKT.residualExtension h
            ((restart.attempt i).point (restart.outputIndex i omega + 1) omega,
              (restart.attempt i).multiplier
                (restart.outputIndex i omega + 1) omega) =
          KKT.residual f c
            ((restart.attempt i).point (restart.outputIndex i omega + 1) omega)
            ((restart.attempt i).multiplier
              (restart.outputIndex i omega + 1) omega) :=
      KKT.residualExtension_eq h hselectedRegion
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_mem hpair, Set.indicator_of_mem homega]
    unfold pointMultiplierObservable selectedAttemptResidualSq
    rw [hextension]
  · have hpair :
        (restart.outputIndex i omega, pointMultiplierObservable restart i omega) ∉
          {output : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            output.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
      intro hall
      apply homega
      apply hsuccess.mp
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using hall.2
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_notMem hpair, Set.indicator_of_notMem homega]

/-- Helper for Corollary 4.2: mapping the right coordinate of a product measure
commutes with a measurable nonnegative integral. -/
private lemma lintegral_prod_map_right
    {E : Type*} [MeasurableSpace E]
    (mu : Measure ℕ) (g : Ω → E) (hg : AEMeasurable g ℙ)
    (F : ℕ × E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂mu.prod (ℙ.map g)) =
      ∫⁻ z, F (z.1, g z.2) ∂mu.prod ℙ := by
  -- Apply Tonelli on both sides and transport every section through `g`.
  have hsection (k : ℕ) :
      AEMeasurable (fun y : E ↦ F (k, y)) (ℙ.map g) :=
    (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hcomposedSection (k : ℕ) :
      AEMeasurable (fun omega ↦ F (k, g omega)) ℙ :=
    (hsection k).comp_aemeasurable hg
  have hcomposed : AEMeasurable
      (fun z : ℕ × Ω ↦ F (z.1, g z.2)) (mu.prod ℙ) :=
    StochasticRun.aemeasurableIndexedProduct mu
      (fun k omega ↦ F (k, g omega)) hcomposedSection
  calc
    (∫⁻ z, F z ∂mu.prod (ℙ.map g)) =
        ∫⁻ k, ∫⁻ y, F (k, y) ∂ℙ.map g ∂mu :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ k, ∫⁻ omega, F (k, g omega) ∂ℙ ∂mu := by
      apply lintegral_congr
      intro k
      exact lintegral_map' (hsection k) hg
    _ = ∫⁻ z, F (z.1, g z.2) ∂mu.prod ℙ :=
      (lintegral_prod _ hcomposed).symm

/-- Helper for Corollary 4.2: the corrected trajectory normal form on the
uniform product space is the terminal-survival restricted residual almost surely. -/
private lemma restrictedTrajectoryResidualSq_reference
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXregion : X ⊆ h.region)
    (run : SPIDER.Correction.ScheduledRun h oracle ℙ x₀ multiplier₀ params K) :
    (fun output : ℕ × Ω ↦ restrictedTrajectoryResidualSq h K X
        (output.1,
          (fun k ↦ run.point k output.2, fun k ↦ run.multiplier k output.2))) =ᵐ[
        StochasticRun.UniformOutput.measure K hK ℙ]
      fun output ↦
        (Set.univ ×ˢ StochasticRun.Localization.survivalEvent run X K).indicator
        (fun output ↦ ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point run output)
            (StochasticRun.UniformOutput.multiplier run output) ^ 2)) output := by
  let p := StochasticRun.UniformOutput.indexLaw K hK
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ Finset.Icc 1 (K - 1) := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hpZero : p k = 0 := by
      simp only [p, StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk]
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod ℙ, output.1 ∈ Finset.Icc 1 (K - 1) :=
    (Measure.quasiMeasurePreserving_fst (μ := p.toMeasure) (ν := ℙ)).ae hpSupport
  change _ =ᵐ[p.toMeasure.prod ℙ] _
  filter_upwards [hpSupportLifted] with output hindex
  -- Both indicators use the same finite corrected point-membership tests.
  have hsuccess :
      (∀ j ∈ Finset.Icc 1 K, run.point j output.2 ∈ X) ↔
        output.2 ∈ StochasticRun.Localization.survivalEvent run X K := by
    rw [StochasticRun.Localization.mem_survivalEvent]
    simp only [Finset.mem_Icc, Set.mem_Icc]
  by_cases homega : output.2 ∈ StochasticRun.Localization.survivalEvent run X K
  · have hall := hsuccess.mpr homega
    have hselectedIndex : output.1 + 1 ∈ Finset.Icc 1 K := by
      have hindexBounds := Finset.mem_Icc.mp hindex
      simp only [Finset.mem_Icc]
      omega
    have hselectedRegion : run.point (output.1 + 1) output.2 ∈ h.region :=
      hXregion (hall _ hselectedIndex)
    have htrajectory :
        (output.1,
          (fun k ↦ run.point k output.2, fun k ↦ run.multiplier k output.2)) ∈
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            z.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      simpa only [Set.mem_setOf_eq] using ⟨hindex, hall⟩
    have hproduct :
        output ∈ Set.univ ×ˢ StochasticRun.Localization.survivalEvent run X K :=
      ⟨Set.mem_univ _, homega⟩
    have hextension :
        KKT.residualExtension h
            (run.point (output.1 + 1) output.2,
              run.multiplier (output.1 + 1) output.2) =
          KKT.residual f c (run.point (output.1 + 1) output.2)
            (run.multiplier (output.1 + 1) output.2) :=
      KKT.residualExtension_eq h hselectedRegion
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_mem htrajectory, Set.indicator_of_mem hproduct,
      StochasticRun.UniformOutput.point_apply,
      StochasticRun.UniformOutput.multiplier_apply, hextension]
  · have htrajectory :
        (output.1,
          (fun k ↦ run.point k output.2, fun k ↦ run.multiplier k output.2)) ∉
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            z.1 ∈ Finset.Icc 1 (K - 1) ∧
              ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      intro hall
      apply homega
      apply hsuccess.mp
      exact hall.2
    have hproduct :
        output ∉ Set.univ ×ˢ StochasticRun.Localization.survivalEvent run X K := by
      intro houtput
      exact homega houtput.2
    unfold restrictedTrajectoryResidualSq
    rw [Set.indicator_of_notMem htrajectory, Set.indicator_of_notMem hproduct]

/-- Helper for Corollary 4.2: a fixed corrected attempt's success-restricted
selected residual has the canonical uniform-product integral. -/
private lemma successRestrictedSelectedResidual_eq
    (K : ℕ) (hK : 2 ≤ K) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    (∫⁻ omega in restart.successEvent i,
        selectedAttemptResidualSq restart i omega ∂ℙ) =
      ∫⁻ output in
          Set.univ ×ˢ StochasticRun.Localization.survivalEvent
            (restart.attempt i) X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point (restart.attempt i) output)
            (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2)
        ∂StochasticRun.UniformOutput.measure K hK ℙ := by
  -- Transport the common trajectory integrand through selector independence.
  let muIndex := (StochasticRun.UniformOutput.indexLaw K hK).toMeasure
  let trajectory := pointMultiplierObservable restart i
  let integrand := restrictedTrajectoryResidualSq h K X
  have htrajectory : AEMeasurable trajectory ℙ :=
    aemeasurablePointMultiplierObservable restart i
  have hintegrand : Measurable integrand :=
    measurableRestrictedTrajectoryResidualSq h K X hX
  have htrajectoryLaw : ProbabilityTheory.HasLaw trajectory (ℙ.map trajectory) ℙ :=
    ⟨htrajectory, rfl⟩
  have hjointLaw : ProbabilityTheory.HasLaw
      (fun omega ↦ (restart.outputIndex i omega, trajectory omega))
      (muIndex.prod (ℙ.map trajectory)) ℙ :=
    (outputIndex_indep_pointMultiplierObservable restart i).hasLaw_prod
      (restart.outputIndex_hasLaw i) htrajectoryLaw
  have hsuccess : NullMeasurableSet (restart.successEvent i) ℙ := by
    rw [restart.successEvent_eq_survivalEvent]
    exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
      (restart.attempt i) X hX K
  have hreferenceSuccess : NullMeasurableSet
      (Set.univ ×ˢ StochasticRun.Localization.survivalEvent
        (restart.attempt i) X K) (muIndex.prod ℙ) :=
    MeasurableSet.univ.nullMeasurableSet.prod
      (StochasticRun.Localization.nullMeasurableSet_survivalEvent
        (restart.attempt i) X hX K)
  calc
    (∫⁻ omega in restart.successEvent i,
        selectedAttemptResidualSq restart i omega ∂ℙ) =
        ∫⁻ omega, (restart.successEvent i).indicator
          (selectedAttemptResidualSq restart i) omega ∂ℙ :=
      (lintegral_indicator₀ hsuccess _).symm
    _ = ∫⁻ omega,
        integrand (restart.outputIndex i omega, trajectory omega) ∂ℙ := by
      exact lintegral_congr_ae
        (restrictedTrajectoryResidualSq_actual hXregion restart i).symm
    _ = ∫⁻ z, integrand z ∂muIndex.prod (ℙ.map trajectory) :=
      hjointLaw.lintegral_comp hintegrand.aemeasurable
    _ = ∫⁻ z, integrand (z.1, trajectory z.2) ∂muIndex.prod ℙ :=
      lintegral_prod_map_right muIndex trajectory htrajectory integrand hintegrand
    _ = ∫⁻ output,
        (Set.univ ×ˢ StochasticRun.Localization.survivalEvent
          (restart.attempt i) X K).indicator
          (fun output ↦ ENNReal.ofReal
            (KKT.residual f c
              (StochasticRun.UniformOutput.point (restart.attempt i) output)
              (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2))
          output ∂muIndex.prod ℙ := by
      exact lintegral_congr_ae
        (restrictedTrajectoryResidualSq_reference K hK X hXregion
          (restart.attempt i))
    _ = ∫⁻ output in
        Set.univ ×ˢ StochasticRun.Localization.survivalEvent
          (restart.attempt i) X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point (restart.attempt i) output)
            (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2)
        ∂muIndex.prod ℙ :=
      lintegral_indicator₀ hreferenceSuccess _
    _ = ∫⁻ output in
        Set.univ ×ˢ StochasticRun.Localization.survivalEvent
          (restart.attempt i) X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point (restart.attempt i) output)
            (StochasticRun.UniformOutput.multiplier (restart.attempt i) output) ^ 2)
        ∂StochasticRun.UniformOutput.measure K hK ℙ := by
      rfl

/-- Helper for Corollary 4.2: every fixed corrected attempt satisfies the
success-restricted residual estimate used by the first-success mixture. -/
private lemma successRestrictedSelectedResidual_le
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) (i : ℕ) :
    (∫⁻ omega in restart.successEvent i,
        selectedAttemptResidualSq restart i omega ∂ℙ) ≤
      ℙ (restart.successEvent i) *
        ENNReal.ofReal (stochasticComplexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
  -- Bound the raw numerator, then insert the certified survival probability.
  let run := restart.attempt i
  let S := StochasticRun.Localization.survivalEvent run X K
  let C := stochasticComplexityConstant h oracle params
  let bound := ENNReal.ofReal (C / ((1 - confidence) * ((K : ℝ) - 1)))
  have hXregion : X ⊆ h.region := by
    intro x hx
    exact h_region.thickening_subset (Metric.self_subset_cthickening X hx)
  have htransport :
      (∫⁻ omega in restart.successEvent i,
          selectedAttemptResidualSq restart i omega ∂ℙ) =
        ∫⁻ output in Set.univ ×ˢ S,
          ENNReal.ofReal
            (KKT.residual f c
              (StochasticRun.UniformOutput.point run output)
              (StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂StochasticRun.UniformOutput.measure K hK ℙ := by
    exact successRestrictedSelectedResidual_eq K hK X hX hXregion restart i
  have hnumerator :
      (∫⁻ output in Set.univ ×ˢ S,
          ENNReal.ofReal
            (KKT.residual f c
              (StochasticRun.UniformOutput.point run output)
              (StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂StochasticRun.UniformOutput.measure K hK ℙ) ≤
        ENNReal.ofReal (C / ((K : ℝ) - 1)) := by
    exact StochasticRun.UniformOutput.survivalRestrictedResidualLIntegral_le
      K hK confidence X hX initial_mem run h_region
  have hsurvival : ENNReal.ofReal (1 - confidence) ≤ ℙ S :=
    StochasticRun.Localization.survivalProbability_ge K hK confidence
      confidence_pos X hX initial_mem run h_region
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnat
  have hdenominator : 0 < (K : ℝ) - 1 := by
    exact sub_pos.mpr hKreal
  have honeMinus : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hnormalize :
      ENNReal.ofReal (C / ((K : ℝ) - 1)) =
        ENNReal.ofReal (1 - confidence) * bound := by
    rw [← ENNReal.ofReal_mul honeMinus.le]
    congr 1
    field_simp [honeMinus.ne', hdenominator.ne']
  calc
    (∫⁻ omega in restart.successEvent i,
        selectedAttemptResidualSq restart i omega ∂ℙ) =
        ∫⁻ output in Set.univ ×ˢ S,
          ENNReal.ofReal
            (KKT.residual f c
              (StochasticRun.UniformOutput.point run output)
              (StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂StochasticRun.UniformOutput.measure K hK ℙ := htransport
    _ ≤ ENNReal.ofReal (C / ((K : ℝ) - 1)) := hnumerator
    _ = ENNReal.ofReal (1 - confidence) * bound := hnormalize
    _ ≤ ℙ S * bound := by
      simpa only [mul_comm] using mul_le_mul_left hsurvival bound
    _ = ℙ (restart.successEvent i) *
        ENNReal.ofReal (stochasticComplexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
      rw [restart.successEvent_eq_survivalEvent]

/-- Helper for Corollary 4.2: the indicator that a corrected trajectory
completes every localization test. -/
private noncomputable def trajectorySuccessWeight
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : ℕ ×
      ((ℕ → EuclideanSpace ℝ (Fin n)) ×
        (ℕ → EuclideanSpace ℝ (Fin m)))) : ℝ≥0∞ :=
  {z | ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X}.indicator (fun _ ↦ 1) output

/-- Helper for Corollary 4.2: the corrected trajectory success indicator is
measurable. -/
private lemma measurableTrajectorySuccessWeight
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (trajectorySuccessWeight (n := n) (m := m) K X) := by
  -- Express completion as a finite intersection of coordinate events.
  have hcoordinate (j : ℕ) : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) | output.2.1 j ∈ X} :=
    hX.preimage ((measurable_pi_apply j).comp measurable_snd.fst)
  have hsuccess : MeasurableSet
      {output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) |
        ∀ j ∈ Finset.Icc 1 K, output.2.1 j ∈ X} := by
    induction Finset.Icc 1 K using Finset.induction with
    | empty =>
        simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          Set.setOf_true, MeasurableSet.univ]
    | insert a s ha hs =>
        simpa only [Finset.forall_mem_insert, Set.setOf_and] using
          (hcoordinate a).inter hs
  unfold trajectorySuccessWeight
  exact measurable_const.indicator hsuccess

/-- Helper for Corollary 4.2: trajectory completion evaluated on a corrected
attempt is its public success-event indicator. -/
private lemma trajectorySuccessWeight_actual
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) :
    trajectorySuccessWeight (n := n) (m := m) K X
        (restart.outputIndex i omega, pointMultiplierObservable restart i omega) =
      (restart.successEvent i).indicator (fun _ ↦ (1 : ℝ≥0∞)) omega := by
  -- Both indicators encode the same finite family of point-membership tests.
  have hsuccess :
      (∀ j ∈ Finset.Icc 1 K, (restart.attempt i).point j omega ∈ X) ↔
        omega ∈ restart.successEvent i := by
    rw [restart.successEvent_eq_survivalEvent, mem_survivalEvent]
    simp only [Finset.mem_Icc, Set.mem_Icc]
  by_cases homega : omega ∈ restart.successEvent i
  · have htrajectory :
        (restart.outputIndex i omega, pointMultiplierObservable restart i omega) ∈
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using
        hsuccess.mpr homega
    unfold trajectorySuccessWeight
    rw [Set.indicator_of_mem htrajectory, Set.indicator_of_mem homega]
  · have htrajectory :
        (restart.outputIndex i omega, pointMultiplierObservable restart i omega) ∉
          {z : ℕ ×
            ((ℕ → EuclideanSpace ℝ (Fin n)) ×
              (ℕ → EuclideanSpace ℝ (Fin m))) |
            ∀ j ∈ Finset.Icc 1 K, z.2.1 j ∈ X} := by
      intro hall
      apply homega
      apply hsuccess.mp
      simpa only [Set.mem_setOf_eq, pointMultiplierObservable] using hall
    unfold trajectorySuccessWeight
    rw [Set.indicator_of_notMem htrajectory, Set.indicator_of_notMem homega]

/-- Helper for Corollary 4.2: one corrected attempt exposes its success weight
and success-restricted selected residual together. -/
private noncomputable def successResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) : ℝ≥0∞ × ℝ≥0∞ :=
  ((restart.successEvent i).indicator (fun _ ↦ 1) omega,
    (restart.successEvent i).indicator (selectedAttemptResidualSq restart i) omega)

/-- Helper for Corollary 4.2: every corrected success-residual attempt
observable is almost-everywhere measurable. -/
private lemma aemeasurableSuccessResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (successResidualObservable restart i) ℙ := by
  -- Use the trajectory normal form for the residual coordinate.
  have hsuccess : NullMeasurableSet (restart.successEvent i) ℙ := by
    rw [restart.successEvent_eq_survivalEvent]
    exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
      (restart.attempt i) X hX K
  have hjoint : AEMeasurable
      (fun omega ↦ (restart.outputIndex i omega,
        pointMultiplierObservable restart i omega)) ℙ :=
    (restart.outputIndex_hasLaw i).aemeasurable.prodMk
      (aemeasurablePointMultiplierObservable restart i)
  have hrestricted : AEMeasurable
      (fun omega ↦ (restart.successEvent i).indicator
        (selectedAttemptResidualSq restart i) omega) ℙ :=
    ((measurableRestrictedTrajectoryResidualSq h K X hX).comp_aemeasurable
      hjoint).congr (restrictedTrajectoryResidualSq_actual hXregion restart i)
  unfold successResidualObservable
  exact (aemeasurable_const.indicator₀ hsuccess).prodMk hrestricted

/-- Helper for Corollary 4.2: corrected attemptwise success-residual
observables are mutually independent. -/
private lemma iIndepFun_successResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X) :
    ProbabilityTheory.iIndepFun (fun i ↦ successResidualObservable restart i) ℙ := by
  -- Project and summarize each complete corrected attempt record measurably.
  let projectAttempt := fun z : AttemptObservable Ξ n m ↦
    (z.1, (z.2.2.1, z.2.2.2.1))
  let summarizeAttempt := fun z : ℕ ×
      ((ℕ → EuclideanSpace ℝ (Fin n)) ×
        (ℕ → EuclideanSpace ℝ (Fin m))) ↦
    (trajectorySuccessWeight (n := n) (m := m) K X z,
      restrictedTrajectoryResidualSq h K X z)
  have hproject : Measurable projectAttempt :=
    measurable_fst.prodMk
      (measurable_snd.snd.fst.prodMk measurable_snd.snd.snd.fst)
  have hsummarize : Measurable summarizeAttempt :=
    (measurableTrajectorySuccessWeight K X hX).prodMk
      (measurableRestrictedTrajectoryResidualSq h K X hX)
  have hindependent := restart.independent_attempt.comp
    (fun _ ↦ summarizeAttempt ∘ projectAttempt)
    (fun _ ↦ hsummarize.comp hproject)
  refine hindependent.congr fun i ↦ ?_
  filter_upwards [restrictedTrajectoryResidualSq_actual hXregion restart i] with
    omega hresidual
  -- The two computation lemmas recover the public attempt observable.
  simp only [Function.comp_apply, projectAttempt, summarizeAttempt]
  apply Prod.ext
  · exact trajectorySuccessWeight_actual restart i omega
  · exact hresidual

/-- Helper for Corollary 4.2: the event that every corrected attempt before
`i` fails. -/
private def priorFailureEvent
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range i, (restart.successEvent j)ᶜ

/-- Helper for Corollary 4.2: a finite corrected first-acceptance fiber is the
intersection of all prior failures with current success. -/
private lemma firstAcceptedFiber_eq
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    {omega | restart.firstAccepted omega = (i : ℕ∞)} =
      priorFailureEvent restart i ∩ restart.successEvent i := by
  -- Rewrite the public hitting-time characterization as a finite intersection.
  ext omega
  rw [Set.mem_setOf_eq, restart.firstAccepted_eq_coe_iff]
  simp only [priorFailureEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Finset.mem_range]
  tauto

/-- Helper for Corollary 4.2: the indicator that every first coordinate of a
finite family vanishes. -/
private noncomputable def allFirstCoordinatesZeroWeight
    {ι : Type*} (z : ι → ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  {z | ∀ j, (z j).1 = 0}.indicator (fun _ ↦ 1) z

/-- Helper for Corollary 4.2: the finite all-zero weight is measurable. -/
private lemma measurableAllFirstCoordinatesZeroWeight
    {ι : Type*} [Finite ι] :
    Measurable (allFirstCoordinatesZeroWeight (ι := ι)) := by
  -- The all-zero locus is a finite intersection of coordinate fibers.
  have hcoordinate (j : ι) : Measurable
      (fun z : ι → ℝ≥0∞ × ℝ≥0∞ ↦ (z j).1) :=
    measurable_fst.comp (measurable_pi_apply j)
  unfold allFirstCoordinatesZeroWeight
  apply measurable_const.indicator
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun j ↦
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage (hcoordinate j)

/-- Helper for Corollary 4.2: the indicator of failure of every corrected
attempt before `i`. -/
private noncomputable def priorFailureWeight
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) : ℝ≥0∞ :=
  (priorFailureEvent restart i).indicator (fun _ ↦ 1) omega

/-- Helper for Corollary 4.2: the finite all-zero attempt weight equals the
public corrected prior-failure indicator. -/
private lemma allFirstCoordinatesZeroWeight_attempts
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) :
    allFirstCoordinatesZeroWeight
        (fun j : ↑(Finset.range i) ↦ successResidualObservable restart j omega) =
      priorFailureWeight restart i omega := by
  -- Compare both indicators through failure of every earlier attempt.
  classical
  by_cases hprior : omega ∈ priorFailureEvent restart i
  · have hfail : ∀ j ∈ Finset.range i, omega ∉ restart.successEvent j := by
      simpa only [priorFailureEvent, Set.mem_iInter, Set.mem_compl_iff] using hprior
    have hsummary :
        (fun j : ↑(Finset.range i) ↦ successResidualObservable restart j omega) ∈
          {z | ∀ j, (z j).1 = 0} := by
      intro j
      unfold successResidualObservable
      change (restart.successEvent j).indicator (fun _ ↦ (1 : ℝ≥0∞)) omega = 0
      rw [Set.indicator_of_notMem (hfail j j.property)]
    unfold allFirstCoordinatesZeroWeight priorFailureWeight
    rw [Set.indicator_of_mem hsummary, Set.indicator_of_mem hprior]
  · have hsummary :
        (fun j : ↑(Finset.range i) ↦ successResidualObservable restart j omega) ∉
          {z | ∀ j, (z j).1 = 0} := by
      intro hall
      apply hprior
      simp only [priorFailureEvent, Set.mem_iInter, Set.mem_compl_iff]
      intro j hj hsuccess
      have hzero := hall ⟨j, hj⟩
      unfold successResidualObservable at hzero
      change (restart.successEvent j).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) omega = 0 at hzero
      rw [Set.indicator_of_mem hsuccess] at hzero
      exact one_ne_zero hzero
    unfold allFirstCoordinatesZeroWeight priorFailureWeight
    rw [Set.indicator_of_notMem hsummary, Set.indicator_of_notMem hprior]

/-- Helper for Corollary 4.2: the corrected prior-failure weight is independent
of the current attempt's success-residual observable. -/
private lemma priorFailureWeight_indep_successResidualObservable
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : ProbabilityTheory.IndepFun (priorFailureWeight restart i)
      (successResidualObservable restart i) ℙ := by
  -- Split mutual independence into the strict prefix and current singleton.
  classical
  have hdisjoint : Disjoint (Finset.range i) {i} := by simp
  have htuple :=
    (iIndepFun_successResidualObservable hX hXregion restart).indepFun_finset₀
    (Finset.range i) {i} hdisjoint
      (aemeasurableSuccessResidualObservable hX hXregion restart)
  have hprojected := htuple.comp
    measurableAllFirstCoordinatesZeroWeight
    (measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩)
  refine hprojected.congr ?_ ?_
  · exact Filter.Eventually.of_forall fun omega ↦
      allFirstCoordinatesZeroWeight_attempts restart i omega
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Helper for Corollary 4.2: the corrected prior-failure event is
null-measurable. -/
private lemma nullMeasurableSetPriorFailureEvent
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : NullMeasurableSet (priorFailureEvent restart i) ℙ := by
  -- Each earlier failure complements a corrected localization survival event.
  unfold priorFailureEvent
  apply (Finset.range i).nullMeasurableSet_biInter
  intro j hj
  rw [restart.successEvent_eq_survivalEvent]
  exact (StochasticRun.Localization.nullMeasurableSet_survivalEvent
    (restart.attempt j) X hX K).compl

/-- Helper for Corollary 4.2: every finite corrected first-acceptance fiber is
null-measurable. -/
private lemma nullMeasurableSetFirstAcceptedFiber
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) :
    NullMeasurableSet {omega | restart.firstAccepted omega = (i : ℕ∞)} ℙ := by
  -- Use the prior-failure/current-success normal form.
  rw [firstAcceptedFiber_eq restart i]
  refine (nullMeasurableSetPriorFailureEvent hX restart i).inter ?_
  rw [restart.successEvent_eq_survivalEvent]
  exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
    (restart.attempt i) X hX K

/-- Helper for Corollary 4.2: on a finite first-acceptance fiber, the returned
corrected residual is the residual selected in that attempt. -/
private lemma returnedResidualSq_eq_selectedAttempt_onFiber
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω)
    (hfirst : restart.firstAccepted omega = (i : ℕ∞)) :
    ENNReal.ofReal
        (KKT.residual f c (restart.returnedPoint omega)
          (restart.returnedMultiplier omega) ^ 2) =
      selectedAttemptResidualSq restart i omega := by
  -- Normalize the defaulted finite index through the fiber equality.
  have hindex : (restart.firstAccepted omega).untopD 0 = i := by
    rw [hfirst]
    rfl
  rw [restart.returnedPoint_apply, restart.returnedMultiplier_apply]
  unfold selectedAttemptResidualSq
  rw [hindex]

/-- Helper for Corollary 4.2: prior failure times current success is the
indicator of the corresponding corrected first-acceptance fiber. -/
private lemma priorFailureWeight_mul_successWeight
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) :
    priorFailureWeight restart i omega *
        (successResidualObservable restart i omega).1 =
      {omega | restart.firstAccepted omega = (i : ℕ∞)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) omega := by
  -- Resolve both event indicators through the fiber intersection.
  change priorFailureWeight restart i omega *
      (restart.successEvent i).indicator (fun _ ↦ (1 : ℝ≥0∞)) omega = _
  by_cases hprior : omega ∈ priorFailureEvent restart i
  · by_cases hsuccess : omega ∈ restart.successEvent i
    · have hfiber :
          omega ∈ {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
    · have hnotFiber :
          omega ∉ {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber :
        omega ∉ {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
      rw [firstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 4.2: prior failure times the current restricted
residual is the returned residual restricted to that corrected fiber. -/
private lemma priorFailureWeight_mul_successResidual
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) :
    priorFailureWeight restart i omega *
        (successResidualObservable restart i omega).2 =
      {omega | restart.firstAccepted omega = (i : ℕ∞)}.indicator
        (fun omega ↦ ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint omega)
            (restart.returnedMultiplier omega) ^ 2)) omega := by
  -- On the fiber identify the returned attempt; off it one factor is zero.
  change priorFailureWeight restart i omega *
      (restart.successEvent i).indicator
        (selectedAttemptResidualSq restart i) omega = _
  by_cases hprior : omega ∈ priorFailureEvent restart i
  · by_cases hsuccess : omega ∈ restart.successEvent i
    · have hfiber :
          omega ∈ {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
      exact (returnedResidualSq_eq_selectedAttempt_onFiber
        restart i omega hfiber).symm
    · have hnotFiber :
          omega ∉ {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
        rw [firstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber :
        omega ∉ {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
      rw [firstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 4.2: a corrected success-restricted attempt bound
transfers to its first-acceptance fiber. -/
private lemma firstAcceptedFiberResidual_le
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (bound : ℝ≥0∞)
    (hfixed :
      (∫⁻ omega in restart.successEvent i,
          selectedAttemptResidualSq restart i omega ∂ℙ) ≤
        ℙ (restart.successEvent i) * bound) :
    (∫⁻ omega in {omega | restart.firstAccepted omega = (i : ℕ∞)},
        ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint omega)
            (restart.returnedMultiplier omega) ^ 2) ∂ℙ) ≤
      ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)} * bound := by
  -- Factor prior failure from current success and residual using independence.
  have hpriorNull := nullMeasurableSetPriorFailureEvent hX restart i
  have hfiberNull := nullMeasurableSetFirstAcceptedFiber hX restart i
  have hsuccessNull : NullMeasurableSet (restart.successEvent i) ℙ := by
    rw [restart.successEvent_eq_survivalEvent]
    exact StochasticRun.Localization.nullMeasurableSet_survivalEvent
      (restart.attempt i) X hX K
  have hpriorMeas : AEMeasurable (priorFailureWeight restart i) ℙ := by
    unfold priorFailureWeight
    exact aemeasurable_const.indicator₀ hpriorNull
  have hcurrentMeas :=
    aemeasurableSuccessResidualObservable hX hXregion restart i
  have hindependent :=
    priorFailureWeight_indep_successResidualObservable hX hXregion restart i
  have hfactorResidual :
      (∫⁻ omega, priorFailureWeight restart i omega *
          (successResidualObservable restart i omega).2 ∂ℙ) =
        (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
          ∫⁻ omega, (successResidualObservable restart i omega).2 ∂ℙ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.snd
        (hindependent.comp measurable_id measurable_snd)
  have hfactorSuccess :
      (∫⁻ omega, priorFailureWeight restart i omega *
          (successResidualObservable restart i omega).1 ∂ℙ) =
        (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
          ∫⁻ omega, (successResidualObservable restart i omega).1 ∂ℙ :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.fst
        (hindependent.comp measurable_id measurable_fst)
  have hcurrentResidualIntegral :
      (∫⁻ omega, (successResidualObservable restart i omega).2 ∂ℙ) =
        ∫⁻ omega in restart.successEvent i,
          selectedAttemptResidualSq restart i omega ∂ℙ := by
    unfold successResidualObservable
    exact lintegral_indicator₀ hsuccessNull _
  have hcurrentSuccessIntegral :
      (∫⁻ omega, (successResidualObservable restart i omega).1 ∂ℙ) =
        ℙ (restart.successEvent i) := by
    unfold successResidualObservable
    exact lintegral_indicator_one₀ hsuccessNull
  have hmeasureFiber :
      ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)} =
        (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
          ℙ (restart.successEvent i) := by
    calc
      ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)} =
          ∫⁻ omega,
            {omega | restart.firstAccepted omega = (i : ℕ∞)}.indicator
              (fun _ ↦ (1 : ℝ≥0∞)) omega ∂ℙ :=
        (lintegral_indicator_one₀ hfiberNull).symm
      _ = ∫⁻ omega, priorFailureWeight restart i omega *
          (successResidualObservable restart i omega).1 ∂ℙ := by
        apply lintegral_congr
        intro omega
        exact (priorFailureWeight_mul_successWeight restart i omega).symm
      _ = (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
          ∫⁻ omega, (successResidualObservable restart i omega).1 ∂ℙ :=
        hfactorSuccess
      _ = (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
          ℙ (restart.successEvent i) := by
        rw [hcurrentSuccessIntegral]
  -- Apply the fixed numerator estimate between the two factorizations.
  calc
    (∫⁻ omega in {omega | restart.firstAccepted omega = (i : ℕ∞)},
        ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint omega)
            (restart.returnedMultiplier omega) ^ 2) ∂ℙ) =
        ∫⁻ omega,
          {omega | restart.firstAccepted omega = (i : ℕ∞)}.indicator
            (fun omega ↦ ENNReal.ofReal
              (KKT.residual f c (restart.returnedPoint omega)
                (restart.returnedMultiplier omega) ^ 2)) omega ∂ℙ :=
      (lintegral_indicator₀ hfiberNull _).symm
    _ = ∫⁻ omega, priorFailureWeight restart i omega *
        (successResidualObservable restart i omega).2 ∂ℙ := by
      apply lintegral_congr
      intro omega
      exact (priorFailureWeight_mul_successResidual restart i omega).symm
    _ = (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
        ∫⁻ omega, (successResidualObservable restart i omega).2 ∂ℙ :=
      hfactorResidual
    _ = (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
        (∫⁻ omega in restart.successEvent i,
          selectedAttemptResidualSq restart i omega ∂ℙ) := by
      rw [hcurrentResidualIntegral]
    _ ≤ (∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
        (ℙ (restart.successEvent i) * bound) :=
      mul_le_mul_right hfixed _
    _ = ((∫⁻ omega, priorFailureWeight restart i omega ∂ℙ) *
        ℙ (restart.successEvent i)) * bound :=
      (mul_assoc _ _ _).symm
    _ = ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)} * bound := by
      rw [← hmeasureFiber]

/-- Helper for Corollary 4.2: uniform corrected success-restricted bounds pass
through the almost-surely terminating first-success mixture. -/
private lemma residualMeanSquare_le_of_successRestricted
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (hXregion : X ⊆ h.region)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (bound : ℝ≥0∞)
    (htermination : ∀ᵐ omega ∂ℙ, restart.firstAccepted omega ≠ ⊤)
    (hfixed : ∀ i,
      (∫⁻ omega in restart.successEvent i,
          selectedAttemptResidualSq restart i omega ∂ℙ) ≤
        ℙ (restart.successEvent i) * bound) :
    KKT.Stochastic.residualMeanSquare ℙ f c
      restart.returnedPoint restart.returnedMultiplier ≤ bound := by
  -- Finite first-acceptance fibers are pairwise disjoint.
  have hdisjoint : Pairwise fun i j : ℕ ↦
      Disjoint {omega | restart.firstAccepted omega = (i : ℕ∞)}
        {omega | restart.firstAccepted omega = (j : ℕ∞)} := by
    intro i j hij
    rw [Set.disjoint_left]
    intro omega hi hj
    apply hij
    apply ENat.coe_inj.mp
    exact hi.symm.trans hj
  have haedisjoint : Pairwise fun i j : ℕ ↦
      AEDisjoint ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)}
        {omega | restart.firstAccepted omega = (j : ℕ∞)} :=
    hdisjoint.aedisjoint
  have hfiberNull (i : ℕ) :
      NullMeasurableSet
        {omega | restart.firstAccepted omega = (i : ℕ∞)} ℙ :=
    nullMeasurableSetFirstAcceptedFiber hX restart i
  -- Almost-sure termination makes the union of finite fibers conull.
  have hunionAE : ∀ᵐ omega ∂ℙ,
      omega ∈ ⋃ i : ℕ,
        {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
    filter_upwards [htermination] with omega hfinite
    obtain ⟨i, hi⟩ :
        ∃ i : ℕ, restart.firstAccepted omega = (i : ℕ∞) := by
      cases hvalue : restart.firstAccepted omega using ENat.recTopCoe with
      | top => exact False.elim (hfinite hvalue)
      | coe i => exact ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hunionMeasure :
      ℙ (⋃ i : ℕ,
        {omega | restart.firstAccepted omega = (i : ℕ∞)}) = 1 := by
    calc
      ℙ (⋃ i : ℕ,
          {omega | restart.firstAccepted omega = (i : ℕ∞)}) =
          ℙ Set.univ :=
        measure_congr (Filter.eventuallyEq_univ.mpr hunionAE)
      _ = 1 := measure_univ
  -- Decompose the residual integral over the conull disjoint union.
  calc
    KKT.Stochastic.residualMeanSquare ℙ f c
        restart.returnedPoint restart.returnedMultiplier =
        ∫⁻ omega, ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint omega)
            (restart.returnedMultiplier omega) ^ 2) ∂ℙ := by
      rw [KKT.Stochastic.residualMeanSquare_def]
    _ = ∫⁻ omega in
          ⋃ i : ℕ, {omega | restart.firstAccepted omega = (i : ℕ∞)},
        ENNReal.ofReal
          (KKT.residual f c (restart.returnedPoint omega)
            (restart.returnedMultiplier omega) ^ 2) ∂ℙ := by
      rw [Measure.restrict_eq_self_of_ae_mem hunionAE]
    _ = ∑' i : ℕ,
        ∫⁻ omega in {omega | restart.firstAccepted omega = (i : ℕ∞)},
          ENNReal.ofReal
            (KKT.residual f c (restart.returnedPoint omega)
              (restart.returnedMultiplier omega) ^ 2) ∂ℙ :=
      lintegral_iUnion₀ hfiberNull haedisjoint _
    _ ≤ ∑' i : ℕ,
        ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)} * bound :=
      ENNReal.tsum_le_tsum fun i ↦
        firstAcceptedFiberResidual_le hX hXregion restart i bound (hfixed i)
    _ = (∑' i : ℕ,
        ℙ {omega | restart.firstAccepted omega = (i : ℕ∞)}) * bound :=
      ENNReal.tsum_mul_right
    _ = ℙ (⋃ i : ℕ,
        {omega | restart.firstAccepted omega = (i : ℕ∞)}) * bound := by
      rw [measure_iUnion₀ haedisjoint hfiberNull]
    _ = 1 * bound := by rw [hunionMeasure]
    _ = bound := one_mul bound

/-- Helper for Corollary 4.2: the primal point selected inside one fixed
corrected attempt. -/
private noncomputable def selectedAttemptPoint
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin n) :=
  (restart.attempt i).point (restart.outputIndex i omega + 1) omega

/-- Helper for Corollary 4.2: the multiplier selected inside one fixed
corrected attempt. -/
private noncomputable def selectedAttemptMultiplier
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) (omega : Ω) : EuclideanSpace ℝ (Fin m) :=
  (restart.attempt i).multiplier (restart.outputIndex i omega + 1) omega

/-- Helper for Corollary 4.2: a fixed corrected attempt's selected primal
point is almost-everywhere measurable. -/
private lemma aemeasurableSelectedAttemptPoint
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (selectedAttemptPoint restart i) ℙ := by
  -- Evaluate the measurable point trajectory at the independent countable selector.
  have hjoint : AEMeasurable
      (fun omega ↦ (restart.outputIndex i omega,
        pointMultiplierObservable restart i omega)) ℙ :=
    (restart.outputIndex_hasLaw i).aemeasurable.prodMk
      (aemeasurablePointMultiplierObservable restart i)
  have hevaluate : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.1 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_fst
  unfold selectedAttemptPoint
  exact hevaluate.comp_aemeasurable hjoint

/-- Helper for Corollary 4.2: a fixed corrected attempt's selected multiplier
is almost-everywhere measurable. -/
private lemma aemeasurableSelectedAttemptMultiplier
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (i : ℕ) : AEMeasurable (selectedAttemptMultiplier restart i) ℙ := by
  -- Evaluate the measurable multiplier trajectory at the same selector.
  have hjoint : AEMeasurable
      (fun omega ↦ (restart.outputIndex i omega,
        pointMultiplierObservable restart i omega)) ℙ :=
    (restart.outputIndex_hasLaw i).aemeasurable.prodMk
      (aemeasurablePointMultiplierObservable restart i)
  have hevaluate : Measurable
      (fun output : ℕ ×
        ((ℕ → EuclideanSpace ℝ (Fin n)) ×
          (ℕ → EuclideanSpace ℝ (Fin m))) ↦
        output.2.2 (output.1 + 1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply (k + 1)).comp measurable_snd
  unfold selectedAttemptMultiplier
  exact hevaluate.comp_aemeasurable hjoint

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: almost-everywhere measurable functions on a
countable null-measurable conull partition glue to a global function. -/
private lemma aemeasurable_of_eq_on_countable_partition
    {E : Type*} [MeasurableSpace E]
    (sets : ℕ → Set Ω) (hsets : ∀ i, NullMeasurableSet (sets i) ℙ)
    (hcover : ∀ᵐ omega ∂ℙ, omega ∈ ⋃ i, sets i)
    (selected : ℕ → Ω → E) (returned : Ω → E)
    (hselected : ∀ i, AEMeasurable (selected i) ℙ)
    (heq : ∀ i omega, omega ∈ sets i → returned omega = selected i omega) :
    AEMeasurable returned ℙ := by
  -- Glue on each restricted fiber and then replace the conull union restriction.
  have hrestricted : AEMeasurable returned (ℙ.restrict (⋃ i, sets i)) := by
    rw [aemeasurable_iUnion_iff]
    intro i
    have hselectedRestricted :
        AEMeasurable (selected i) (ℙ.restrict (sets i)) :=
      (hselected i).mono_measure Measure.restrict_le_self
    have heqAE : selected i =ᵐ[ℙ.restrict (sets i)] returned :=
      (ae_restrict_mem₀ (hsets i)).mono fun omega homega ↦
        (heq i omega homega).symm
    exact hselectedRestricted.congr heqAE
  have hmeasure : ℙ.restrict (⋃ i, sets i) = ℙ :=
    Measure.restrict_eq_self_of_ae_mem hcover
  rwa [hmeasure] at hrestricted

/-- Helper for Corollary 4.2: almost-sure termination makes the union of all
finite corrected first-acceptance fibers conull. -/
private lemma firstAcceptedFiberUnion_ae
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (htermination : ∀ᵐ omega ∂ℙ, restart.firstAccepted omega ≠ ⊤) :
    ∀ᵐ omega ∂ℙ,
      omega ∈ ⋃ i : ℕ, {omega | restart.firstAccepted omega = (i : ℕ∞)} := by
  -- Every non-top extended natural is the coercion of a natural index.
  filter_upwards [htermination] with omega hfinite
  cases hvalue : restart.firstAccepted omega using ENat.recTopCoe with
  | top => exact False.elim (hfinite hvalue)
  | coe i => exact Set.mem_iUnion.mpr ⟨i, hvalue⟩

/-- Helper for Corollary 4.2: the returned corrected primal point is
almost-everywhere measurable under almost-sure termination. -/
private lemma aemeasurableReturnedPoint
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (htermination : ∀ᵐ omega ∂ℙ, restart.firstAccepted omega ≠ ⊤) :
    AEMeasurable restart.returnedPoint ℙ := by
  -- Glue the fixed-attempt selected points over the first-acceptance fibers.
  let sets : ℕ → Set Ω := fun i ↦
    {omega | restart.firstAccepted omega = (i : ℕ∞)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) ℙ :=
    nullMeasurableSetFirstAcceptedFiber hX restart i
  have hcover : ∀ᵐ omega ∂ℙ, omega ∈ ⋃ i, sets i :=
    firstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (omega : Ω) (homega : omega ∈ sets i) :
      restart.returnedPoint omega = selectedAttemptPoint restart i omega := by
    have hindex : (restart.firstAccepted omega).untopD 0 = i := by
      rw [homega]
      rfl
    rw [restart.returnedPoint_apply]
    unfold selectedAttemptPoint
    rw [hindex]
  exact aemeasurable_of_eq_on_countable_partition sets hsets hcover
    (selectedAttemptPoint restart) restart.returnedPoint
    (aemeasurableSelectedAttemptPoint restart) heq

/-- Helper for Corollary 4.2: the returned corrected multiplier is
almost-everywhere measurable under almost-sure termination. -/
private lemma aemeasurableReturnedMultiplier
    {K : ℕ} {hK : 2 ≤ K} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : MeasurableSet X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (htermination : ∀ᵐ omega ∂ℙ, restart.firstAccepted omega ≠ ⊤) :
    AEMeasurable restart.returnedMultiplier ℙ := by
  -- Glue the fixed-attempt selected multipliers over the same fibers.
  let sets : ℕ → Set Ω := fun i ↦
    {omega | restart.firstAccepted omega = (i : ℕ∞)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) ℙ :=
    nullMeasurableSetFirstAcceptedFiber hX restart i
  have hcover : ∀ᵐ omega ∂ℙ, omega ∈ ⋃ i, sets i :=
    firstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (omega : Ω) (homega : omega ∈ sets i) :
      restart.returnedMultiplier omega =
        selectedAttemptMultiplier restart i omega := by
    have hindex : (restart.firstAccepted omega).untopD 0 = i := by
      rw [homega]
      rfl
    rw [restart.returnedMultiplier_apply]
    unfold selectedAttemptMultiplier
    rw [hindex]
  exact aemeasurable_of_eq_on_countable_partition sets hsets hcover
    (selectedAttemptMultiplier restart) restart.returnedMultiplier
    (aemeasurableSelectedAttemptMultiplier restart) heq

/-- Helper for Corollary 4.2: the first accepted corrected pair is measurable
and inherits the uniform successful-attempt residual bound. -/
theorem returnedPairResidualBounds
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X) :
    AEMeasurable restart.returnedPoint ℙ ∧
      AEMeasurable restart.returnedMultiplier ℙ ∧
      KKT.Stochastic.residualMeanSquare ℙ f c
          restart.returnedPoint restart.returnedMultiplier ≤
        ENNReal.ofReal (stochasticComplexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
  -- Termination glues output measurability and closes the first-success mixture.
  have htermination := terminatesAE confidence confidence_pos confidence_lt_one
    hX initial_mem restart h_region
  have hXregion : X ⊆ h.region := by
    intro x hx
    exact h_region.thickening_subset (Metric.self_subset_cthickening X hx)
  have hpoint := aemeasurableReturnedPoint hX restart htermination
  have hmultiplier := aemeasurableReturnedMultiplier hX restart htermination
  have hfixed (i : ℕ) := successRestrictedSelectedResidual_le K hK confidence
    confidence_pos confidence_lt_one X hX initial_mem restart h_region i
  have hresidual := residualMeanSquare_le_of_successRestricted hX hXregion restart
    (ENNReal.ofReal (stochasticComplexityConstant h oracle params /
      ((1 - confidence) * ((K : ℝ) - 1)))) htermination hfixed
  exact ⟨hpoint, hmultiplier, hresidual⟩

/-- Corollary 4.2 (16): under corrected localization and the safeguarded restart,
the returned pair at the corrected threshold is stochastic `ε`-KKT. -/
theorem isApproximatePair_of_iterationBound
    (K : ℕ) (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : SafeguardedRestart h oracle ℙ x₀ multiplier₀ params K hK X)
    (h_region : RegionCondition h oracle params confidence X)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations : stochasticComplexityConstant h oracle params * ε⁻¹ ^ 2 ≤
      (1 - confidence) * ((K : ℝ) - 1)) :
    KKT.Stochastic.IsApproximatePair ℙ f c ε
      restart.returnedPoint restart.returnedMultiplier := by
  -- Obtain measurability and the corrected first-success residual rate together.
  have hreturned := returnedPairResidualBounds K hK confidence confidence_pos
    confidence_lt_one X hX initial_mem restart h_region
  have hepsilon : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hepsilonNe : (ε : ℝ) ≠ 0 := hepsilon.ne'
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnat
  have hdenominator :
      0 < (1 - confidence) * ((K : ℝ) - 1) :=
    mul_pos (sub_pos.mpr confidence_lt_one) (sub_pos.mpr hKreal)
  -- Divide the iteration threshold by its positive corrected denominator.
  have hrealRate :
      stochasticComplexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1)) ≤
        (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    calc
      stochasticComplexityConstant h oracle params =
          (stochasticComplexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) *
            (ε : ℝ) ^ 2 := by
        field_simp [hepsilonNe]
      _ ≤ ((1 - confidence) * ((K : ℝ) - 1)) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h_iterations (sq_nonneg (ε : ℝ))
      _ = (ε : ℝ) ^ 2 *
          ((1 - confidence) * ((K : ℝ) - 1)) := by ring
  have hresidual :
      KKT.Stochastic.residualMeanSquare ℙ f c
          restart.returnedPoint restart.returnedMultiplier ≤
        (ε : ℝ≥0∞) ^ 2 := by
    calc
      KKT.Stochastic.residualMeanSquare ℙ f c
          restart.returnedPoint restart.returnedMultiplier ≤
          ENNReal.ofReal (stochasticComplexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))) := hreturned.2.2
      _ ≤ ENNReal.ofReal ((ε : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal hrealRate
      _ = (ε : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  exact KKT.Stochastic.IsApproximatePair.of_residualMeanSquare_le
    hreturned.1 hreturned.2.1 hresidual


omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: an ENNReal expected-cost bound transfers a real
Big-O estimate from its nonnegative deterministic majorant. -/
private lemma expectedCost_isBigO_of_bound
    (cost : ℝ≥0 → Ω → ℕ∞) (bound rate : ℝ≥0 → ℝ)
    (hboundNonneg : ∀ ε, 0 ≤ bound ε)
    (hcost : ∀ ε, ∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (bound ε))
    (hboundBigO : bound =O[nhdsWithin 0 (Set.Ioi 0)] rate) :
    (fun ε ↦ ENNReal.toReal
      (∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] rate := by
  -- Convert the finite ENNReal majorant pointwise, then compose Big-O bounds.
  have hdomination :
      (fun ε ↦ ENNReal.toReal
        (∫⁻ omega, (cost ε omega : ℝ≥0∞) ∂ℙ))
        =O[nhdsWithin 0 (Set.Ioi 0)] bound :=
    Asymptotics.isBigO_of_le _ fun ε ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        Real.norm_eq_abs, abs_of_nonneg (hboundNonneg ε)]
      exact ENNReal.toReal_le_of_le_ofReal (hboundNonneg ε) (hcost ε)
  exact hdomination.trans hboundBigO

/-- Helper for Corollary 4.2: the confidence-adjusted corrected safeguarded
iteration horizon is `O(ε⁻²)`. -/
private lemma safeguardedIterationBudget_isBigO
    (confidence : ℝ) :
    (fun ε : ℝ≥0 ↦
      (safeguardedIterationBudget h oracle params confidence ε : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Normalize division by the fixed positive success probability into the coefficient.
  simpa only [safeguardedIterationBudget_def, div_eq_mul_inv, mul_assoc,
    mul_left_comm, mul_comm] using
      natCeilQuadraticBudget_isBigO
        (stochasticComplexityConstant h oracle params / (1 - confidence))

/-- Helper for Corollary 4.2: expected corrected safeguarded iterations are
`O(ε⁻²)`. -/
private lemma expectedTotalIterations_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (h_region : RegionCondition h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ omega, ((restart ε).totalIterations omega : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Multiply the quadratic horizon estimate by the fixed geometric factor.
  let budget : ℝ≥0 → ℝ := fun ε ↦
    (safeguardedIterationBudget h oracle params confidence ε : ℝ) /
      (1 - confidence)
  have honeMinus : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hbudgetNonneg (ε : ℝ≥0) : 0 ≤ budget ε := by
    dsimp only [budget]
    exact div_nonneg (Nat.cast_nonneg _) honeMinus.le
  have hquadratic := safeguardedIterationBudget_isBigO
    (h := h) (oracle := oracle) (params := params) confidence
  have hbudgetBigO :
      budget =O[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
    have hscaled := hquadratic.const_mul_left ((1 - confidence)⁻¹)
    simpa only [budget, div_eq_mul_inv, mul_comm] using hscaled
  refine expectedCost_isBigO_of_bound
    (fun ε ↦ (restart ε).totalIterations) budget
      (fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2) hbudgetNonneg ?_ hbudgetBigO
  intro ε
  exact expectedTotalIterations_le confidence confidence_pos confidence_lt_one
    hX initial_mem (restart ε) h_region

/-- Helper for Corollary 4.2: one full corrected attempt at the safeguarded
horizon has `O(ε⁻³)` stochastic-gradient cost. -/
private lemma safeguardedAttemptGradientEvaluationCount_isBigO
    (confidence : ℝ)
    (run : ∀ ε : ℝ≥0, SPIDER.Correction.ScheduledRun h oracle ℙ x₀ multiplier₀
      params (safeguardedIterationBudget h oracle params confidence ε)) :
    (fun ε : ℝ≥0 ↦ ((run ε).gradientEvaluationCount
      (safeguardedIterationBudget h oracle params confidence ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
  -- Reuse the direct schedule architecture with the confidence-adjusted coefficient.
  let C : ℝ := stochasticComplexityConstant h oracle params / (1 - confidence)
  let D : ℝ := |C| + 3
  let A : ℝ :=
    2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2 *
      displacementFactor h params.delta ^ 2
  let M : ℝ := D * ((D + 1) + 2 * (A * (D + 1) + 1))
  refine Asymptotics.IsBigO.of_bound M ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  let x : ℝ := (ε : ℝ)⁻¹
  let K : ℕ := safeguardedIterationBudget h oracle params confidence ε
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact (one_le_inv₀ hεreal).2 hεrealOne
  have hxNonneg : 0 ≤ x := le_trans zero_le_one hx
  have hxSq : 1 ≤ x ^ 2 := by nlinarith
  have hxSqNonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [abs_nonneg C]
  have hDNonneg : 0 ≤ D := le_trans zero_le_one hD
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [errorStepConstant_pos h params]
  have hK : 2 ≤ K := by
    dsimp only [K]
    rw [safeguardedIterationBudget_def]
    omega
  have hKNonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hzeroOne : (0 : ℝ) ≤ 1 := by norm_num
  have hargument :
      stochasticComplexityConstant h oracle params * x ^ 2 /
          (1 - confidence) = C * x ^ 2 := by
    dsimp only [C]
    ring
  -- The adjusted ceiling horizon remains quadratically bounded near zero.
  have hKBound : (K : ℝ) ≤ D * x ^ 2 := by
    dsimp only [K]
    rw [safeguardedIterationBudget_def, hargument]
    by_cases hC : 0 ≤ C
    · have hceilingArgument : 0 ≤ C * x ^ 2 := mul_nonneg hC hxSqNonneg
      have hceiling := Nat.ceil_lt_add_one hceilingArgument
      have hCplus : 0 ≤ C + 3 := by positivity
      rw [Nat.cast_add, Nat.cast_ofNat]
      dsimp only [D]
      rw [abs_of_nonneg hC]
      nlinarith [mul_nonneg hCplus (sub_nonneg.mpr hxSq)]
    · have hceilingArgument : C * x ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hxSqNonneg
      have hceiling : Nat.ceil (C * x ^ 2) = 0 :=
        Nat.ceil_eq_zero.mpr hceilingArgument
      rw [hceiling, Nat.zero_add, Nat.cast_ofNat]
      dsimp only [D]
      have hcoefficient : 0 ≤ |C| + 3 := by positivity
      have hthree : (3 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      have hproduct : (3 : ℝ) * 1 ≤ (|C| + 3) * x ^ 2 :=
        mul_le_mul hthree hxSq hzeroOne hcoefficient
      nlinarith
  -- Convert the quadratic horizon into linear refresh and inner-batch bounds.
  have hrefreshRaw := StochasticRun.refreshPeriod_le_sqrt_add_one K hK
  have hDsq : D ≤ D ^ 2 := by nlinarith
  have hKSquare : (K : ℝ) ≤ (D * x) ^ 2 := by
    calc
      (K : ℝ) ≤ D * x ^ 2 := hKBound
      _ ≤ D ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hDsq hxSqNonneg
      _ = (D * x) ^ 2 := by ring
  have hsqrtK : Real.sqrt K ≤ D * x := by
    have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
    have hsqrtSquare := Real.sq_sqrt hKNonneg
    have hDxNonneg : 0 ≤ D * x := mul_nonneg hDNonneg hxNonneg
    nlinarith
  have hrefreshBound :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ (D + 1) * x := by
    calc
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := hrefreshRaw
      _ ≤ D * x + 1 := by
        simpa only [add_comm] using add_le_add_right hsqrtK 1
      _ ≤ (D + 1) * x := by nlinarith
  have hinnerRaw := StochasticRun.innerBatchSize_le_linear h oracle params K
  have hinnerBound :
      ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
        (A * (D + 1) + 1) * x := by
    calc
      ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
          A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
        simpa only [A] using hinnerRaw
      _ ≤ A * ((D + 1) * x) + 1 := by
        gcongr
      _ ≤ (A * (D + 1) + 1) * x := by
        nlinarith [mul_nonneg hA (add_nonneg hDNonneg zero_le_one)]
  -- Insert the combinatorial schedule count and collect cubic powers.
  have hcountNat := StochasticRun.gradientEvaluationCount_le_schedule K hK (run ε)
  have hcountReal :
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤
        ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
          2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) := by
    exact_mod_cast hcountNat
  have hrefreshNonneg :
      0 ≤ ((SPIDER.refreshPeriod K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hinnerNonneg :
      0 ≤ ((SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hrefreshWork :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K ≤
        ((D + 1) * x) * (D * x ^ 2) := by
    exact mul_le_mul hrefreshBound hKBound hKNonneg
      (mul_nonneg (add_nonneg hDNonneg zero_le_one) hxNonneg)
  have hinnerCoefficientNonneg : 0 ≤ A * (D + 1) + 1 := by positivity
  have hinnerWork :
      (2 : ℝ) * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) ≤
        2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) := by
    gcongr
  have hcountBound :
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤ M * x ^ 3 := by
    calc
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤
          ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
            2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) :=
        hcountReal
      _ ≤ ((D + 1) * x) * (D * x ^ 2) +
          2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) :=
        add_le_add hrefreshWork hinnerWork
      _ = M * x ^ 3 := by
        dsimp only [M]
        ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxNonneg 3)]
  simpa only [K, x] using hcountBound

/-- Corollary 4.2 (17): the safeguarded expected stochastic-gradient count is
`O(ε⁻³)`. -/
theorem expectedGradientEvaluationCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (h_region : RegionCondition h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).gradientEvaluationCount ω : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
  -- Bound total work by expected attempts times one full corrected SPIDER schedule.
  let perAttempt : ℝ≥0 → ℕ := fun ε ↦
    ((restart ε).attempt 0).gradientEvaluationCount
      (safeguardedIterationBudget h oracle params confidence ε)
  let bound : ℝ≥0 → ℝ := fun ε ↦ (perAttempt ε : ℝ) / (1 - confidence)
  have honeMinus : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hboundNonneg (ε : ℝ≥0) : 0 ≤ bound ε := by
    dsimp only [bound]
    exact div_nonneg (Nat.cast_nonneg _) honeMinus.le
  have hperAttempt := safeguardedAttemptGradientEvaluationCount_isBigO
    (h := h) (oracle := oracle) (params := params) confidence
      (fun ε ↦ (restart ε).attempt 0)
  have hboundBigO :
      bound =O[nhdsWithin 0 (Set.Ioi 0)]
        fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
    have hscaled := hperAttempt.const_mul_left ((1 - confidence)⁻¹)
    simpa only [bound, perAttempt, div_eq_mul_inv, mul_comm] using hscaled
  refine expectedCost_isBigO_of_bound
    (fun ε ↦ (restart ε).gradientEvaluationCount) bound
      (fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3) hboundNonneg ?_ hboundBigO
  intro ε
  simpa only [bound, perAttempt] using
    expectedCost_le confidence confidence_pos confidence_lt_one hX initial_mem
      (restart ε) h_region (restart ε).gradientEvaluationCount (perAttempt ε)
        (restart ε).gradientEvaluationCount_le

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Corollary 4.2: doubling an extended-natural cost commutes with
the real-valued expectation used in the complexity statements. -/
private lemma toReal_lintegral_two_mul_enat (cost : Ω → ℕ∞) :
    ENNReal.toReal (∫⁻ omega, ((2 : ℕ∞) * cost omega : ℝ≥0∞) ∂ℙ) =
      2 * ENNReal.toReal (∫⁻ omega, (cost omega : ℝ≥0∞) ∂ℙ) := by
  rw [lintegral_const_mul']
  · simp
  · norm_num

/-- Corollary 4.2 (18): the safeguarded expected deterministic constraint count
is `O(ε⁻²)`. -/
theorem expectedConstraintEvaluationCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (h_region : RegionCondition h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).constraintEvaluationCount ω : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Pull the two constraint evaluations per transition through expectation.
  have htotal :=
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region
  have hscaled := htotal.const_mul_left (2 : ℝ)
  simpa only [constraintEvaluationCount_eq_two_mul_totalIterations,
    ENat.toENNReal_mul, ENat.toENNReal_coe, toReal_lintegral_two_mul_enat] using hscaled

/-- Corollary 4.2 (19): the safeguarded expected deterministic Jacobian count is
`O(ε⁻²)`. -/
theorem expectedJacobianEvaluationCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (h_region : RegionCondition h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).jacobianEvaluationCount ω : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Pull the two Jacobian evaluations per transition through expectation.
  have htotal :=
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region
  have hscaled := htotal.const_mul_left (2 : ℝ)
  simpa only [jacobianEvaluationCount_eq_two_mul_totalIterations,
    ENat.toENNReal_mul, ENat.toENNReal_coe, toReal_lintegral_two_mul_enat] using hscaled

/-- Corollary 4.2 (20): the safeguarded expected primal-solve count is
`O(ε⁻²)`. -/
theorem expectedPrimalSolveCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (h_region : RegionCondition h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).primalSolveCount ω : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- This counter is definitionally the executed-iteration counter.
  simpa only [primalSolveCount_eq_totalIterations] using
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region

/-- Corollary 4.2 (21): the safeguarded expected correction-solve count is
`O(ε⁻²)`. -/
theorem expectedCorrectionSolveCount_isBigO
    (confidence : ℝ) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (restart : ∀ ε : ℝ≥0, SafeguardedRestart h oracle ℙ x₀ multiplier₀ params
      (safeguardedIterationBudget h oracle params confidence ε)
      (safeguardedIterationBudget_ge_two h oracle params confidence ε) X)
    (h_region : RegionCondition h oracle params confidence X) :
    (fun ε : ℝ≥0 ↦ ENNReal.toReal
      (∫⁻ ω, ((restart ε).correctionSolveCount ω : ℝ≥0∞) ∂ℙ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- This counter is definitionally the executed-iteration counter.
  simpa only [correctionSolveCount_eq_totalIterations] using
    expectedTotalIterations_isBigO confidence confidence_pos confidence_lt_one
      X hX initial_mem restart h_region

end SafeguardedRestart

namespace Run

/-- Helper for Corollary 4.2: the corrected lifted energy controls the square
of the natural two-base-step trajectory length. -/
private lemma liftedEnergyDescent
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (k : ℕ) (hk : 1 ≤ k) :
    (params.beta / 16) *
        (‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖) ^ 2 ≤
      LALM.liftedEnergy f c params.rho params.beta (run.liftedIterate k) -
        LALM.liftedEnergy f c params.rho params.beta
          (run.liftedIterate (k + 1)) := by
  -- Corrected primal descent and the adjacent-step multiplier estimate give
  -- the same lifted sufficient-decrease inequality as in Theorem 2.13.
  have hAdmissible := allPrefixesAdmissible h params h_region run (k + 1)
  have hLagrangian :=
    run.augmentedLagrangianDescent h params hAdmissible (Nat.lt_succ_self k)
  have hMultiplier :=
    run.norm_multiplier_succ_sub_sq_le h params hAdmissible hk
      (Nat.lt_succ_self k)
  have hMultiplierDiv :
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    have hDivided := (div_le_div_iff_of_pos_right run.rho_pos).2 hMultiplier
    calc
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound *
              (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2)) /
                params.rho := hDivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
              (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by ring
  have hCoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have hCorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) ≤
        (params.beta / 8) *
            (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hCoefficient
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hTwoStepSquare :
      (‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖) ^ 2 ≤
        2 * (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    nlinarith [sq_nonneg (‖run.baseStep k‖ - ‖run.baseStep (k - 1)‖)]
  -- Expand the two lifted energies once and combine the correction terms.
  rw [run.liftedIterate_apply, run.liftedIterate_apply,
    liftedEnergy_liftedState, liftedEnergy_liftedState, Nat.add_sub_cancel,
    augmentedLagrangian_multiplier_succ_eq h params run]
  nlinarith [run.beta_pos]

/-- Helper for Corollary 4.2: corrected lifted states whose primal coordinate
lies in the regularity region. -/
private def liftedRegularityRegion (h : EqualityConstrained.Regularity f c) :
    Set (LiftedState n m) :=
  {u | u.fst ∈ h.region}

/-- Helper for Corollary 4.2: the corrected lifted regularity region is open. -/
private lemma isOpen_liftedRegularityRegion
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (liftedRegularityRegion h) := by
  exact h.isOpen_region.preimage (WithLp.continuous_fst 2 _ _)

/-- Helper for Corollary 4.2: primal--multiplier pairs whose primal coordinate
lies in the regularity region. -/
private def pairRegularityRegion (h : EqualityConstrained.Regularity f c) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  {z | z.1 ∈ h.region}

/-- Helper for Corollary 4.2: the corrected primal--multiplier regularity
region is open. -/
private lemma isOpen_pairRegularityRegion
    (h : EqualityConstrained.Regularity f c) :
    IsOpen (pairRegularityRegion h) := by
  exact h.isOpen_region.preimage continuous_fst

/-- Helper for Corollary 4.2: all corrected lifted iterates lie in one compact
subset of the lifted finite-dimensional state space. -/
private lemma existsCompactLiftedIterateRange
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params)) :
    ∃ K : Set (LiftedState n m), IsCompact K ∧
      K ⊆ liftedRegularityRegion h ∧ ∀ k, run.liftedIterate k ∈ K := by
  let source : Set ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ×
      EuclideanSpace ℝ (Fin n)) :=
    (deterministicSublevel h params ×ˢ
      Metric.closedBall 0 params.multiplierBound) ×ˢ
        Metric.closedBall 0 params.delta
  let assemble :
      ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ×
        EuclideanSpace ℝ (Fin n)) → LiftedState n m :=
    fun z ↦ liftedState z.1.1 z.1.2 z.2
  have hSource : IsCompact source := by
    -- Compactness of the primal sublevel and Euclidean closed balls gives the
    -- compact source set for the lifted-state assembly map.
    exact (h_compact.prod (isCompact_closedBall 0 params.multiplierBound)).prod
      (isCompact_closedBall 0 params.delta)
  have hAssemble : Continuous assemble := by
    unfold assemble liftedState
    fun_prop
  refine ⟨assemble '' source, hSource.image hAssemble, ?_, fun k ↦ ?_⟩
  · rintro u ⟨z, hz, rfl⟩
    change z.1.1 ∈ h.region
    apply (deterministicRegionCondition_iff h params).1 h_region
    exact Metric.self_subset_cthickening (deterministicSublevel h params) hz.1.1
  have hPrefix := allPrefixesAdmissible h params h_region run (k + 1)
  have hkLe : k ≤ k + 1 := Nat.le_succ k
  have hkBaseStep : k - 1 < k + 1 := by omega
  have hPoint : run.point k ∈ deterministicSublevel h params :=
    (mem_deterministicSublevel h params (run.point k)).2
      ⟨objective_le_deterministicBound_of_prefix h params run hPrefix hkLe,
        constraintNorm_le_localizationBound_of_prefix h params run hPrefix hkLe⟩
  have hMultiplier : ‖run.multiplier k‖ ≤ params.multiplierBound :=
    run.norm_multiplier_le h params hPrefix hkLe
  have hBaseStep : ‖run.baseStep (k - 1)‖ ≤ params.delta :=
    run.norm_baseStep_le h params hPrefix hkBaseStep
  -- Package the three global corrected bounds as one image witness.
  rw [run.liftedIterate_apply]
  refine ⟨((run.point k, run.multiplier k), run.baseStep (k - 1)), ?_, rfl⟩
  change ((run.point k ∈ deterministicSublevel h params ∧
      run.multiplier k ∈ Metric.closedBall 0 params.multiplierBound) ∧
        run.baseStep (k - 1) ∈ Metric.closedBall 0 params.delta)
  refine ⟨⟨hPoint, ?_⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hMultiplier
  · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hBaseStep

/-- Helper for Corollary 4.2: the lifted energy is continuous wherever its
primal coordinate lies in the regularity region. -/
private lemma continuousOn_liftedEnergy
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ) :
    ContinuousOn (LALM.liftedEnergy f c rho beta)
      (liftedRegularityRegion h) := by
  intro u hu
  change u.fst ∈ h.region at hu
  have hObjective : ContinuousAt f u.fst := h.continuousAt_objective hu
  have hConstraint : ContinuousAt c u.fst := h.continuousAt_constraint hu
  -- Each energy term is assembled from continuous lifted-state projections.
  apply ContinuousAt.continuousWithinAt
  unfold liftedEnergy augmentedLagrangian
  fun_prop

/-- Helper for Corollary 4.2: the lifted-energy gradient separates into
stationarity, feasibility, and the stored base-step coordinate. -/
private lemma hasGradientAt_liftedEnergy_liftedState
    (h : EqualityConstrained.Regularity f c) (rho beta : ℝ)
    (x step : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (hx : x ∈ h.region) :
    HasGradientAt (LALM.liftedEnergy f c rho beta)
      (liftedState (KKT.stationarity f c x (multiplier + rho • c x))
        (c x) ((beta / 2) • step))
      (liftedState x multiplier step) := by
  let pointMap : LiftedState n m →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    WithLp.fstL 2 ℝ _ _
  let remainderMap : LiftedState n m →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    WithLp.sndL 2 ℝ _ _
  let multiplierMap : LiftedState n m →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.fstL 2 ℝ _ _).comp remainderMap
  let stepMap : LiftedState n m →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.sndL 2 ℝ _ _).comp remainderMap
  have hPoint : HasFDerivAt (fun u : LiftedState n m ↦ u.fst) pointMap
      (liftedState x multiplier step) := by
    refine pointMap.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp only [pointMap, WithLp.fstL_apply]
  have hMultiplier : HasFDerivAt
      (fun u : LiftedState n m ↦ u.snd.fst) multiplierMap
      (liftedState x multiplier step) := by
    refine multiplierMap.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp only [multiplierMap, remainderMap, ContinuousLinearMap.comp_apply,
      WithLp.fstL_apply, WithLp.sndL_apply]
  have hStep : HasFDerivAt (fun u : LiftedState n m ↦ u.snd.snd) stepMap
      (liftedState x multiplier step) := by
    refine stepMap.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards with u
    simp only [stepMap, remainderMap, ContinuousLinearMap.comp_apply,
      WithLp.sndL_apply]
  have hObjectiveAt : HasFDerivAt f (fderiv ℝ f x) x :=
    h.hasFDerivAt_objective hx
  have hConstraintAt : HasFDerivAt c (fderiv ℝ c x) x :=
    h.hasFDerivAt_constraint hx
  have hObjective := hObjectiveAt.comp (liftedState x multiplier step) hPoint
  have hConstraint := hConstraintAt.comp (liftedState x multiplier step) hPoint
  have hPairing := hMultiplier.inner ℝ hConstraint
  have hConstraintSquare := hConstraint.norm_sq
  have hStepSquare := hStep.norm_sq
  have hDerivative :=
    (hObjective.add hPairing).add (hConstraintSquare.const_mul (rho / 2)) |>.add
      (hStepSquare.const_mul (beta / 4))
  -- Identify the assembled derivative with the Riesz dual of the displayed
  -- three-coordinate gradient.
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hDerivative.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards with u
    rfl
  · ext direction
    simp only [pointMap, remainderMap, multiplierMap, stepMap,
      liftedState_multiplier, Function.comp_apply, liftedState_point,
      liftedState_step, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, WithLp.fstL_apply, WithLp.sndL_apply,
      fderivInnerCLM_apply, smul_apply, coe_innerSL_apply, nsmul_eq_mul,
      Nat.cast_ofNat, smul_eq_mul, KKT.stationarity_def,
      EqualityConstrained.constraintGradient_def,
      InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply,
      WithLp.ofLp_fst, WithLp.ofLp_snd, map_add, map_smul]
    rw [inner_add_left, inner_add_left, inner_smul_left, inner_gradient_left,
      ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
    simp only [starRingEnd_apply, star_trivial, inner_smul_left]
    rw [real_inner_comm direction.snd.fst (c x)]
    ring

/-- Helper for Corollary 4.2: the norm of a lifted state is bounded by the sum
of the norms of its three coordinates. -/
private lemma norm_liftedState_le
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (step : EuclideanSpace ℝ (Fin n)) :
    ‖liftedState x multiplier step‖ ≤ ‖x‖ + ‖multiplier‖ + ‖step‖ := by
  -- Compare squares using the exact nested `L²` product norm formula.
  apply (sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _))).1
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [liftedState_point, liftedState_multiplier, liftedState_step]
  nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg multiplier),
    mul_nonneg (norm_nonneg x) (norm_nonneg step),
    mul_nonneg (norm_nonneg multiplier) (norm_nonneg step)]

/-- Helper for Corollary 4.2: the corrected lifted gradient at iterate `k + 1`
is bounded by a fixed multiple of the adjacent base-step length at `k`. -/
private lemma norm_gradient_liftedEnergy_liftedIterate_succ_le
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ k, 1 ≤ k →
      ‖gradient (LALM.liftedEnergy f c params.rho params.beta)
        (run.liftedIterate (k + 1))‖ ≤
          B * (‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖) := by
  let residualCoefficient := Residual.comparisonConstant
    (primalComparisonConstant h params.delta params.beta params.rho
      params.multiplierBound)
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound) params.rho
  let comparison := residualCoefficient + 1
  let B := (2 + (params.rho : ℝ) * h.constraintGradientBound) * comparison +
    (params.beta : ℝ) / 2
  have hResidualCoefficient : 0 ≤ residualCoefficient := by
    dsimp only [residualCoefficient]
    rw [Residual.comparisonConstant_def, multiplierPrimalConstant_def]
    positivity
  have hComparisonNonneg : 0 ≤ comparison := by
    dsimp only [comparison]
    linarith
  have hComparisonPos : 0 < comparison := by
    dsimp only [comparison]
    linarith
  have hComparisonSquare : residualCoefficient ≤ comparison ^ 2 := by
    dsimp only [comparison]
    nlinarith [sq_nonneg residualCoefficient]
  have hBPos : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hBPos, fun k hk ↦ ?_⟩
  let twoStep := ‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖
  have hTwoStepNonneg : 0 ≤ twoStep := by
    dsimp only [twoStep]
    positivity
  have hTwoStepSquare :
      ‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2 ≤ twoStep ^ 2 := by
    dsimp only [twoStep]
    nlinarith [mul_nonneg (norm_nonneg (run.baseStep k))
      (norm_nonneg (run.baseStep (k - 1)))]
  have hAdmissible := allPrefixesAdmissible h params h_region run (k + 1)
  have hResidualSquare :=
    residual_sq_le h params run hAdmissible hk (Nat.lt_succ_self k)
  have hResidualComponents :
      ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1))‖ ^ 2 +
          ‖c (run.point (k + 1))‖ ^ 2 ≤
        residualCoefficient *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    rw [KKT.residual_def, Real.sq_sqrt
      (add_nonneg (sq_nonneg _) (sq_nonneg _))] at hResidualSquare
    simpa only [residualCoefficient] using hResidualSquare
  have hStationaritySquare :
      ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1))‖ ^ 2 ≤
        (comparison * twoStep) ^ 2 := by
    calc
      _ ≤ residualCoefficient *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) :=
        (le_add_of_nonneg_right (sq_nonneg _)).trans hResidualComponents
      _ ≤ residualCoefficient * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_left hTwoStepSquare hResidualCoefficient
      _ ≤ comparison ^ 2 * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_right hComparisonSquare (sq_nonneg _)
      _ = (comparison * twoStep) ^ 2 := by ring
  have hConstraintSquare :
      ‖c (run.point (k + 1))‖ ^ 2 ≤ (comparison * twoStep) ^ 2 := by
    calc
      _ ≤ ‖KKT.stationarity f c (run.point (k + 1))
            (run.multiplier (k + 1))‖ ^ 2 + ‖c (run.point (k + 1))‖ ^ 2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ residualCoefficient *
          (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) :=
        hResidualComponents
      _ ≤ residualCoefficient * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_left hTwoStepSquare hResidualCoefficient
      _ ≤ comparison ^ 2 * twoStep ^ 2 :=
        mul_le_mul_of_nonneg_right hComparisonSquare (sq_nonneg _)
      _ = (comparison * twoStep) ^ 2 := by ring
  have hStationarity :
      ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1))‖ ≤ comparison * twoStep :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hComparisonNonneg hTwoStepNonneg)).1 hStationaritySquare
  have hConstraint :
      ‖c (run.point (k + 1))‖ ≤ comparison * twoStep :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hComparisonNonneg hTwoStepNonneg)).1 hConstraintSquare
  have hTransition := (run.isAdmissiblePrefix_iff h (k + 1)).1 hAdmissible k
    (Nat.lt_succ_self k)
  have hPointMem : run.point (k + 1) ∈ h.region := by
    rw [run.point_succ]
    exact nextPoint_mem_region h (run.point k) (run.baseStep k) hTransition
  have hOperator := h.norm_constraintGradient_le (run.point (k + 1)) hPointMem
  have hCorrection :
      ‖EqualityConstrained.constraintGradient c (run.point (k + 1))
          ((params.rho : ℝ) • c (run.point (k + 1)))‖ ≤
        (params.rho : ℝ) * h.constraintGradientBound * comparison * twoStep := by
    calc
      _ ≤ ‖EqualityConstrained.constraintGradient c (run.point (k + 1))‖ *
          ‖(params.rho : ℝ) • c (run.point (k + 1))‖ :=
        (EqualityConstrained.constraintGradient c
          (run.point (k + 1))).le_opNorm _
      _ = ‖EqualityConstrained.constraintGradient c (run.point (k + 1))‖ *
          ((params.rho : ℝ) * ‖c (run.point (k + 1))‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos run.rho_pos]
      _ ≤ h.constraintGradientBound *
          ((params.rho : ℝ) * ‖c (run.point (k + 1))‖) :=
        mul_le_mul_of_nonneg_right hOperator
          (mul_nonneg run.rho_pos.le (norm_nonneg _))
      _ ≤ h.constraintGradientBound *
          ((params.rho : ℝ) * (comparison * twoStep)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hConstraint run.rho_pos.le)
          (NNReal.coe_nonneg h.constraintGradientBound)
      _ = (params.rho : ℝ) * h.constraintGradientBound * comparison *
          twoStep := by ring
  have hShiftedStationarity :
      ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1) +
            (params.rho : ℝ) • c (run.point (k + 1)))‖ ≤
        (1 + (params.rho : ℝ) * h.constraintGradientBound) * comparison *
          twoStep := by
    have hIdentity :
        KKT.stationarity f c (run.point (k + 1))
            (run.multiplier (k + 1) +
              (params.rho : ℝ) • c (run.point (k + 1))) =
          KKT.stationarity f c (run.point (k + 1))
              (run.multiplier (k + 1)) +
            EqualityConstrained.constraintGradient c (run.point (k + 1))
              ((params.rho : ℝ) • c (run.point (k + 1))) := by
      simp only [KKT.stationarity_def, map_add]
      abel
    rw [hIdentity]
    calc
      _ ≤ ‖KKT.stationarity f c (run.point (k + 1))
              (run.multiplier (k + 1))‖ +
            ‖EqualityConstrained.constraintGradient c (run.point (k + 1))
              ((params.rho : ℝ) • c (run.point (k + 1)))‖ := norm_add_le _ _
      _ ≤ comparison * twoStep +
            (params.rho : ℝ) * h.constraintGradientBound * comparison * twoStep :=
        add_le_add hStationarity hCorrection
      _ = (1 + (params.rho : ℝ) * h.constraintGradientBound) * comparison *
          twoStep := by ring
  have hGradient :
      gradient (LALM.liftedEnergy f c params.rho params.beta)
          (run.liftedIterate (k + 1)) =
        liftedState
          (KKT.stationarity f c (run.point (k + 1))
            (run.multiplier (k + 1) +
              (params.rho : ℝ) • c (run.point (k + 1))))
          (c (run.point (k + 1)))
          ((params.beta / 2 : ℝ) • run.baseStep k) := by
    rw [run.liftedIterate_apply, Nat.add_sub_cancel]
    exact (hasGradientAt_liftedEnergy_liftedState h params.rho params.beta
      (run.point (k + 1)) (run.baseStep k)
      (run.multiplier (k + 1)) hPointMem).gradient
  have hStepPart :
      ‖(params.beta / 2 : ℝ) • run.baseStep k‖ ≤
        ((params.beta : ℝ) / 2) * twoStep := by
    have hTwoPos : (0 : ℝ) < 2 := by norm_num
    have hBetaHalfPos : 0 < (params.beta : ℝ) / 2 :=
      div_pos run.beta_pos hTwoPos
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos hBetaHalfPos]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg (run.baseStep (k - 1))))
      hBetaHalfPos.le
  -- Combine the three lifted-gradient coordinates under one fixed comparison.
  rw [hGradient]
  calc
    _ ≤ ‖KKT.stationarity f c (run.point (k + 1))
          (run.multiplier (k + 1) +
            (params.rho : ℝ) • c (run.point (k + 1)))‖ +
          ‖c (run.point (k + 1))‖ +
            ‖(params.beta / 2 : ℝ) • run.baseStep k‖ :=
      norm_liftedState_le _ _ _
    _ ≤ (1 + (params.rho : ℝ) * h.constraintGradientBound) * comparison *
          twoStep + comparison * twoStep +
            ((params.beta : ℝ) / 2) * twoStep :=
      add_le_add (add_le_add hShiftedStationarity hConstraint) hStepPart
    _ = B * (‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖) := by
      dsimp only [B, twoStep]
      ring

/-- Helper for Corollary 4.2: summability of adjacent corrected base-step
lengths implies summability of base steps together with multiplier increments. -/
private lemma summableBaseStepAndMultiplierIncrement_of_summableTwoStep
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (hTwoStep : Summable
      (fun k ↦ ‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖)) :
    Summable (fun k ↦ ‖run.baseStep k‖ +
      ‖run.multiplier (k + 1) - run.multiplier k‖) := by
  let coefficient := multiplierPrimalConstant h params.delta params.beta
    params.rho params.multiplierBound
  let comparison := coefficient + 1
  have hCoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    rw [multiplierPrimalConstant_def]
    positivity
  have hComparison : 0 ≤ comparison := by
    dsimp only [comparison]
    linarith
  have hComparisonSq : coefficient ≤ comparison ^ 2 := by
    dsimp only [comparison]
    nlinarith [sq_nonneg coefficient]
  have hShiftedTwoStep : Summable
      (fun k ↦ ‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) := by
    simpa only [Nat.add_sub_cancel] using (summable_nat_add_iff 1).2 hTwoStep
  have hDominating : Summable (fun k ↦
      (comparison + 1) * (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖)) :=
    hShiftedTwoStep.mul_left (comparison + 1)
  rw [← summable_nat_add_iff 1]
  apply hDominating.of_nonneg_of_le
  · intro k
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro k
    have hkPos : 1 ≤ k + 1 := by omega
    have hkLt : k + 1 < k + 2 := by omega
    have hMultiplierSq := run.norm_multiplier_succ_sub_sq_le h params
      (allPrefixesAdmissible h params h_region run (k + 2))
      hkPos hkLt
    have hTwoStepSquare :
        ‖run.baseStep (k + 1)‖ ^ 2 + ‖run.baseStep k‖ ^ 2 ≤
          (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) ^ 2 := by
      nlinarith [mul_nonneg (norm_nonneg (run.baseStep (k + 1)))
        (norm_nonneg (run.baseStep k))]
    have hMultiplierSquareBound :
        ‖run.multiplier (k + 2) - run.multiplier (k + 1)‖ ^ 2 ≤
          (comparison *
            (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖)) ^ 2 := by
      calc
        _ ≤ coefficient *
            (‖run.baseStep (k + 1)‖ ^ 2 + ‖run.baseStep k‖ ^ 2) := by
          simpa only [coefficient, Nat.add_sub_cancel] using hMultiplierSq
        _ ≤ coefficient *
            (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hTwoStepSquare hCoefficient
        _ ≤ comparison ^ 2 *
            (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hComparisonSq (sq_nonneg _)
        _ = (comparison *
            (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖)) ^ 2 := by ring
    have hMultiplierBound :
        ‖run.multiplier (k + 2) - run.multiplier (k + 1)‖ ≤
          comparison *
            (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hComparison
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))).1
            hMultiplierSquareBound
    have hStepBound :
        ‖run.baseStep (k + 1)‖ ≤
          ‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖ :=
      le_add_of_nonneg_right (norm_nonneg _)
    have hCombined :
        ‖run.baseStep (k + 1)‖ +
            ‖run.multiplier (k + 2) - run.multiplier (k + 1)‖ ≤
          (comparison + 1) *
            (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) := by
      calc
        _ ≤ (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) +
              comparison *
                (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) :=
          add_le_add hStepBound hMultiplierBound
        _ = (comparison + 1) *
              (‖run.baseStep (k + 1)‖ + ‖run.baseStep k‖) := by ring
    simpa only [Nat.add_assoc] using hCombined

/-- Helper for Corollary 4.2: a nonnegative sequence is summable when twice
each successor is controlled by its predecessor and a telescoping potential. -/
private lemma summable_of_two_mul_shift_le
    (d q : ℕ → ℝ)
    (hDNonneg : ∀ k, 0 ≤ d k)
    (hQNonneg : ∀ k, 0 ≤ q k)
    (hRecurrence : ∀ k, 2 * d (k + 1) ≤ d k + q k - q (k + 1)) :
    Summable d := by
  have hPartial : ∀ k,
      (∑ i ∈ Finset.range (k + 1), d i) + d k + q k ≤ 2 * d 0 + q 0 := by
    intro k
    induction k with
    | zero =>
        rw [Finset.sum_range_one]
        ring_nf
        exact le_rfl
    | succ k hk =>
        rw [Finset.sum_range_succ]
        have hStep := hRecurrence k
        nlinarith
  -- Drop the nonnegative boundary terms from the uniform partial-sum bound.
  apply summable_of_sum_range_le (c := 2 * d 0 + q 0) hDNonneg
  intro k
  cases k with
  | zero =>
      have hDZero := hDNonneg 0
      have hQZero := hQNonneg 0
      simp only [Finset.range_zero, Finset.sum_empty]
      nlinarith
  | succ k =>
      have hBoundary := add_nonneg (hDNonneg k) (hQNonneg k)
      have hBound := hPartial k
      nlinarith

/-- Helper for Corollary 4.2: a desingularizer remains a desingularizer after
restricting its positive energy window. -/
private lemma isDesingularizer_of_le
    {eta eta' : ℝ} {phi : ℝ → ℝ}
    (hPhi : KurdykaLojasiewicz.IsDesingularizer eta phi)
    (hEta : eta' ≤ eta) :
    KurdykaLojasiewicz.IsDesingularizer eta' phi := by
  rw [KurdykaLojasiewicz.isDesingularizer_iff] at hPhi ⊢
  rcases hPhi with ⟨hMaps, hContinuous, hZero, hContDiff, hDeriv, hConcave⟩
  have hIco : Set.Ico 0 eta' ⊆ Set.Ico 0 eta := by
    intro x hx
    exact ⟨hx.1, hx.2.trans_le hEta⟩
  have hIoo : Set.Ioo 0 eta' ⊆ Set.Ioo 0 eta := by
    intro x hx
    exact ⟨hx.1, hx.2.trans_le hEta⟩
  -- Restrict every defining regularity and positivity property to the smaller
  -- interval without changing the desingularizing function.
  refine ⟨hMaps.mono hIco Set.Subset.rfl, hContinuous.mono hIco, hZero,
    hContDiff.mono hIoo, ?_, ⟨convex_Ico 0 eta', ?_⟩⟩
  · intro x hx
    exact hDeriv x (hIoo hx)
  · intro x hx y hy a b ha hb hab
    exact hConcave.2 (hIco hx) (hIco hy) ha hb hab

/-- Helper for Corollary 4.2: a nonempty finite sum of desingularizers on a
common window is again a desingularizer on that window. -/
private lemma isDesingularizer_finsetSum
    {index : Type*} (s : Finset index) (hNonempty : s.Nonempty)
    (eta : ℝ) (phi : index → ℝ → ℝ)
    (hPhi : ∀ i ∈ s, KurdykaLojasiewicz.IsDesingularizer eta (phi i)) :
    KurdykaLojasiewicz.IsDesingularizer eta
      (fun x ↦ ∑ i ∈ s, phi i x) := by
  classical
  simp only [KurdykaLojasiewicz.isDesingularizer_iff] at hPhi ⊢
  have hConcaveSum : ∀ t : Finset index,
      (∀ i ∈ t, ConcaveOn ℝ (Set.Ico 0 eta) (phi i)) →
        ConcaveOn ℝ (Set.Ico 0 eta) (fun x ↦ ∑ i ∈ t, phi i x) := by
    intro t hConcave
    induction t using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (concaveOn_const (0 : ℝ) (convex_Ico 0 eta))
    | @insert i t hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hConcave i (Finset.mem_insert_self i t)).add
          (ih fun j hj ↦ hConcave j (Finset.mem_insert_of_mem hj))
  -- Verify the desingularizer properties componentwise over the finite family.
  refine ⟨?_, ?_, ?_, ?_, ?_,
    hConcaveSum s fun i hi ↦ (hPhi i hi).2.2.2.2.2⟩
  · intro x hx
    simp only [Set.mem_Ici]
    exact Finset.sum_nonneg fun i hi ↦ (hPhi i hi).1 hx
  · exact tendsto_finsetSum s fun i hi ↦ (hPhi i hi).2.1
  · exact Finset.sum_eq_zero fun i hi ↦ (hPhi i hi).2.2.1
  · exact ContDiffOn.sum fun i hi ↦ (hPhi i hi).2.2.2.1
  · intro x hx
    have hDifferentiable : ∀ i ∈ s, DifferentiableAt ℝ (phi i) x := by
      intro i hi
      have hDifferentiableWithin :
          DifferentiableWithinAt ℝ (phi i) (Set.Ioo 0 eta) x := by
        apply ((hPhi i hi).2.2.2.1 x hx).differentiableWithinAt
        norm_num
      exact hDifferentiableWithin.differentiableAt (isOpen_Ioo.mem_nhds hx)
    rw [deriv_fun_sum hDifferentiable]
    exact Finset.sum_pos
      (fun i hi ↦ (hPhi i hi).2.2.2.2.1 x hx) hNonempty

/-- Helper for Corollary 4.2: pointwise KL inequalities on a compact corrected
cluster set combine into one eventual inequality with a common desingularizer. -/
private lemma eventually_uniformKL_of_compactCluster
    (energy : LiftedState n m → ℝ) (u : ℕ → LiftedState n m)
    (K : Set (LiftedState n m)) (hKCompact : IsCompact K)
    (hKRange : ∀ k, u k ∈ K)
    (hKL : KurdykaLojasiewicz.HasAtClusterPoints energy atTop u)
    (energyLimit : ℝ)
    (hClusterEnergy : ∀ x,
      MapClusterPt x atTop u → energy x = energyLimit) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ phi : ℝ → ℝ,
      KurdykaLojasiewicz.IsDesingularizer eta phi ∧
        ∀ᶠ k in atTop,
          energyLimit < energy (u k) → energy (u k) < energyLimit + eta →
            1 ≤ deriv phi (energy (u k) - energyLimit) *
              ‖gradient energy (u k)‖ := by
  classical
  let omega : Set (LiftedState n m) :=
    K ∩ {x | MapClusterPt x atTop u}
  have hClusterClosed : IsClosed {x | MapClusterPt x atTop u} := by
    change IsClosed {x | ClusterPt x (Filter.map u atTop)}
    exact isClosed_setOf_clusterPt
  have hOmegaCompact : IsCompact omega :=
    hKCompact.inter_right hClusterClosed
  have hMapRange : Filter.map u atTop ≤ Filter.principal K := by
    rw [le_principal_iff]
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall hKRange)
  obtain ⟨xCluster, hxK, hxCluster⟩ :=
    hKCompact.exists_mapClusterPt hMapRange
  have hOmegaNonempty : omega.Nonempty := ⟨xCluster, hxK, hxCluster⟩
  -- Choose local KL data at each cluster point before extracting a finite
  -- subcover of the compact corrected cluster set.
  have hLocalData : ∀ x : omega, ∃ eta : ℝ, 0 < eta ∧ ∃ phi : ℝ → ℝ,
      KurdykaLojasiewicz.IsDesingularizer eta phi ∧
        ∀ᶠ y in 𝓝 (x : LiftedState n m),
          energy x < energy y → energy y < energy x + eta →
            1 ≤ deriv phi (energy y - energy x) * ‖gradient energy y‖ := by
    intro x
    exact (KurdykaLojasiewicz.hasAt_iff energy x).1
      ((KurdykaLojasiewicz.hasAtClusterPoints_iff energy atTop u).1
        hKL x x.2.2)
  choose localEta hLocalEta localPhi hLocalPhi hLocalInequality using hLocalData
  let neighborhood : omega → Set (LiftedState n m) := fun x ↦
    {y | energy x < energy y → energy y < energy x + localEta x →
      1 ≤ deriv (localPhi x) (energy y - energy x) * ‖gradient energy y‖}
  have hNeighborhood : ∀ x : omega,
      neighborhood x ∈ 𝓝 (x : LiftedState n m) := by
    intro x
    change ∀ᶠ y in 𝓝 (x : LiftedState n m),
      energy x < energy y → energy y < energy x + localEta x →
        1 ≤ deriv (localPhi x) (energy y - energy x) * ‖gradient energy y‖
    exact hLocalInequality x
  obtain ⟨cover, hCover⟩ := hOmegaCompact.elim_nhds_subcover_nhdsSet'
    (fun x hx ↦ neighborhood ⟨x, hx⟩)
    (fun x hx ↦ hNeighborhood ⟨x, hx⟩)
  have hOmegaSubset : omega ⊆ ⋃ x ∈ cover, neighborhood x :=
    subset_of_mem_nhdsSet hCover
  have hCoverNonempty : cover.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    obtain ⟨x, hx⟩ := hOmegaNonempty
    have hxUnion := hOmegaSubset hx
    rw [hEmpty] at hxUnion
    simp at hxUnion
  let eta : ℝ := cover.inf' hCoverNonempty localEta
  have hEtaPos : 0 < eta := by
    dsimp only [eta]
    exact (Finset.lt_inf'_iff hCoverNonempty).2 fun i hi ↦ hLocalEta i
  have hEtaLe : ∀ i ∈ cover, eta ≤ localEta i := by
    intro i hi
    exact Finset.inf'_le localEta hi
  let phi : ℝ → ℝ := fun t ↦ ∑ i ∈ cover, localPhi i t
  have hRestricted : ∀ i ∈ cover,
      KurdykaLojasiewicz.IsDesingularizer eta (localPhi i) := by
    intro i hi
    exact isDesingularizer_of_le (hLocalPhi i) (hEtaLe i hi)
  have hPhi : KurdykaLojasiewicz.IsDesingularizer eta phi :=
    isDesingularizer_finsetSum cover hCoverNonempty eta localPhi hRestricted
  -- Every sufficiently late iterate lies in the finite cover, and the
  -- derivative of its summed chart dominates the selected local derivative.
  have hApproachOmega : Tendsto u atTop (nhdsSet omega) :=
    hKCompact.tendsto_nhdsSet_of_mapClusterPt
      (Filter.Eventually.of_forall hKRange)
      fun x hxK hxCluster ↦ ⟨hxK, hxCluster⟩
  have hEventuallyCovered : ∀ᶠ k in atTop,
      u k ∈ ⋃ x ∈ cover, neighborhood x := hApproachOmega hCover
  refine ⟨eta, hEtaPos, phi, hPhi, ?_⟩
  filter_upwards [hEventuallyCovered] with k hkCovered
  intro hAbove hBelow
  rcases Set.mem_iUnion.1 hkCovered with ⟨i, hkCovered⟩
  rcases Set.mem_iUnion.1 hkCovered with ⟨hiCover, hiNeighborhood⟩
  have hCenter : energy i = energyLimit := hClusterEnergy i i.2.2
  have hChart :
      1 ≤ deriv (localPhi i) (energy (u k) - energyLimit) *
        ‖gradient energy (u k)‖ := by
    have hWindow : energyLimit + eta ≤ energyLimit + localEta i := by
      linarith [hEtaLe i hiCover]
    rw [← hCenter]
    have hAboveCenter : energy i < energy (u k) := by
      rwa [hCenter]
    have hBelowCenter : energy (u k) < energy i + localEta i := by
      rw [hCenter]
      exact hBelow.trans_le hWindow
    exact hiNeighborhood hAboveCenter hBelowCenter
  have hGap : energy (u k) - energyLimit ∈ Set.Ioo 0 eta :=
    ⟨sub_pos.mpr hAbove, sub_lt_iff_lt_add'.mpr hBelow⟩
  have hDifferentiable : ∀ j ∈ cover,
      DifferentiableAt ℝ (localPhi j) (energy (u k) - energyLimit) := by
    intro j hj
    have hRestrictedSpec :=
      (KurdykaLojasiewicz.isDesingularizer_iff eta (localPhi j)).1
        (hRestricted j hj)
    have hDifferentiableWithin : DifferentiableWithinAt ℝ (localPhi j)
        (Set.Ioo 0 eta) (energy (u k) - energyLimit) := by
      apply (hRestrictedSpec.2.2.2.1 _ hGap).differentiableWithinAt
      norm_num
    exact hDifferentiableWithin.differentiableAt (isOpen_Ioo.mem_nhds hGap)
  have hComponentLe :
      deriv (localPhi i) (energy (u k) - energyLimit) ≤
        deriv phi (energy (u k) - energyLimit) := by
    dsimp only [phi]
    rw [deriv_fun_sum hDifferentiable]
    apply Finset.single_le_sum _ hiCover
    intro j hj
    have hRestrictedSpec :=
      (KurdykaLojasiewicz.isDesingularizer_iff eta (localPhi j)).1
        (hRestricted j hj)
    exact (hRestrictedSpec.2.2.2.2.1 _ hGap).le
  exact hChart.trans
    (mul_le_mul_of_nonneg_right hComponentLe (norm_nonneg _))

/-- Helper for Corollary 4.2: corrected compactness and the KL property imply
summability of base-step lengths together with multiplier increments. -/
private lemma summableBaseStepAndMultiplierIncrement
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (LALM.liftedEnergy f c params.rho params.beta) atTop
        run.liftedIterate) :
    Summable (fun k ↦ ‖run.baseStep k‖ +
      ‖run.multiplier (k + 1) - run.multiplier k‖) := by
  -- Compact containment and corrected lifted sufficient decrease establish the
  -- global rank used by the KL recurrence.
  obtain ⟨K, hKCompact, hKSubset, hKRange⟩ :=
    existsCompactLiftedIterateRange h params h_region run h_compact
  let length : ℕ → ℝ :=
    fun k ↦ ‖run.baseStep k‖ + ‖run.baseStep (k - 1)‖
  have hLengthNonneg : ∀ k, 0 ≤ length k :=
    fun k ↦ add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hEnergyContinuous := continuousOn_liftedEnergy h params.rho params.beta
  let energy : LiftedState n m → ℝ :=
    LALM.liftedEnergy f c params.rho params.beta
  let energyTail : ℕ → ℝ := fun k ↦ energy (run.liftedIterate (k + 1))
  have hEnergyTailAntitone : Antitone energyTail := by
    apply antitone_nat_of_succ_le
    intro k
    have hk : 1 ≤ k + 1 := by omega
    have hStep := liftedEnergyDescent h params h_region run (k + 1) hk
    have hCoefficientNonneg : 0 ≤ (params.beta : ℝ) / 16 := by
      positivity
    have hLengthSquareNonneg :
        0 ≤ (‖run.baseStep (k + 1)‖ +
          ‖run.baseStep (k + 1 - 1)‖) ^ 2 := sq_nonneg _
    dsimp only [energyTail, energy]
    nlinarith
  have hEnergyTailBddBelow : BddBelow (Set.range energyTail) := by
    have hCompactImage : BddBelow (energy '' K) :=
      hKCompact.bddBelow_image (hEnergyContinuous.mono hKSubset)
    apply hCompactImage.mono
    rintro y ⟨k, rfl⟩
    exact ⟨run.liftedIterate (k + 1), hKRange (k + 1), rfl⟩
  let energyLimit : ℝ := ⨅ k, energyTail k
  have hEnergyTailTendsto : Tendsto energyTail atTop (𝓝 energyLimit) :=
    tendsto_atTop_ciInf hEnergyTailAntitone hEnergyTailBddBelow
  have hEnergyTendsto :
      Tendsto (fun k ↦ energy (run.liftedIterate k)) atTop
        (𝓝 energyLimit) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [energyTail] using hEnergyTailTendsto
  have hClusterEnergy : ∀ xBar,
      MapClusterPt xBar atTop run.liftedIterate →
        energy xBar = energyLimit := by
    intro xBar hxBar
    obtain ⟨subsequence, hSubsequence, hLiftedSubsequence⟩ :=
      hxBar.tendsto_subseq
    have hxK : xBar ∈ K :=
      hKCompact.isClosed.mem_of_tendsto hLiftedSubsequence
        (Filter.Eventually.of_forall fun k ↦ hKRange (subsequence k))
    have hxRegion : xBar ∈ liftedRegularityRegion h := hKSubset hxK
    have hEnergyAtCluster : Tendsto
        (fun k ↦ energy (run.liftedIterate (subsequence k))) atTop
          (𝓝 (energy xBar)) := by
      have hEnergyAt : ContinuousAt energy xBar :=
        hEnergyContinuous.continuousAt
          ((isOpen_liftedRegularityRegion h).mem_nhds hxRegion)
      have hComposed := hEnergyAt.tendsto.comp hLiftedSubsequence
      simpa [Function.comp_def, energy] using hComposed
    have hEnergyAlongSubsequence : Tendsto
        (fun k ↦ energy (run.liftedIterate (subsequence k))) atTop
          (𝓝 energyLimit) :=
      hEnergyTendsto.comp hSubsequence.tendsto_atTop
    exact tendsto_nhds_unique hEnergyAtCluster hEnergyAlongSubsequence
  have hSummableLength : Summable length := by
    -- Uniformize the KL inequality on the compact cluster set, then compare
    -- its lifted gradient with the corrected adjacent-step length.
    obtain ⟨eta, hEtaPos, phi, hPhi, hUniformKL⟩ :=
      eventually_uniformKL_of_compactCluster energy run.liftedIterate K
        hKCompact hKRange h_KL energyLimit hClusterEnergy
    obtain ⟨B, hBPos, hGradientBound⟩ :=
      norm_gradient_liftedEnergy_liftedIterate_succ_le h params h_region run
    let gap : ℕ → ℝ := fun k ↦ energyTail k - energyLimit
    let coefficient : ℝ := (params.beta : ℝ) / 16
    let potential : ℕ → ℝ := fun k ↦
      (B / coefficient) * phi (gap k)
    have hCoefficientPos : 0 < coefficient := by
      dsimp only [coefficient]
      apply div_pos run.beta_pos
      norm_num
    have hGapNonneg : ∀ k, 0 ≤ gap k := by
      intro k
      dsimp only [gap]
      exact sub_nonneg.mpr
        (hEnergyTailAntitone.le_of_tendsto hEnergyTailTendsto k)
    have hGapAntitone : Antitone gap := by
      intro i j hij
      dsimp only [gap]
      exact sub_le_sub_right (hEnergyTailAntitone hij) energyLimit
    have hGapTendsto : Tendsto gap atTop (𝓝 0) := by
      have hConstant : Tendsto (fun _ : ℕ ↦ energyLimit) atTop
          (𝓝 energyLimit) := tendsto_const_nhds
      dsimp only [gap]
      simpa only [sub_self] using hEnergyTailTendsto.sub hConstant
    have hGapLt : ∀ᶠ k in atTop, gap k < eta :=
      hGapTendsto (Iio_mem_nhds hEtaPos)
    have hUniformKLShift : ∀ᶠ k in atTop,
        0 < gap k → gap k < eta →
          1 ≤ deriv phi (gap k) *
            ‖gradient energy (run.liftedIterate (k + 1))‖ := by
      have hShifted := (tendsto_add_atTop_nat 1) hUniformKL
      filter_upwards [hShifted] with k hk
      intro hGapPos hGapUpper
      apply hk
      · dsimp only [gap, energyTail] at hGapPos ⊢
        linarith
      · dsimp only [gap, energyTail] at hGapUpper ⊢
        linarith
    have hPhiSpec :=
      (KurdykaLojasiewicz.isDesingularizer_iff eta phi).1 hPhi
    have hEventualRecurrence : ∀ᶠ k in atTop,
        2 * length (k + 1) ≤
          length k + potential k - potential (k + 1) := by
      filter_upwards [hUniformKLShift, hGapLt, eventually_ge_atTop 1]
        with k hKLAt hGapUpper hk
      have hGapNextLe : gap (k + 1) ≤ gap k :=
        hGapAntitone (Nat.le_succ k)
      have hGapNextUpper : gap (k + 1) < eta :=
        hGapNextLe.trans_lt hGapUpper
      have hDescentStep : coefficient * length (k + 1) ^ 2 ≤
          gap k - gap (k + 1) := by
        have hkNext : 1 ≤ k + 1 := by omega
        have hStep :=
          liftedEnergyDescent h params h_region run (k + 1) hkNext
        dsimp only [coefficient, length, gap, energyTail, energy]
        nlinarith
      by_cases hGapZero : gap k = 0
      · have hGapNextZero : gap (k + 1) = 0 := by
          have hNextNonneg := hGapNonneg (k + 1)
          nlinarith
        have hLengthNextZero : length (k + 1) = 0 := by
          rw [hGapZero, hGapNextZero, sub_self] at hDescentStep
          have hProductZero : coefficient * length (k + 1) ^ 2 = 0 :=
            le_antisymm hDescentStep
              (mul_nonneg hCoefficientPos.le (sq_nonneg _))
          have hSquareZero : length (k + 1) ^ 2 = 0 :=
            (mul_eq_zero.mp hProductZero).resolve_left hCoefficientPos.ne'
          exact sq_eq_zero_iff.mp hSquareZero
        dsimp only [potential]
        rw [hGapZero, hGapNextZero, hPhiSpec.2.2.1, hLengthNextZero]
        simpa only [mul_zero, zero_mul, add_zero, sub_zero] using
          hLengthNonneg k
      · have hGapPos : 0 < gap k :=
          lt_of_le_of_ne (hGapNonneg k) (Ne.symm hGapZero)
        have hDerivPos : 0 < deriv phi (gap k) :=
          hPhiSpec.2.2.2.2.1 _ ⟨hGapPos, hGapUpper⟩
        have hRelative :
            1 ≤ deriv phi (gap k) * (B * length k) := by
          calc
            1 ≤ deriv phi (gap k) *
                ‖gradient energy (run.liftedIterate (k + 1))‖ :=
              hKLAt hGapPos hGapUpper
            _ ≤ deriv phi (gap k) * (B * length k) := by
              apply mul_le_mul_of_nonneg_left _ hDerivPos.le
              simpa only [energy, length] using hGradientBound k hk
        by_cases hGapEqual : gap (k + 1) = gap k
        · have hLengthNextZero : length (k + 1) = 0 := by
            rw [hGapEqual, sub_self] at hDescentStep
            have hProductZero : coefficient * length (k + 1) ^ 2 = 0 :=
              le_antisymm hDescentStep
                (mul_nonneg hCoefficientPos.le (sq_nonneg _))
            have hSquareZero : length (k + 1) ^ 2 = 0 :=
              (mul_eq_zero.mp hProductZero).resolve_left hCoefficientPos.ne'
            exact sq_eq_zero_iff.mp hSquareZero
          dsimp only [potential]
          rw [hGapEqual, hLengthNextZero]
          nlinarith [hLengthNonneg k]
        · have hGapStrict : gap (k + 1) < gap k :=
            lt_of_le_of_ne hGapNextLe hGapEqual
          have hGapMem : gap k ∈ Set.Ioo 0 eta := ⟨hGapPos, hGapUpper⟩
          have hDifferentiableWithin :
              DifferentiableWithinAt ℝ phi (Set.Ioo 0 eta) (gap k) := by
            apply (hPhiSpec.2.2.2.1 _ hGapMem).differentiableWithinAt
            norm_num
          have hDifferentiable : DifferentiableAt ℝ phi (gap k) :=
            hDifferentiableWithin.differentiableAt (isOpen_Ioo.mem_nhds hGapMem)
          have hSlope := hPhiSpec.2.2.2.2.2.deriv_le_slope
            ⟨hGapNonneg (k + 1), hGapNextUpper⟩
            ⟨hGapPos.le, hGapUpper⟩ hGapStrict hDifferentiable
          have hConcavityProduct :
              deriv phi (gap k) * (gap k - gap (k + 1)) ≤
                phi (gap k) - phi (gap (k + 1)) := by
            rw [slope_def_field] at hSlope
            exact (le_div_iff₀ (sub_pos.mpr hGapStrict)).1 hSlope
          have hPhiDrop : coefficient * deriv phi (gap k) *
                length (k + 1) ^ 2 ≤
              phi (gap k) - phi (gap (k + 1)) := by
            calc
              coefficient * deriv phi (gap k) * length (k + 1) ^ 2 =
                  deriv phi (gap k) *
                    (coefficient * length (k + 1) ^ 2) := by ring
              _ ≤ deriv phi (gap k) * (gap k - gap (k + 1)) :=
                mul_le_mul_of_nonneg_left hDescentStep hDerivPos.le
              _ ≤ phi (gap k) - phi (gap (k + 1)) := hConcavityProduct
          have hScaledSquare : coefficient * length (k + 1) ^ 2 ≤
              B * length k *
                (phi (gap k) - phi (gap (k + 1))) := by
            calc
              coefficient * length (k + 1) ^ 2 =
                  1 * (coefficient * length (k + 1) ^ 2) := by ring
              _ ≤ (deriv phi (gap k) * (B * length k)) *
                    (coefficient * length (k + 1) ^ 2) :=
                mul_le_mul_of_nonneg_right hRelative
                  (mul_nonneg hCoefficientPos.le (sq_nonneg _))
              _ = B * length k *
                  (coefficient * deriv phi (gap k) *
                    length (k + 1) ^ 2) := by ring
              _ ≤ B * length k *
                  (phi (gap k) - phi (gap (k + 1))) :=
                mul_le_mul_of_nonneg_left hPhiDrop
                  (mul_nonneg hBPos.le (hLengthNonneg k))
          let drop : ℝ :=
            (B / coefficient) * (phi (gap k) - phi (gap (k + 1)))
          have hDropNonneg : 0 ≤ drop := by
            dsimp only [drop]
            have hPhiDropNonneg :
                0 ≤ phi (gap k) - phi (gap (k + 1)) :=
              le_trans (mul_nonneg
                (mul_nonneg hCoefficientPos.le hDerivPos.le) (sq_nonneg _))
                hPhiDrop
            exact mul_nonneg (div_nonneg hBPos.le hCoefficientPos.le)
              hPhiDropNonneg
          have hSquareProduct : length (k + 1) ^ 2 ≤ length k * drop := by
            dsimp only [drop]
            calc
              length (k + 1) ^ 2 ≤
                  (B * length k *
                    (phi (gap k) - phi (gap (k + 1)))) / coefficient := by
                apply (le_div_iff₀ hCoefficientPos).2
                simpa only [mul_comm] using hScaledSquare
              _ = length k * ((B / coefficient) *
                    (phi (gap k) - phi (gap (k + 1)))) := by ring
          have hTwoSquare :
              (2 * length (k + 1)) ^ 2 ≤ (length k + drop) ^ 2 := by
            nlinarith [sq_nonneg (length k - drop)]
          have hTwoLengthNonneg : 0 ≤ 2 * length (k + 1) := by
            positivity
          have hTwoLength :
              2 * length (k + 1) ≤ length k + drop :=
            (sq_le_sq₀ hTwoLengthNonneg
              (add_nonneg (hLengthNonneg _) hDropNonneg)).1 hTwoSquare
          calc
            2 * length (k + 1) ≤ length k + drop := hTwoLength
            _ = length k + potential k - potential (k + 1) := by
              dsimp only [drop, potential]
              ring
    -- Shift past the eventual threshold and telescope the desingularized energy
    -- drops with the generic scalar summability lemma.
    have hEventualGood : ∀ᶠ k in atTop,
        (2 * length (k + 1) ≤
          length k + potential k - potential (k + 1)) ∧ gap k < eta :=
      hEventualRecurrence.and hGapLt
    obtain ⟨N, hTail⟩ := eventually_atTop.1 hEventualGood
    rw [← summable_nat_add_iff N]
    apply summable_of_two_mul_shift_le
      (fun k ↦ length (k + N)) (fun k ↦ potential (k + N))
    · intro k
      exact hLengthNonneg (k + N)
    · intro k
      have hNLe : N ≤ k + N := by omega
      have hGood := hTail (k + N) hNLe
      have hGapMem : gap (k + N) ∈ Set.Ico 0 eta :=
        ⟨hGapNonneg (k + N), hGood.2⟩
      dsimp only [potential]
      exact mul_nonneg (div_nonneg hBPos.le hCoefficientPos.le)
        (hPhiSpec.1 hGapMem)
    · intro k
      have hNLe : N ≤ k + N := by omega
      have hGood := hTail (k + N) hNLe
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hGood.1
  -- The corrected multiplier comparison converts adjacent base-step length to
  -- the base-step-plus-multiplier series required by the corollary.
  apply summableBaseStepAndMultiplierIncrement_of_summableTwoStep
    h params h_region run
  simpa only [length] using hSummableLength

/-- Corollary 4.2 (22): compactness of the corrected sublevel and the
Kurdyka--Łojasiewicz property at every corrected lifted cluster point imply
finite point--multiplier length. -/
theorem summablePointAndMultiplierIncrement
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (LALM.liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    Summable (fun k ↦ ‖run.point (k + 1) - run.point k‖ +
      ‖run.multiplier (k + 1) - run.multiplier k‖) := by
  -- First separate the two nonnegative components of the corrected KL length.
  have hLength :=
    summableBaseStepAndMultiplierIncrement h params h_region run h_compact h_KL
  have hBaseStep : Summable (fun k ↦ ‖run.baseStep k‖) :=
    hLength.of_nonneg_of_le (fun k ↦ norm_nonneg (run.baseStep k))
      (fun k ↦ le_add_of_nonneg_right (norm_nonneg _))
  have hMultiplier : Summable
      (fun k ↦ ‖run.multiplier (k + 1) - run.multiplier k‖) :=
    hLength.of_nonneg_of_le (fun k ↦ norm_nonneg _)
      (fun k ↦ le_add_of_nonneg_left (norm_nonneg _))
  have hFactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hScaledBaseStep : Summable
      (fun k ↦ displacementFactor h params.delta * ‖run.baseStep k‖) :=
    hBaseStep.mul_left (displacementFactor h params.delta)
  have hPoint : Summable
      (fun k ↦ ‖run.point (k + 1) - run.point k‖) := by
    apply hScaledBaseStep.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · intro k
      have hPrefix := allPrefixesAdmissible h params h_region run (k + 1)
      have hTransition := (run.isAdmissiblePrefix_iff h (k + 1)).1 hPrefix k
        (Nat.lt_succ_self k)
      have hBaseStepBound := run.norm_baseStep_le h params hPrefix
        (Nat.lt_succ_self k)
      have hDisplacement := displacement_le h params.delta (run.point k)
        (run.baseStep k) hTransition hBaseStepBound
      rw [← run.point_succ k] at hDisplacement
      exact hDisplacement
  -- Add the transported primal series to the multiplier-increment series.
  exact hPoint.add hMultiplier

/-- Helper for Corollary 4.2: corrected stationarity varies continuously on
primal--multiplier pairs whose primal coordinate lies in the regularity region. -/
private lemma continuousOn_stationarity
    (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        KKT.stationarity f c z.1 z.2)
      (pairRegularityRegion h) := by
  intro z hz
  change z.1 ∈ h.region at hz
  have hGradient : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f z.1) z :=
    (h.continuousAt_gradient hz).comp continuous_fst.continuousAt
  have hConstraintGradient : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        EqualityConstrained.constraintGradient c z.1) z :=
    (h.continuousAt_constraintGradient hz).comp continuous_fst.continuousAt
  have hStationarity : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        gradient f z.1 + EqualityConstrained.constraintGradient c z.1 z.2) z :=
    hGradient.add (hConstraintGradient.clm_apply continuous_snd.continuousAt)
  apply ContinuousAt.continuousWithinAt
  simpa only [KKT.stationarity_def] using hStationarity

/-- Helper for Corollary 4.2: the corrected aggregate KKT residual is
continuous wherever the primal coordinate lies in the regularity region. -/
private lemma continuousOn_residual
    (h : EqualityConstrained.Regularity f c) :
    ContinuousOn
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        KKT.residual f c z.1 z.2)
      (pairRegularityRegion h) := by
  intro z hz
  have hzPair : z ∈ pairRegularityRegion h := hz
  have hStationarity : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        KKT.stationarity f c z.1 z.2) z :=
    (continuousOn_stationarity h).continuousAt
      ((isOpen_pairRegularityRegion h).mem_nhds hzPair)
  change z.1 ∈ h.region at hz
  have hConstraint : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦ c z.1) z :=
    (h.continuousAt_constraint hz).comp continuous_fst.continuousAt
  have hResidualSquare : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        ‖KKT.stationarity f c z.1 z.2‖ ^ 2 + ‖c z.1‖ ^ 2) z :=
    (hStationarity.norm.pow 2).add (hConstraint.norm.pow 2)
  have hResidual : ContinuousAt
      (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        Real.sqrt (‖KKT.stationarity f c z.1 z.2‖ ^ 2 + ‖c z.1‖ ^ 2)) z :=
    Real.continuous_sqrt.continuousAt.comp hResidualSquare
  apply ContinuousAt.continuousWithinAt
  simpa only [KKT.residual_def] using hResidual

/-- Helper for Corollary 4.2: finite corrected KL length yields a lifted KKT
limit whose preceding base-step coordinate vanishes. -/
private theorem existsLiftedKKTLimit
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (LALM.liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    ∃ limit : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      KKT.IsPair f c limit.1 limit.2 ∧
        Tendsto run.liftedIterate atTop
          (𝓝 (liftedState limit.1 limit.2 0)) := by
  -- Separate the corrected base-step length and both physical trajectory
  -- components from the two finite-length theorems.
  have hBaseLength :=
    summableBaseStepAndMultiplierIncrement h params h_region run h_compact h_KL
  have hBaseStepNorm : Summable (fun k ↦ ‖run.baseStep k‖) :=
    hBaseLength.of_nonneg_of_le (fun k ↦ norm_nonneg (run.baseStep k))
      (fun k ↦ le_add_of_nonneg_right (norm_nonneg _))
  have hPairLength :=
    summablePointAndMultiplierIncrement h params h_region run h_compact h_KL
  have hPointIncrementNorm :
      Summable (fun k ↦ ‖run.point (k + 1) - run.point k‖) :=
    hPairLength.of_nonneg_of_le (fun k ↦ norm_nonneg _)
      (fun k ↦ le_add_of_nonneg_right (norm_nonneg _))
  have hMultiplierIncrementNorm :
      Summable (fun k ↦ ‖run.multiplier (k + 1) - run.multiplier k‖) :=
    hPairLength.of_nonneg_of_le (fun k ↦ norm_nonneg _)
      (fun k ↦ le_add_of_nonneg_left (norm_nonneg _))
  have hPointDistance :
      Summable (fun k ↦ dist (run.point k) (run.point k.succ)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hPointIncrementNorm
  have hMultiplierDistance :
      Summable (fun k ↦ dist (run.multiplier k) (run.multiplier k.succ)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hMultiplierIncrementNorm
  -- Completeness converts finite total variation into limits of the primal and
  -- multiplier sequences; summability also makes the base step vanish.
  obtain ⟨xStar, hPoint⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hPointDistance)
  obtain ⟨multiplierStar, hMultiplier⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hMultiplierDistance)
  have hBaseStep : Tendsto run.baseStep atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hBaseStepNorm.tendsto_atTop_zero
  have hPreviousBaseStep : Tendsto (fun k ↦ run.baseStep (k - 1)) atTop (𝓝 0) :=
    hBaseStep.comp (tendsto_sub_atTop_nat 1)
  have hLifted : Tendsto run.liftedIterate atTop
      (𝓝 (liftedState xStar multiplierStar 0)) := by
    have hCoordinates := hPoint.prodMk_nhds
      (hMultiplier.prodMk_nhds hPreviousBaseStep)
    have hAssembly : Continuous
        (fun z : EuclideanSpace ℝ (Fin n) ×
            (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦
          liftedState z.1 z.2.1 z.2.2) := by
      unfold liftedState
      fun_prop
    have hAssembled :=
      (hAssembly.tendsto (xStar, multiplierStar, 0)).comp hCoordinates
    apply hAssembled.congr
    intro k
    simp only [Function.comp_apply, run.liftedIterate_apply]
  obtain ⟨K, hKCompact, hKSubset, hKRange⟩ :=
    existsCompactLiftedIterateRange h params h_region run h_compact
  have hLiftedLimitMemK : liftedState xStar multiplierStar 0 ∈ K :=
    hKCompact.isClosed.mem_of_tendsto hLifted
      (Filter.Eventually.of_forall hKRange)
  have hLiftedLimitRegion :
      liftedState xStar multiplierStar 0 ∈ liftedRegularityRegion h :=
    hKSubset hLiftedLimitMemK
  have hPairLimitRegion : (xStar, multiplierStar) ∈ pairRegularityRegion h := by
    change xStar ∈ h.region
    exact hLiftedLimitRegion
  -- The corrected residual comparison and the two vanishing adjacent base
  -- steps force the residual at the successor iterates to zero.
  let comparison := Residual.comparisonConstant
    (primalComparisonConstant h params.delta params.beta params.rho
      params.multiplierBound)
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound) params.rho
  have hBaseStepNormZero : Tendsto (fun k ↦ ‖run.baseStep k‖) atTop (𝓝 0) :=
    hBaseStepNorm.tendsto_atTop_zero
  have hPreviousBaseStepNormZero :
      Tendsto (fun k ↦ ‖run.baseStep (k - 1)‖) atTop (𝓝 0) :=
    hBaseStepNormZero.comp (tendsto_sub_atTop_nat 1)
  have hComparisonZero :
      Tendsto (fun k ↦ comparison *
        (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [pow_two, zero_mul, add_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ comparison) atTop (𝓝 comparison)).mul
        ((hBaseStepNormZero.pow 2).add (hPreviousBaseStepNormZero.pow 2))
  have hResidualSqBound : ∀ᶠ k in atTop,
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2 ≤
        comparison * (‖run.baseStep k‖ ^ 2 + ‖run.baseStep (k - 1)‖ ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact residual_sq_le h params run
      (allPrefixesAdmissible h params h_region run (k + 1)) hk
        (Nat.lt_succ_self k)
  have hResidualSq : Tendsto (fun k ↦
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun k ↦ sq_nonneg _) hResidualSqBound
      hComparisonZero
  have hResidual : Tendsto (fun k ↦
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)))
      atTop (𝓝 0) := by
    have hSqrt : Tendsto (fun k ↦ Real.sqrt
        (KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2))
        atTop (𝓝 0) := by
      have hComposed := (Real.continuous_sqrt.tendsto 0).comp hResidualSq
      have hAtZero : Tendsto ((fun x ↦ Real.sqrt x) ∘ fun k ↦
          KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1)) ^ 2)
          atTop (𝓝 0) := by
        simpa only [Real.sqrt_zero] using hComposed
      apply hAtZero.congr
      intro k
      rfl
    apply hSqrt.congr
    intro k
    apply Real.sqrt_sq
    rw [KKT.residual_def]
    exact Real.sqrt_nonneg _
  -- Continuity identifies the residual limit, so the limiting primal and
  -- multiplier coordinates satisfy the exact KKT equations.
  have hPair := hPoint.prodMk_nhds hMultiplier
  have hPairSucc := hPair.comp (tendsto_add_atTop_nat 1)
  have hResidualAtLimit : Tendsto (fun k ↦
      KKT.residual f c (run.point (k + 1)) (run.multiplier (k + 1))) atTop
      (𝓝 (KKT.residual f c xStar multiplierStar)) := by
    have hResidualContinuousAt : ContinuousAt
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
          KKT.residual f c z.1 z.2) (xStar, multiplierStar) :=
      (continuousOn_residual h).continuousAt
        ((isOpen_pairRegularityRegion h).mem_nhds hPairLimitRegion)
    have hContinuous := hResidualContinuousAt.tendsto.comp hPairSucc
    apply hContinuous.congr
    intro k
    simp only [Function.comp_apply]
  have hResidualZero : KKT.residual f c xStar multiplierStar = 0 :=
    tendsto_nhds_unique hResidualAtLimit hResidual
  have hKKT : KKT.IsPair f c xStar multiplierStar := by
    have hResidualLe : KKT.residual f c xStar multiplierStar ≤ 0 := by
      rw [hResidualZero]
    have hApproximate : KKT.IsApproximatePair f c 0 xStar multiplierStar :=
      KKT.IsApproximatePair.of_residual_le hResidualLe
    apply (KKT.isPair_iff f c xStar multiplierStar).2
    constructor
    · have hStationarityNorm :
          ‖KKT.stationarity f c xStar multiplierStar‖ = 0 := by
        apply norm_le_zero_iff.mp
        simpa using hApproximate.stationarity_le
      exact norm_eq_zero.mp hStationarityNorm
    · have hFeasibilityNorm : ‖c xStar‖ = 0 := by
        apply norm_le_zero_iff.mp
        simpa using hApproximate.feasibility_le
      exact norm_eq_zero.mp hFeasibilityNorm
  exact ⟨(xStar, multiplierStar), hKKT, hLifted⟩

/-- Corollary 4.2 (23): under the same compactness and KL conditions, the full
corrected point--multiplier sequence converges to a KKT pair. -/
theorem existsKKTLimit
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (h_region : DeterministicRegionCondition h params)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    (h_compact : IsCompact (deterministicSublevel h params))
    (h_KL : KurdykaLojasiewicz.HasAtClusterPoints
      (LALM.liftedEnergy f c params.rho params.beta) atTop run.liftedIterate) :
    ∃ limit : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m),
      KKT.IsPair f c limit.1 limit.2 ∧
        Tendsto (fun k ↦ (run.point k, run.multiplier k)) atTop (𝓝 limit) := by
  -- Project the lifted KKT limit onto the primal and multiplier coordinates.
  obtain ⟨limit, hLimit, hLifted⟩ :=
    existsLiftedKKTLimit h params h_region run h_compact h_KL
  exact ⟨limit, hLimit,
    run.pairTendsto_of_liftedTendsto limit.1 limit.2 hLifted⟩

end Run

end LALM.Correction

end
