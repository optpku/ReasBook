/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Assumption_2_3.Parameters
public import TR_LALM_theory.Proposition_4_1.Step

public section

open scoped NNReal

namespace LALM.Correction

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The corrected model-descent constant. -/
@[expose] noncomputable def modelConstant (h : EqualityConstrained.Regularity f c)
    (delta rho multiplierBound : ℝ) : ℝ :=
  h.gradientBound * stepConstant h +
    (h.gradientLipschitz / 2) * displacementFactor h delta ^ 2 +
    errorFactor h delta *
      (3 * multiplierBound + rho * h.constraintGradientBound * delta) +
    (rho / 2) * errorFactor h delta ^ 2 * delta ^ 2

/-- The corrected model constant has the source formula. -/
theorem modelConstant_def (h : EqualityConstrained.Regularity f c)
    (delta rho multiplierBound : ℝ) :
    modelConstant h delta rho multiplierBound =
      h.gradientBound * stepConstant h +
        (h.gradientLipschitz / 2) * displacementFactor h delta ^ 2 +
        errorFactor h delta *
          (3 * multiplierBound + rho * h.constraintGradientBound * delta) +
        (rho / 2) * errorFactor h delta ^ 2 * delta ^ 2 := rfl

/-- The corrected primal-step constant. -/
@[expose] noncomputable def primalConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho : ℝ) : ℝ :=
  beta + rho * h.constraintGradientBound * errorFactor h delta * delta

/-- The corrected primal-step constant has the source formula. -/
theorem primalConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho : ℝ) :
    primalConstant h delta beta rho =
      beta + rho * h.constraintGradientBound * errorFactor h delta * delta := rfl

/-- The corrected comparison constant for the primal step. -/
@[expose] noncomputable def primalComparisonConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  primalConstant h delta beta rho +
    (h.gradientLipschitz + h.constraintGradientLipschitz * multiplierBound) *
      displacementFactor h delta

/-- The corrected primal comparison constant has the source formula. -/
theorem primalComparisonConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    primalComparisonConstant h delta beta rho multiplierBound =
      primalConstant h delta beta rho +
        (h.gradientLipschitz + h.constraintGradientLipschitz * multiplierBound) *
          displacementFactor h delta := rfl

/-- The corrected multiplier-primal comparison constant. -/
@[expose] noncomputable def multiplierPrimalConstant
    (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  (4 / h.licqModulus ^ 2) *
    max ((primalConstant h delta beta rho) ^ 2)
      ((primalComparisonConstant h delta beta rho multiplierBound) ^ 2)

/-- The corrected multiplier-primal constant has the source formula. -/
theorem multiplierPrimalConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    multiplierPrimalConstant h delta beta rho multiplierBound =
      (4 / h.licqModulus ^ 2) *
        max ((primalConstant h delta beta rho) ^ 2)
          ((primalComparisonConstant h delta beta rho multiplierBound) ^ 2) := rfl

/-- The corrected stationarity constant. -/
@[expose] noncomputable def stationarityConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  beta + rho * h.constraintGradientBound * errorFactor h delta * delta +
    (h.gradientLipschitz + h.constraintGradientLipschitz * multiplierBound) *
      displacementFactor h delta

/-- The corrected stationarity constant has the source formula. -/
theorem stationarityConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    stationarityConstant h delta beta rho multiplierBound =
      beta + rho * h.constraintGradientBound * errorFactor h delta * delta +
        (h.gradientLipschitz + h.constraintGradientLipschitz * multiplierBound) *
          displacementFactor h delta := rfl

/-- The stationarity and primal comparison constants agree while retaining their
distinct analytical roles. -/
theorem stationarityConstant_eq_primalComparisonConstant
    (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    stationarityConstant h delta beta rho multiplierBound =
      primalComparisonConstant h delta beta rho multiplierBound := rfl

/-- Positive scalar NR-LALM+SOC parameters satisfying the initialization-independent
admissibility bounds. -/
structure AdmissibleParameters (h : EqualityConstrained.Regularity f c) where
  /-- The corrected step-radius parameter. -/
  delta : NNRealˣ
  /-- The corrected proximal parameter. -/
  beta : NNRealˣ
  /-- The corrected penalty parameter. -/
  rho : NNRealˣ
  /-- The corrected multiplier bound. -/
  multiplierBound : NNRealˣ
  /-- The multiplier bound dominates the corrected parameter expression. -/
  parameterBound_le :
    ((h.gradientBound + beta * delta +
      rho * h.constraintGradientBound * errorFactor h delta * delta ^ 2) /
        h.licqModulus : ℝ) ≤ multiplierBound
  /-- The step radius satisfies the common comparison inequality. -/
  comparisonBound_le :
    (h.gradientBound / beta +
      3 * h.constraintGradientBound * multiplierBound /
        (beta + rho * h.licqModulus ^ 2) : ℝ) ≤ delta
  /-- The corrected model constant is at most three eighths of the proximal parameter. -/
  modelConstant_le : modelConstant h delta rho multiplierBound ≤ 3 * beta / 8
  /-- The penalty parameter dominates the corrected multiplier-primal constant. -/
  multiplierPrimalConstant_le :
    8 * multiplierPrimalConstant h delta beta rho multiplierBound / beta ≤ rho

namespace AdmissibleParameters

/-- Construct a corrected parameter certificate from explicit values and proofs of all
four initialization-independent source conditions. -/
def ofValues (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : NNRealˣ)
    (parameterBound_le :
      ((h.gradientBound + beta * delta +
        rho * h.constraintGradientBound * errorFactor h delta * delta ^ 2) /
          h.licqModulus : ℝ) ≤ multiplierBound)
    (comparisonBound_le :
      (h.gradientBound / beta +
        3 * h.constraintGradientBound * multiplierBound /
          (beta + rho * h.licqModulus ^ 2) : ℝ) ≤ delta)
    (modelConstant_le : modelConstant h delta rho multiplierBound ≤ 3 * beta / 8)
    (multiplierPrimalConstant_le :
      8 * multiplierPrimalConstant h delta beta rho multiplierBound / beta ≤ rho) :
    AdmissibleParameters h :=
  { delta
    beta
    rho
    multiplierBound
    parameterBound_le
    comparisonBound_le
    modelConstant_le
    multiplierPrimalConstant_le }

/-- The corrected parameters viewed in the real scalar domain used by the algorithm. -/
@[expose] def values {h : EqualityConstrained.Regularity f c}
    (params : AdmissibleParameters h) : ℝ × ℝ × ℝ × ℝ :=
  (params.delta, params.beta, params.rho, params.multiplierBound)

/-- The real-coordinate view lists the step radius, proximal parameter, penalty,
and multiplier bound in that order. -/
theorem values_def {h : EqualityConstrained.Regularity f c}
    (params : AdmissibleParameters h) :
    params.values =
      ((params.delta : ℝ), (params.beta : ℝ), (params.rho : ℝ),
        (params.multiplierBound : ℝ)) := rfl

/-- A corrected admissible parameter certificate exposes its positivity and four
initialization-independent inequalities. -/
theorem spec {h : EqualityConstrained.Regularity f c}
    (params : AdmissibleParameters h) :
    ((0 : ℝ) < params.delta ∧ (0 : ℝ) < params.beta ∧
      (0 : ℝ) < params.rho ∧ (0 : ℝ) < params.multiplierBound) ∧
    (((h.gradientBound + params.beta * params.delta +
      params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta ^ 2) / h.licqModulus : ℝ) ≤ params.multiplierBound ∧
      (h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * h.licqModulus ^ 2) : ℝ) ≤ params.delta ∧
      modelConstant h params.delta params.rho params.multiplierBound ≤
        3 * params.beta / 8 ∧
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.beta ≤ params.rho) := by
  -- Positivity comes from the unit-valued coordinates; the inequalities are fields.
  constructor
  · constructor
    · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.delta.ne_zero)
    · constructor
      · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.beta.ne_zero)
      · constructor
        · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.rho.ne_zero)
        · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.multiplierBound.ne_zero)
  · exact ⟨params.parameterBound_le, params.comparisonBound_le,
      params.modelConstant_le, params.multiplierPrimalConstant_le⟩

/-- Helper for Proposition 4.1: on a nonempty regularity region with a positive-dimensional
constraint space, the constraint-gradient norm bound dominates the LICQ modulus. -/
private lemma licqModulus_le_constraintGradientBound
    {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) :
    (h.licqModulus : ℝ) ≤ h.constraintGradientBound := by
  -- Test both regularity bounds on a unit coordinate vector at a point of the region.
  obtain ⟨x, hx⟩ := h.nonempty_region
  let i : Fin m := ⟨0, hm⟩
  let u : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
  have huNorm : ‖u‖ = 1 := by simp [u]
  calc
    (h.licqModulus : ℝ) = (h.licqModulus : ℝ) * ‖u‖ := by rw [huNorm, mul_one]
    _ ≤ ‖EqualityConstrained.constraintGradient c x u‖ := h.licqLowerBound x hx u
    _ ≤ ‖EqualityConstrained.constraintGradient c x‖ * ‖u‖ :=
      (EqualityConstrained.constraintGradient c x).le_opNorm u
    _ ≤ h.constraintGradientBound * ‖u‖ := by
      gcongr
      exact h.norm_constraintGradient_le x hx
    _ = h.constraintGradientBound := by rw [huNorm, mul_one]

/-- Helper for Proposition 4.1: base admissibility forces the normalized correction
radius `stepConstant h * base.delta` to be at most `1 / 8`. -/
private lemma stepConstant_mul_delta_le_eighth
    {h : EqualityConstrained.Regularity f c}
    (base : LALM.AdmissibleParameters h) :
    stepConstant h * base.delta ≤ 1 / 8 := by
  have hsigmaPos : (0 : ℝ) < h.licqModulus :=
    NNReal.coe_pos.2 h.licqModulus_pos
  have hbetaPos : (0 : ℝ) < base.beta :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 base.beta.ne_zero)
  have hdeltaNonneg : (0 : ℝ) ≤ base.delta := by positivity
  have hrhoNonneg : (0 : ℝ) ≤ base.rho := by positivity
  have hmultiplierNonneg : (0 : ℝ) ≤ base.multiplierBound := by positivity
  have hlinearizationNonneg : 0 ≤ LALM.linearizationConstant h := by positivity
  have hparameterNumerator :=
    (div_le_iff₀ hsigmaPos).mp base.parameterBound_le
  have hbetaDelta :
      (base.beta : ℝ) * base.delta ≤
        (base.multiplierBound : ℝ) * h.licqModulus := by
    have hgradientNonneg : (0 : ℝ) ≤ h.gradientBound := by positivity
    have hconstraintGradientNonneg : (0 : ℝ) ≤ h.constraintGradientBound := by
      positivity
    calc
      (base.beta : ℝ) * base.delta ≤
          h.gradientBound + base.beta * base.delta +
            base.rho * h.constraintGradientBound * LALM.linearizationConstant h *
              base.delta ^ 2 := by
        have hremainingNonneg :
            0 ≤ (base.rho : ℝ) * h.constraintGradientBound *
              LALM.linearizationConstant h * base.delta ^ 2 := by positivity
        linarith
      _ ≤ (base.multiplierBound : ℝ) * h.licqModulus := hparameterNumerator
  have hmodel := base.modelConstant_le
  rw [LALM.modelConstant_def] at hmodel
  have hlinearizationMultiplier :
      LALM.linearizationConstant h * base.multiplierBound ≤
        (base.beta : ℝ) / 8 := by
    have hgradientLipschitzNonneg : (0 : ℝ) ≤ h.gradientLipschitz := by positivity
    have hconstraintGradientNonneg : (0 : ℝ) ≤ h.constraintGradientBound := by
      positivity
    have hpenaltyTermNonneg :
        0 ≤ (base.rho : ℝ) / 2 * LALM.linearizationConstant h ^ 2 *
          base.delta ^ 2 := by positivity
    have hmixedTermNonneg :
        0 ≤ LALM.linearizationConstant h *
          ((base.rho : ℝ) * h.constraintGradientBound * base.delta) := by positivity
    nlinarith
  have hdeltaUpper :
      (base.delta : ℝ) ≤
        (base.multiplierBound : ℝ) * h.licqModulus / base.beta := by
    apply (le_div_iff₀ hbetaPos).mpr
    simpa only [mul_comm] using hbetaDelta
  have hstepConstantNonneg : 0 ≤ stepConstant h := by
    rw [stepConstant_def]
    positivity
  calc
    stepConstant h * base.delta ≤
        stepConstant h *
          ((base.multiplierBound : ℝ) * h.licqModulus / base.beta) := by
      gcongr
    _ = LALM.linearizationConstant h * base.multiplierBound / base.beta := by
      rw [stepConstant_def, LALM.linearizationConstant_def]
      norm_num [NNReal.coe_div]
      field_simp [ne_of_gt hsigmaPos]
    _ ≤ 1 / 8 := by
      apply (div_le_iff₀ hbetaPos).mpr
      nlinarith

/-- Helper for Proposition 4.1: the corrected error factor is the base linearization
constant times the square of the normalized correction radius. -/
private lemma errorFactor_eq_linearizationConstant_mul_sq_stepConstant
    (h : EqualityConstrained.Regularity f c) (delta : ℝ) :
    errorFactor h delta = LALM.linearizationConstant h *
      (stepConstant h * delta) ^ 2 := by
  rw [errorFactor_def, errorConstant_def, stepConstant_def,
    LALM.linearizationConstant_def]
  norm_num [NNReal.coe_div]
  field_simp [ne_of_gt (NNReal.coe_pos.2 h.licqModulus_pos)]
  ring

/-- Helper for Proposition 4.1: the corrected error factor is no larger than the
base linearization constant under base admissibility. -/
private lemma errorFactor_le_linearizationConstant
    {h : EqualityConstrained.Regularity f c}
    (base : LALM.AdmissibleParameters h) :
    errorFactor h base.delta ≤ LALM.linearizationConstant h := by
  have ht := stepConstant_mul_delta_le_eighth base
  have htNonneg : 0 ≤ stepConstant h * (base.delta : ℝ) := by
    rw [stepConstant_def]
    positivity
  have hlinearizationNonneg : 0 ≤ LALM.linearizationConstant h := by positivity
  have htSq : (stepConstant h * (base.delta : ℝ)) ^ 2 ≤ 1 := by
    nlinarith
  rw [errorFactor_eq_linearizationConstant_mul_sq_stepConstant]
  calc
    LALM.linearizationConstant h * (stepConstant h * (base.delta : ℝ)) ^ 2 ≤
        LALM.linearizationConstant h * 1 :=
      mul_le_mul_of_nonneg_left htSq hlinearizationNonneg
    _ = LALM.linearizationConstant h := mul_one _

/-- Helper for Proposition 4.1: a normalized radius at most `1 / 8` transports the
base model budget to the corrected model expression. -/
private lemma correctedModelExpression_le
    {t objectiveTerm multiplierTerm mixedTerm penaltyTerm parameterTerm beta : ℝ}
    (htNonneg : 0 ≤ t) (ht : t ≤ 1 / 8)
    (hmultiplierNonneg : 0 ≤ multiplierTerm)
    (hmixedNonneg : 0 ≤ mixedTerm)
    (hpenaltyNonneg : 0 ≤ penaltyTerm)
    (hbetaNonneg : 0 ≤ beta)
    (hparameter : parameterTerm + beta * t + mixedTerm * t ≤ multiplierTerm)
    (hmodel : objectiveTerm + 3 * multiplierTerm + mixedTerm + penaltyTerm ≤
      3 * beta / 8) :
    parameterTerm + objectiveTerm * (1 + t) ^ 2 +
        3 * multiplierTerm * t ^ 2 + mixedTerm * t ^ 2 +
          penaltyTerm * t ^ 4 ≤ 3 * beta / 8 := by
  have htSq : t ^ 2 ≤ t := by nlinarith
  have htFourth : t ^ 4 ≤ 1 := by nlinarith [sq_nonneg (t ^ 2)]
  have hobjectiveUpper : objectiveTerm ≤ 3 * beta / 8 := by nlinarith
  have hinflationPolynomial : 2 * t + t ^ 2 ≤ 17 * t / 8 := by nlinarith
  have hobjectiveInflation :
      objectiveTerm * (2 * t + t ^ 2) ≤ beta * t := by
    have hinflationNonneg : 0 ≤ 2 * t + t ^ 2 := by nlinarith
    calc
      objectiveTerm * (2 * t + t ^ 2) ≤
          (3 * beta / 8) * (2 * t + t ^ 2) := by
        exact mul_le_mul_of_nonneg_right hobjectiveUpper hinflationNonneg
      _ ≤ (3 * beta / 8) * (17 * t / 8) := by
        gcongr
      _ ≤ beta * t := by nlinarith
  have hobjectiveCorrected :
      objectiveTerm * (1 + t) ^ 2 ≤ objectiveTerm + beta * t := by
    nlinarith
  have hmultiplierCorrected :
      3 * multiplierTerm * t ^ 2 ≤ 2 * multiplierTerm := by
    have : t ^ 2 ≤ 2 / 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hmultiplierNonneg]
  have hmixedCorrected : mixedTerm * t ^ 2 ≤ mixedTerm * t + mixedTerm := by
    nlinarith [mul_le_mul_of_nonneg_left htSq hmixedNonneg]
  have hpenaltyCorrected : penaltyTerm * t ^ 4 ≤ penaltyTerm := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left htFourth hpenaltyNonneg
  nlinarith

/-- The base parameter inequalities imply the corrected multiplier-bound inequality. -/
theorem parameterBound_le_of_base {h : EqualityConstrained.Regularity f c}
    (base : LALM.AdmissibleParameters h) :
    (h.gradientBound + base.beta * base.delta +
      base.rho * h.constraintGradientBound * errorFactor h base.delta *
        base.delta ^ 2) / h.licqModulus ≤ base.multiplierBound := by
  -- Replace the corrected error factor by the larger base linearization constant.
  have hfactor := errorFactor_le_linearizationConstant base
  have hcoefficientNonneg :
      0 ≤ (base.rho : ℝ) * h.constraintGradientBound * base.delta ^ 2 := by
    positivity
  apply (div_le_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)).mpr
  calc
    (h.gradientBound : ℝ) + base.beta * base.delta +
        base.rho * h.constraintGradientBound * errorFactor h base.delta *
          base.delta ^ 2 ≤
        h.gradientBound + base.beta * base.delta +
          base.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            base.delta ^ 2 := by
      gcongr
    _ ≤ (base.multiplierBound : ℝ) * h.licqModulus :=
      (div_le_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)).mp
        base.parameterBound_le

/-- The base model inequality implies its corrected counterpart. -/
theorem modelConstant_le_of_base {h : EqualityConstrained.Regularity f c}
    (base : LALM.AdmissibleParameters h) :
    modelConstant h base.delta base.rho base.multiplierBound ≤
      3 * base.beta / 8 := by
  -- Normalize both model constants by the dimensionless correction radius.
  let t : ℝ := stepConstant h * base.delta
  let objectiveTerm : ℝ := h.gradientLipschitz / 2
  let multiplierTerm : ℝ := LALM.linearizationConstant h * base.multiplierBound
  let mixedTerm : ℝ :=
    base.rho * h.constraintGradientBound * LALM.linearizationConstant h * base.delta
  let penaltyTerm : ℝ :=
    base.rho / 2 * LALM.linearizationConstant h ^ 2 * base.delta ^ 2
  let parameterTerm : ℝ := h.gradientBound * stepConstant h
  have ht := stepConstant_mul_delta_le_eighth base
  have htNonneg : 0 ≤ t := by
    dsimp only [t]
    rw [stepConstant_def]
    positivity
  have hparameterNumerator :=
    (div_le_iff₀ (NNReal.coe_pos.2 h.licqModulus_pos)).mp base.parameterBound_le
  have hstepLinearization :
      stepConstant h * (h.licqModulus : ℝ) = LALM.linearizationConstant h := by
    rw [stepConstant_def, LALM.linearizationConstant_def]
    norm_num [NNReal.coe_div]
    field_simp [ne_of_gt (NNReal.coe_pos.2 h.licqModulus_pos)]
  have hparameterScaled :
      parameterTerm + (base.beta : ℝ) * t + mixedTerm * t ≤ multiplierTerm := by
    have hstepConstantNonneg : 0 ≤ stepConstant h := by
      rw [stepConstant_def]
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hparameterNumerator hstepConstantNonneg
    dsimp only [parameterTerm, t, mixedTerm, multiplierTerm]
    calc
      (h.gradientBound : ℝ) * stepConstant h +
          base.beta * (stepConstant h * base.delta) +
          (base.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            base.delta) * (stepConstant h * base.delta) =
          stepConstant h *
            (h.gradientBound + base.beta * base.delta +
              base.rho * h.constraintGradientBound * LALM.linearizationConstant h *
                base.delta ^ 2) := by ring
      _ ≤ stepConstant h *
          (base.multiplierBound * (h.licqModulus : ℝ)) := hscaled
      _ = LALM.linearizationConstant h * base.multiplierBound := by
        calc
          stepConstant h * (base.multiplierBound * (h.licqModulus : ℝ)) =
              (stepConstant h * (h.licqModulus : ℝ)) * base.multiplierBound := by
            ring
          _ = LALM.linearizationConstant h * base.multiplierBound := by
            rw [hstepLinearization]
  have hbaseModel :
      objectiveTerm + 3 * multiplierTerm + mixedTerm + penaltyTerm ≤
        3 * (base.beta : ℝ) / 8 := by
    dsimp only [objectiveTerm, multiplierTerm, mixedTerm, penaltyTerm]
    calc
      (h.gradientLipschitz : ℝ) / 2 +
          3 * (LALM.linearizationConstant h * base.multiplierBound) +
          base.rho * h.constraintGradientBound * LALM.linearizationConstant h *
            base.delta +
          base.rho / 2 * LALM.linearizationConstant h ^ 2 * base.delta ^ 2 =
          LALM.modelConstant h base.delta base.rho base.multiplierBound := by
        rw [LALM.modelConstant_def]
        ring
      _ ≤ 3 * (base.beta : ℝ) / 8 := base.modelConstant_le
  have hmultiplierNonneg : 0 ≤ multiplierTerm := by
    dsimp only [multiplierTerm]
    positivity
  have hmixedNonneg : 0 ≤ mixedTerm := by
    dsimp only [mixedTerm]
    positivity
  have hpenaltyNonneg : 0 ≤ penaltyTerm := by
    dsimp only [penaltyTerm]
    positivity
  have hbetaNonneg : (0 : ℝ) ≤ base.beta := by positivity
  have hnormalized := correctedModelExpression_le htNonneg ht hmultiplierNonneg
    hmixedNonneg hpenaltyNonneg hbetaNonneg hparameterScaled hbaseModel
  have hfactor := errorFactor_eq_linearizationConstant_mul_sq_stepConstant
    h (base.delta : ℝ)
  rw [modelConstant_def, displacementFactor_def, hfactor]
  dsimp only [t, objectiveTerm, multiplierTerm, mixedTerm, penaltyTerm,
    parameterTerm] at hnormalized ⊢
  nlinarith

/-- Helper for Proposition 4.1: on a nonempty regularity region, the corrected primal
and comparison constants do not exceed their base counterparts. -/
private lemma primalConstants_le_of_base
    {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    primalConstant h base.delta base.beta base.rho ≤
        LALM.primalConstant h base.delta base.beta base.rho ∧
      primalComparisonConstant h base.delta base.beta base.rho base.multiplierBound ≤
        LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound := by
  -- The fourth base inequality supplies enough penalty to absorb displacement inflation.
  let t : ℝ := stepConstant h * base.delta
  let linearization : ℝ := LALM.linearizationConstant h
  let objectiveConstraintTerm : ℝ :=
    h.gradientLipschitz + h.constraintGradientLipschitz * base.multiplierBound
  let mixedTerm : ℝ :=
    base.rho * h.constraintGradientBound * linearization * base.delta
  have ht := stepConstant_mul_delta_le_eighth base
  have htNonneg : 0 ≤ t := by
    dsimp only [t]
    rw [stepConstant_def]
    positivity
  have htSq : t ^ 2 ≤ 1 / 64 := by nlinarith
  have hsigmaPos : (0 : ℝ) < h.licqModulus :=
    NNReal.coe_pos.2 h.licqModulus_pos
  have hbetaPos : (0 : ℝ) < base.beta :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 base.beta.ne_zero)
  have hrhoNonneg : (0 : ℝ) ≤ base.rho := by positivity
  have hboundModulus := licqModulus_le_constraintGradientBound (h := h) hm
  have hstepLinearization :
      stepConstant h * (h.licqModulus : ℝ) = linearization := by
    dsimp only [linearization]
    rw [stepConstant_def, LALM.linearizationConstant_def]
    norm_num [NNReal.coe_div]
    field_simp [ne_of_gt hsigmaPos]
  have htModulus : t * (h.licqModulus : ℝ) =
      linearization * base.delta := by
    calc
      t * (h.licqModulus : ℝ) =
          (stepConstant h * (h.licqModulus : ℝ)) * base.delta := by
        dsimp only [t]
        ring
      _ = linearization * base.delta := by rw [hstepLinearization]
  have hbaseMultiplier := base.multiplierPrimalConstant_le
  have hbaseMultiplierScaled := (div_le_iff₀ hbetaPos).mp hbaseMultiplier
  have hcomparisonSq_le_max :
      LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 ≤
        max (LALM.primalConstant h base.delta base.beta base.rho ^ 2)
          (LALM.primalComparisonConstant h base.delta base.beta base.rho
            base.multiplierBound ^ 2) := le_max_right _ _
  have hcomparisonScaled :
      32 * LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 / (h.licqModulus : ℝ) ^ 2 ≤
        (base.rho : ℝ) * base.beta := by
    calc
      32 * LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 / (h.licqModulus : ℝ) ^ 2 =
          8 * ((4 / (h.licqModulus : ℝ) ^ 2) *
            LALM.primalComparisonConstant h base.delta base.beta base.rho
              base.multiplierBound ^ 2) := by ring
      _ ≤ 8 * ((4 / (h.licqModulus : ℝ) ^ 2) *
          max (LALM.primalConstant h base.delta base.beta base.rho ^ 2)
            (LALM.primalComparisonConstant h base.delta base.beta base.rho
              base.multiplierBound ^ 2)) := by
        gcongr
      _ = 8 * LALM.multiplierPrimalConstant h base.delta base.beta base.rho
          base.multiplierBound := by rw [LALM.multiplierPrimalConstant_def]
      _ ≤ (base.rho : ℝ) * base.beta := hbaseMultiplierScaled
  have hcomparisonScaled' :
      32 * LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 ≤
        ((base.rho : ℝ) * base.beta) * (h.licqModulus : ℝ) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hsigmaPos)).mp hcomparisonScaled
  have hobjectiveConstraintNonneg : 0 ≤ objectiveConstraintTerm := by
    dsimp only [objectiveConstraintTerm]
    positivity
  have hcomparisonFormula :
      LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound = base.beta + mixedTerm + objectiveConstraintTerm := by
    rw [LALM.primalComparisonConstant_def, LALM.primalConstant_def]
    dsimp only [mixedTerm, linearization, objectiveConstraintTerm]
    ring
  have hbetaObjective_le_comparisonSq :
      (base.beta : ℝ) * objectiveConstraintTerm ≤
        LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 := by
    have hmixedNonneg : 0 ≤ mixedTerm := by
      dsimp only [mixedTerm, linearization]
      positivity
    rw [hcomparisonFormula]
    nlinarith [sq_nonneg ((base.beta : ℝ) - objectiveConstraintTerm)]
  have hobjectivePenalty :
      32 * objectiveConstraintTerm ≤
        (base.rho : ℝ) * (h.licqModulus : ℝ) ^ 2 := by
    have hwithBeta :
        (base.beta : ℝ) * (32 * objectiveConstraintTerm) ≤
          base.beta * ((base.rho : ℝ) * (h.licqModulus : ℝ) ^ 2) := by
      calc
        (base.beta : ℝ) * (32 * objectiveConstraintTerm) ≤
            32 * LALM.primalComparisonConstant h base.delta base.beta base.rho
              base.multiplierBound ^ 2 := by nlinarith
        _ ≤ ((base.rho : ℝ) * base.beta) *
            (h.licqModulus : ℝ) ^ 2 := hcomparisonScaled'
        _ = base.beta * ((base.rho : ℝ) * (h.licqModulus : ℝ) ^ 2) := by ring
    exact le_of_mul_le_mul_left hwithBeta hbetaPos
  have hpenaltyScale :
      (base.rho : ℝ) * (h.licqModulus : ℝ) ^ 2 ≤
        base.rho * h.constraintGradientBound * h.licqModulus := by
    have hscaledBound := mul_le_mul_of_nonneg_left hboundModulus hrhoNonneg
    nlinarith
  have hobjectiveAbsorbed :
      objectiveConstraintTerm ≤
        (base.rho : ℝ) * h.constraintGradientBound * h.licqModulus *
          (1 - t ^ 2) := by
    have hobjectiveSmall :
        objectiveConstraintTerm ≤
          ((base.rho : ℝ) * h.constraintGradientBound * h.licqModulus) / 32 := by
      have hthirtyTwoPos : (0 : ℝ) < 32 := by norm_num
      have hobjectivePenalty' :
          objectiveConstraintTerm * 32 ≤
            (base.rho : ℝ) * (h.licqModulus : ℝ) ^ 2 := by
        simpa only [mul_comm] using hobjectivePenalty
      apply (le_div_iff₀ hthirtyTwoPos).mpr
      exact le_trans hobjectivePenalty' hpenaltyScale
    have hscaleNonneg :
        0 ≤ (base.rho : ℝ) * h.constraintGradientBound * h.licqModulus := by
      positivity
    have hscaledSq := mul_le_mul_of_nonneg_left htSq hscaleNonneg
    nlinarith
  have hproductAbsorbed :
      objectiveConstraintTerm * t ≤ mixedTerm * (1 - t ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_right hobjectiveAbsorbed htNonneg
    have hmixedIdentity :
        (base.rho : ℝ) * h.constraintGradientBound * h.licqModulus * t =
          mixedTerm := by
      dsimp only [mixedTerm]
      rw [mul_assoc, mul_assoc, mul_comm (h.licqModulus : ℝ) t,
        htModulus]
      ring
    rw [← hmixedIdentity]
    nlinarith
  have hfactorIdentity := errorFactor_eq_linearizationConstant_mul_sq_stepConstant
    h (base.delta : ℝ)
  constructor
  · -- The corrected primal constant replaces the base linearization factor by a smaller one.
    rw [primalConstant_def, LALM.primalConstant_def]
    gcongr
    exact errorFactor_le_linearizationConstant base
  · -- The loss in the mixed term absorbs the corrected displacement factor.
    rw [primalComparisonConstant_def, primalConstant_def,
      LALM.primalComparisonConstant_def, LALM.primalConstant_def,
      displacementFactor_def, hfactorIdentity]
    dsimp only [t, mixedTerm, linearization, objectiveConstraintTerm] at hproductAbsorbed ⊢
    nlinarith

/-- The base multiplier-primal inequality implies its corrected counterpart on a
nonempty regularity region. -/
theorem multiplierPrimalConstant_le_of_base
    {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    8 * multiplierPrimalConstant h base.delta base.beta base.rho
      base.multiplierBound / base.beta ≤ base.rho := by
  -- Monotonicity of squares and `max` transfers the base fourth inequality.
  obtain ⟨hprimal, hcomparison⟩ := primalConstants_le_of_base hm base
  have hprimalNonneg :
      0 ≤ primalConstant h base.delta base.beta base.rho := by
    rw [primalConstant_def, errorFactor_def, errorConstant_def]
    positivity
  have hbasePrimalNonneg :
      0 ≤ LALM.primalConstant h base.delta base.beta base.rho := by
    rw [LALM.primalConstant_def]
    positivity
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h base.delta base.beta base.rho
        base.multiplierBound := by
    rw [primalComparisonConstant_def, primalConstant_def, errorFactor_def,
      errorConstant_def, displacementFactor_def, stepConstant_def]
    positivity
  have hbaseComparisonNonneg :
      0 ≤ LALM.primalComparisonConstant h base.delta base.beta base.rho
        base.multiplierBound := by
    rw [LALM.primalComparisonConstant_def]
    positivity
  have hprimalSq :
      primalConstant h base.delta base.beta base.rho ^ 2 ≤
        LALM.primalConstant h base.delta base.beta base.rho ^ 2 := by nlinarith
  have hcomparisonSq :
      primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 ≤
        LALM.primalComparisonConstant h base.delta base.beta base.rho
          base.multiplierBound ^ 2 := by nlinarith
  have hmax := max_le_max hprimalSq hcomparisonSq
  calc
    8 * multiplierPrimalConstant h base.delta base.beta base.rho
        base.multiplierBound / base.beta ≤
        8 * LALM.multiplierPrimalConstant h base.delta base.beta base.rho
          base.multiplierBound / base.beta := by
      rw [multiplierPrimalConstant_def, LALM.multiplierPrimalConstant_def]
      gcongr
    _ ≤ base.rho := base.multiplierPrimalConstant_le

/-- Convert the four base admissibility inequalities to their corrected counterparts,
preserving the numerical parameter tuple. -/
@[expose] def ofBase {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    AdmissibleParameters h :=
  { delta := base.delta
    beta := base.beta
    rho := base.rho
    multiplierBound := base.multiplierBound
    parameterBound_le := parameterBound_le_of_base base
    comparisonBound_le := base.comparisonBound_le
    modelConstant_le := modelConstant_le_of_base base
    multiplierPrimalConstant_le :=
      multiplierPrimalConstant_le_of_base hm base }

/-- The containment conversion preserves the complete numerical parameter tuple. -/
theorem ofBase_values {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    (ofBase hm base).values =
      base.values := rfl

/-- The containment conversion preserves the step-radius parameter. -/
theorem ofBase_delta {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    (ofBase hm base).delta = base.delta := rfl

/-- The containment conversion preserves the proximal parameter. -/
theorem ofBase_beta {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    (ofBase hm base).beta = base.beta := rfl

/-- The containment conversion preserves the penalty parameter. -/
theorem ofBase_rho {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    (ofBase hm base).rho = base.rho := rfl

/-- The containment conversion preserves the multiplier bound. -/
theorem ofBase_multiplierBound {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) (base : LALM.AdmissibleParameters h) :
    (ofBase hm base).multiplierBound =
      base.multiplierBound := rfl

end AdmissibleParameters

/-- Corrected admissible parameters together with the two bounds imposed by the
initialization data. -/
structure Parameters (h : EqualityConstrained.Regularity f c)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) extends AdmissibleParameters h where
  /-- The initial multiplier obeys the chosen multiplier bound. -/
  norm_multiplier₀_le : ‖multiplier₀‖ ≤ multiplierBound
  /-- The scaled initial constraint residual obeys the chosen multiplier bound. -/
  initialResidual_le : rho * ‖c x₀‖ ≤ multiplierBound

namespace Parameters

/-- Add the two initialization inequalities to a corrected admissible parameter
certificate. -/
def ofAdmissible (h : EqualityConstrained.Regularity f c)
    (x₀ : EuclideanSpace ℝ (Fin n)) (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : AdmissibleParameters h)
    (norm_multiplier₀_le : ‖multiplier₀‖ ≤ params.multiplierBound)
    (initialResidual_le : params.rho * ‖c x₀‖ ≤ params.multiplierBound) :
    Parameters h x₀ multiplier₀ :=
  { toAdmissibleParameters := params
    norm_multiplier₀_le
    initialResidual_le }

/-- Convert initialized NR-LALM parameters to initialized NR-LALM+SOC
parameters while preserving the complete numerical tuple and initialization. -/
@[expose] def ofBase {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (base : LALM.Parameters h x₀ multiplier₀) :
    Parameters h x₀ multiplier₀ :=
  { toAdmissibleParameters :=
      AdmissibleParameters.ofBase hm base.toAdmissibleParameters
    norm_multiplier₀_le := base.norm_multiplier₀_le
    initialResidual_le := base.initialResidual_le }

/-- The initialized containment conversion preserves the step radius, proximal
parameter, penalty parameter, and multiplier bound. -/
theorem ofBase_values {h : EqualityConstrained.Regularity f c}
    (hm : 0 < m) {x₀ : EuclideanSpace ℝ (Fin n)}
    {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (base : LALM.Parameters h x₀ multiplier₀) :
    (ofBase hm base).toAdmissibleParameters.values =
      base.toAdmissibleParameters.values := by
  exact AdmissibleParameters.ofBase_values hm base.toAdmissibleParameters

/-- An initialized corrected parameter certificate exposes its admissibility and
initialization conditions. -/
theorem spec {h : EqualityConstrained.Regularity f c}
    {x₀ : EuclideanSpace ℝ (Fin n)} {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    ((0 : ℝ) < params.delta ∧ (0 : ℝ) < params.beta ∧
      (0 : ℝ) < params.rho ∧ (0 : ℝ) < params.multiplierBound) ∧
    (((h.gradientBound + params.beta * params.delta +
      params.rho * h.constraintGradientBound * errorFactor h params.delta *
        params.delta ^ 2) / h.licqModulus : ℝ) ≤ params.multiplierBound ∧
      (h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * h.licqModulus ^ 2) : ℝ) ≤ params.delta ∧
      modelConstant h params.delta params.rho params.multiplierBound ≤
        3 * params.beta / 8 ∧
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.beta ≤ params.rho) ∧
    (‖multiplier₀‖ ≤ params.multiplierBound ∧
      params.rho * ‖c x₀‖ ≤ params.multiplierBound) :=
  ⟨params.toAdmissibleParameters.spec.1,
    ⟨params.toAdmissibleParameters.spec.2,
      ⟨params.norm_multiplier₀_le, params.initialResidual_le⟩⟩⟩

end Parameters

end LALM.Correction

end

namespace LALM.Correction


end LALM.Correction
