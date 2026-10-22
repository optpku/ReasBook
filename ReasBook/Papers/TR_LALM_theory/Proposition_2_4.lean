/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Asymptotics.Theta
public import TR_LALM_theory.Assumption_2_3.Parameters

public section

open Filter Asymptotics

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- Helper for Proposition 2.4: a nonnegative summand is small after scaling by
the reciprocal of eight times one plus a dominating nonnegative sum. -/
private lemma coefficient_mul_smallRadius_le (x total : ℝ)
    (htotal : 0 ≤ total) (hxtotal : x ≤ total) :
    x * (1 / (8 * (1 + total))) ≤ 1 / 8 := by
  -- Clear the positive common denominator and use that `x` is one of the controlled terms.
  have hdenominator : 0 < 8 * (1 + total) := by positivity
  have hquotient : x * (1 / (8 * (1 + total))) = x / (8 * (1 + total)) := by
    simp only [div_eq_mul_inv, one_mul]
  rw [hquotient, div_le_iff₀ hdenominator]
  norm_num
  linarith

/-- Helper for Proposition 2.4: bounds of `2 * beta` on both primal constants
imply the multiplier-primal admissibility inequality for a sufficiently large
penalty ratio. -/
private lemma multiplierPrimalConstant_le_of_primal_bounds
    (h : EqualityConstrained.Regularity f c) {delta beta tauRho multiplierBound : ℝ}
    (hbeta : 0 < beta)
    (htauRho : 128 / (h.licqModulus : ℝ) ^ 2 ≤ tauRho)
    (hprimalNonneg : 0 ≤ primalConstant h delta beta (tauRho * beta))
    (hprimal : primalConstant h delta beta (tauRho * beta) ≤ 2 * beta)
    (hcomparisonNonneg :
      0 ≤ primalComparisonConstant h delta beta (tauRho * beta) multiplierBound)
    (hcomparison :
      primalComparisonConstant h delta beta (tauRho * beta) multiplierBound ≤ 2 * beta) :
    8 * multiplierPrimalConstant h delta beta (tauRho * beta) multiplierBound / beta ≤
      tauRho * beta := by
  -- The two hypotheses put both squares below the same quadratic envelope.
  have hlicq : 0 < (h.licqModulus : ℝ) := h.licqModulus_pos
  have hlicqSq : 0 < (h.licqModulus : ℝ) ^ 2 := sq_pos_of_pos hlicq
  have hmax :
      max ((primalConstant h delta beta (tauRho * beta)) ^ 2)
          ((primalComparisonConstant h delta beta (tauRho * beta) multiplierBound) ^ 2) ≤
        4 * beta ^ 2 := by
    rw [max_le_iff]
    constructor
    · nlinarith
    · nlinarith
  -- Clear the two positive divisors; the remaining estimate is exactly the ratio hypothesis.
  rw [multiplierPrimalConstant_def, div_le_iff₀ hbeta]
  have hratio : 128 ≤ tauRho * (h.licqModulus : ℝ) ^ 2 := by
    rwa [div_le_iff₀ hlicqSq] at htauRho
  have hscaledRatio := mul_le_mul_of_nonneg_right hratio (sq_nonneg beta)
  have hreassociate :
      8 * ((4 / (h.licqModulus : ℝ) ^ 2) *
          max ((primalConstant h delta beta (tauRho * beta)) ^ 2)
            ((primalComparisonConstant h delta beta (tauRho * beta) multiplierBound) ^ 2)) =
        (32 * max ((primalConstant h delta beta (tauRho * beta)) ^ 2)
          ((primalComparisonConstant h delta beta (tauRho * beta) multiplierBound) ^ 2)) /
            (h.licqModulus : ℝ) ^ 2 := by
    ring
  rw [hreassociate, div_le_iff₀ hlicqSq]
  nlinarith

/-- Helper for Proposition 2.4: a gradient threshold and a small penalty correction
give the first admissibility inequality when the multiplier coefficient times the
LICQ modulus is four. -/
private lemma parameterBound_le_of_scaled_corrections
    (h : EqualityConstrained.Regularity f c) {delta beta tauRho kappa : ℝ}
    (hdelta : 0 ≤ delta) (hbeta : 0 ≤ beta)
    (hgradient : (h.gradientBound : ℝ) ≤ beta * delta / 2)
    (hpenalty :
      tauRho * h.constraintGradientBound * linearizationConstant h * delta ≤ 1 / 8)
    (hlicq : 0 < (h.licqModulus : ℝ))
    (hkappa : kappa * (h.licqModulus : ℝ) = 4) :
    ((h.gradientBound + beta * delta +
        (tauRho * beta) * h.constraintGradientBound * linearizationConstant h *
          delta ^ 2) / h.licqModulus : ℝ) ≤ kappa * (beta * delta) := by
  -- Scale the small correction by `beta * delta` before clearing the LICQ divisor.
  have hscaleNonneg : 0 ≤ beta * delta := mul_nonneg hbeta hdelta
  have hpenaltyScaled := mul_le_mul_of_nonneg_left hpenalty hscaleNonneg
  have hpenaltyRearranged :
      (tauRho * beta) * (h.constraintGradientBound : ℝ) * linearizationConstant h *
          delta ^ 2 ≤ beta * delta / 8 := by
    calc
      (tauRho * beta) * (h.constraintGradientBound : ℝ) * linearizationConstant h *
          delta ^ 2 =
        (beta * delta) *
          (tauRho * h.constraintGradientBound * linearizationConstant h * delta) := by ring
      _ ≤ (beta * delta) * (1 / 8) := hpenaltyScaled
      _ = beta * delta / 8 := by ring
  have hrhs :
      kappa * (beta * delta) * (h.licqModulus : ℝ) = 4 * (beta * delta) := by
    calc
      kappa * (beta * delta) * (h.licqModulus : ℝ) =
          (kappa * (h.licqModulus : ℝ)) * (beta * delta) := by ring
      _ = 4 * (beta * delta) := by rw [hkappa]
  rw [div_le_iff₀ hlicq, hrhs]
  nlinarith

/-- Helper for Proposition 2.4: the fixed penalty-ratio identity bounds the
comparison quotient by half of the chosen radius. -/
private lemma comparisonBound_le_of_ratio_identity
    (h : EqualityConstrained.Regularity f c) {delta beta tauRho kappa : ℝ}
    (hdelta : 0 ≤ delta) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hgradient : (h.gradientBound : ℝ) ≤ beta * delta / 2)
    (htau :
      tauRho * (h.licqModulus : ℝ) ^ 2 =
        128 + 6 * (h.constraintGradientBound : ℝ) * kappa) :
    (h.gradientBound / beta +
        3 * h.constraintGradientBound * (kappa * (beta * delta)) /
          (beta + (tauRho * beta) * h.licqModulus ^ 2) : ℝ) ≤ delta := by
  -- Split the target between the gradient quotient and the ratio-controlled term.
  have hgradientQuotient : (h.gradientBound : ℝ) / beta ≤ delta / 2 := by
    rw [div_le_iff₀ hbeta]
    nlinarith
  have hcomparisonCoefficient :
      6 * (h.constraintGradientBound : ℝ) * kappa ≤
        1 + tauRho * (h.licqModulus : ℝ) ^ 2 := by
    nlinarith
  have hscaleNonneg : 0 ≤ beta * delta := mul_nonneg hbeta.le hdelta
  have hcomparisonScaled :=
    mul_le_mul_of_nonneg_right hcomparisonCoefficient hscaleNonneg
  have hhalfNonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hcomparisonHalfScaled :=
    mul_le_mul_of_nonneg_right hcomparisonScaled hhalfNonneg
  have hdenominator :
      0 < beta + (tauRho * beta) * (h.licqModulus : ℝ) ^ 2 := by
    have hdenominatorIdentity :
        beta + (tauRho * beta) * (h.licqModulus : ℝ) ^ 2 =
          beta * (1 + tauRho * (h.licqModulus : ℝ) ^ 2) := by ring
    rw [hdenominatorIdentity, htau]
    positivity
  have hcomparisonQuotient :
      3 * (h.constraintGradientBound : ℝ) * (kappa * (beta * delta)) /
          (beta + (tauRho * beta) * (h.licqModulus : ℝ) ^ 2) ≤ delta / 2 := by
    rw [div_le_iff₀ hdenominator]
    calc
      3 * (h.constraintGradientBound : ℝ) * (kappa * (beta * delta)) =
          (6 * h.constraintGradientBound * kappa * (beta * delta)) * (1 / 2) := by ring
      _ ≤ ((1 + tauRho * (h.licqModulus : ℝ) ^ 2) * (beta * delta)) *
          (1 / 2) := hcomparisonHalfScaled
      _ = delta / 2 *
          (beta + (tauRho * beta) * (h.licqModulus : ℝ) ^ 2) := by ring
  nlinarith

/-- Helper for Proposition 2.4: normalized linear and quadratic corrections
bound the model constant by three eighths of `beta`. -/
private lemma modelConstant_le_of_scaled_corrections
    (h : EqualityConstrained.Regularity f c) {delta beta tauRho kappa : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaUpper : delta ≤ 1 / 8) (hbeta : 0 ≤ beta)
    (hgradientLipschitz : (h.gradientLipschitz : ℝ) ≤ beta / 4)
    (hlinear :
      linearizationConstant h * (3 * kappa + tauRho * h.constraintGradientBound) *
        delta ≤ 1 / 8)
    (hquadratic : tauRho * linearizationConstant h ^ 2 * delta ≤ 1 / 8) :
    modelConstant h delta (tauRho * beta) (kappa * (beta * delta)) ≤
      3 * beta / 8 := by
  -- Scale the normalized corrections, then expose the model formula once.
  have hlinearScaled := mul_le_mul_of_nonneg_left hlinear hbeta
  have hdeltaProductNonneg : 0 ≤ beta * delta := mul_nonneg hbeta hdelta
  have hquadraticScaled := mul_le_mul_of_nonneg_left hquadratic hdeltaProductNonneg
  rw [modelConstant_def]
  nlinarith

/-- Helper for Proposition 2.4: the normalized penalty and comparison corrections
put both primal constants between zero and `2 * beta`. -/
private lemma primalConstants_bounds_of_scaled_corrections
    (h : EqualityConstrained.Regularity f c) {delta beta tauRho kappa : ℝ}
    (hdelta : 0 ≤ delta) (hbeta : 0 ≤ beta)
    (htauRho : 0 ≤ tauRho) (hkappa : 0 ≤ kappa)
    (hpenalty :
      tauRho * h.constraintGradientBound * linearizationConstant h * delta ≤ 1 / 8)
    (hcomparison : (h.constraintGradientLipschitz : ℝ) * kappa * delta ≤ 1 / 8)
    (hgradientLipschitz : (h.gradientLipschitz : ℝ) ≤ beta / 4) :
    0 ≤ primalConstant h delta beta (tauRho * beta) ∧
      primalConstant h delta beta (tauRho * beta) ≤ 2 * beta ∧
      0 ≤ primalComparisonConstant h delta beta (tauRho * beta)
        (kappa * (beta * delta)) ∧
      primalComparisonConstant h delta beta (tauRho * beta)
        (kappa * (beta * delta)) ≤ 2 * beta := by
  -- Scale both correction bounds once and use the explicit primal formulas.
  have hpenaltyScaled := mul_le_mul_of_nonneg_left hpenalty hbeta
  have hcomparisonScaled := mul_le_mul_of_nonneg_left hcomparison hbeta
  have hpenaltyCorrection :
      (tauRho * beta) * (h.constraintGradientBound : ℝ) * linearizationConstant h * delta ≤
        beta / 8 := by
    calc
      (tauRho * beta) * (h.constraintGradientBound : ℝ) * linearizationConstant h * delta =
          beta *
            (tauRho * h.constraintGradientBound * linearizationConstant h * delta) := by ring
      _ ≤ beta * (1 / 8) := hpenaltyScaled
      _ = beta / 8 := by ring
  have hcomparisonCorrection :
      (h.constraintGradientLipschitz : ℝ) * (kappa * (beta * delta)) ≤ beta / 8 := by
    calc
      (h.constraintGradientLipschitz : ℝ) * (kappa * (beta * delta)) =
          beta * (h.constraintGradientLipschitz * kappa * delta) := by ring
      _ ≤ beta * (1 / 8) := hcomparisonScaled
      _ = beta / 8 := by ring
  have hprimalNonneg : 0 ≤ primalConstant h delta beta (tauRho * beta) := by
    rw [primalConstant_def]
    positivity
  have hprimalBound : primalConstant h delta beta (tauRho * beta) ≤ 2 * beta := by
    rw [primalConstant_def]
    nlinarith
  have hprimalSharp : primalConstant h delta beta (tauRho * beta) ≤ 9 * beta / 8 := by
    rw [primalConstant_def]
    nlinarith
  have hcomparisonNonneg :
      0 ≤ primalComparisonConstant h delta beta (tauRho * beta)
        (kappa * (beta * delta)) := by
    rw [primalComparisonConstant_def]
    positivity
  have hcomparisonBound :
      primalComparisonConstant h delta beta (tauRho * beta)
          (kappa * (beta * delta)) ≤ 2 * beta := by
    rw [primalComparisonConstant_def]
    nlinarith
  exact ⟨hprimalNonneg, hprimalBound, hcomparisonNonneg, hcomparisonBound⟩

/-- Helper for Proposition 2.4: positive real scalars can be represented by units
of `NNReal` without changing their real value. -/
private lemma existsNNRealUnit_coe_eq_of_pos (x : ℝ) (hx : 0 < x) :
    ∃ u : NNRealˣ, (u : ℝ) = x := by
  -- Package `x` as a nonzero nonnegative real, then use the canonical unit constructor.
  let y : NNReal := ⟨x, hx.le⟩
  have hy : y ≠ 0 := by
    exact ne_of_gt (NNReal.coe_pos.mp hx)
  refine ⟨Units.mk0 y hy, ?_⟩
  rfl

/-- Helper for Proposition 2.4: the regularity constants admit fixed positive
scales for which all four real admissibility inequalities hold above one
positive threshold. -/
private lemma existsPositiveScalarAdmissibilityScales
    (h : EqualityConstrained.Regularity f c) :
    ∃ delta tauRho kappa beta₀ : ℝ,
      0 < delta ∧ 0 < tauRho ∧ 0 < kappa ∧ 0 < beta₀ ∧
        ∀ beta ≥ beta₀,
          ((h.gradientBound + beta * delta +
              (tauRho * beta) * h.constraintGradientBound * linearizationConstant h *
                delta ^ 2) / h.licqModulus : ℝ) ≤ kappa * (beta * delta) ∧
          (h.gradientBound / beta +
              3 * h.constraintGradientBound * (kappa * (beta * delta)) /
                (beta + (tauRho * beta) * h.licqModulus ^ 2) : ℝ) ≤ delta ∧
          modelConstant h delta (tauRho * beta) (kappa * (beta * delta)) ≤
            3 * beta / 8 ∧
          8 * multiplierPrimalConstant h delta beta (tauRho * beta)
              (kappa * (beta * delta)) / beta ≤ tauRho * beta := by
  -- Fix the multiplier coefficient first and choose the penalty ratio to dominate LICQ losses.
  let kappa : ℝ := 4 / (h.licqModulus : ℝ)
  let tauRho : ℝ :=
    (128 + 6 * (h.constraintGradientBound : ℝ) * kappa) /
      (h.licqModulus : ℝ) ^ 2
  let total : ℝ :=
    tauRho * h.constraintGradientBound * linearizationConstant h +
      h.constraintGradientLipschitz * kappa +
      linearizationConstant h * (3 * kappa + tauRho * h.constraintGradientBound) +
      tauRho * linearizationConstant h ^ 2
  let delta : ℝ := 1 / (8 * (1 + total))
  let beta₀ : ℝ :=
    1 + 2 * (h.gradientBound : ℝ) / delta +
      4 * (h.gradientLipschitz : ℝ)
  have hlicq : 0 < (h.licqModulus : ℝ) := h.licqModulus_pos
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    positivity
  have htauRho : 0 < tauRho := by
    dsimp [tauRho]
    positivity
  have htotal : 0 ≤ total := by
    dsimp [total]
    positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbeta₀ : 0 < beta₀ := by
    dsimp [beta₀]
    positivity
  refine ⟨delta, tauRho, kappa, beta₀, hdelta, htauRho, hkappa, hbeta₀, ?_⟩
  intro beta hbetaThreshold
  have hbeta : 0 < beta := lt_of_lt_of_le hbeta₀ hbetaThreshold
  -- The reciprocal radius makes every coefficient correction uniformly small.
  have hpenaltyTermNonneg :
      0 ≤ tauRho * h.constraintGradientBound * linearizationConstant h := by positivity
  have hcomparisonTermNonneg :
      0 ≤ (h.constraintGradientLipschitz : ℝ) * kappa := by positivity
  have hmodelTermNonneg :
      0 ≤ linearizationConstant h *
        (3 * kappa + tauRho * h.constraintGradientBound) := by positivity
  have hquadraticTermNonneg :
      0 ≤ tauRho * linearizationConstant h ^ 2 := by positivity
  have hpenaltyTerm_le_total :
      tauRho * h.constraintGradientBound * linearizationConstant h ≤ total := by
    dsimp [total]
    nlinarith
  have hcomparisonTerm_le_total :
      (h.constraintGradientLipschitz : ℝ) * kappa ≤ total := by
    dsimp [total]
    nlinarith
  have hmodelTerm_le_total :
      linearizationConstant h * (3 * kappa + tauRho * h.constraintGradientBound) ≤
        total := by
    dsimp [total]
    nlinarith
  have hquadraticTerm_le_total :
      tauRho * linearizationConstant h ^ 2 ≤ total := by
    dsimp [total]
    nlinarith
  have hpenaltySmall :
      tauRho * h.constraintGradientBound * linearizationConstant h * delta ≤ 1 / 8 := by
    exact coefficient_mul_smallRadius_le _ _ htotal hpenaltyTerm_le_total
  have hcomparisonSmall :
      (h.constraintGradientLipschitz : ℝ) * kappa * delta ≤ 1 / 8 := by
    exact coefficient_mul_smallRadius_le _ _ htotal hcomparisonTerm_le_total
  have hmodelSmall :
      linearizationConstant h * (3 * kappa + tauRho * h.constraintGradientBound) * delta ≤
        1 / 8 := by
    exact coefficient_mul_smallRadius_le _ _ htotal hmodelTerm_le_total
  have hquadraticSmall :
      tauRho * linearizationConstant h ^ 2 * delta ≤ 1 / 8 := by
    exact coefficient_mul_smallRadius_le _ _ htotal hquadraticTerm_le_total
  have hdeltaUpper : delta ≤ 1 / 8 := by
    have hone_le : (1 : ℝ) ≤ 1 + total := by linarith
    dsimp [delta]
    have hdenominator : 0 < 8 * (1 + total) := by positivity
    rw [div_le_iff₀ hdenominator]
    norm_num
    nlinarith
  -- The threshold absorbs the objective gradient and Lipschitz constants.
  have hgradientBound : (h.gradientBound : ℝ) ≤ beta * delta / 2 := by
    have hthresholdRatioNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) / delta := by positivity
    have hgradientLipschitzNonneg : 0 ≤ (h.gradientLipschitz : ℝ) := by positivity
    have hthresholdPart : 2 * (h.gradientBound : ℝ) / delta ≤ beta := by
      dsimp [beta₀] at hbetaThreshold
      nlinarith
    rw [div_le_iff₀ hdelta] at hthresholdPart
    nlinarith
  have hgradientLipschitz : (h.gradientLipschitz : ℝ) ≤ beta / 4 := by
    have hthresholdRatioNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) / delta := by positivity
    dsimp [beta₀] at hbetaThreshold
    nlinarith
  -- Record the two exact ratio identities used when clearing denominators.
  have hkappaIdentity : kappa * (h.licqModulus : ℝ) = 4 := by
    dsimp [kappa]
    field_simp
  have htauIdentity :
      tauRho * (h.licqModulus : ℝ) ^ 2 =
        128 + 6 * (h.constraintGradientBound : ℝ) * kappa := by
    dsimp [tauRho]
    field_simp
  have htauLower : 128 / (h.licqModulus : ℝ) ^ 2 ≤ tauRho := by
    have hcoefficientNonneg : 0 ≤ (h.constraintGradientBound : ℝ) * kappa := by
      positivity
    rw [div_le_iff₀ (sq_pos_of_pos hlicq)]
    nlinarith
  -- The first two admissibility inequalities follow after clearing their positive denominators.
  have hparameterBound := parameterBound_le_of_scaled_corrections h hdelta.le hbeta.le
    hgradientBound hpenaltySmall hlicq hkappaIdentity
  have hcomparisonBound := comparisonBound_le_of_ratio_identity h hdelta.le hbeta hkappa.le
    hgradientBound htauIdentity
  -- Bound the model and both primal constants by fixed multiples of `beta`.
  have hmodelBound := modelConstant_le_of_scaled_corrections h hdelta.le hdeltaUpper
    hbeta.le hgradientLipschitz hmodelSmall hquadraticSmall
  obtain ⟨hprimalNonneg, hprimalBound, hcomparisonNonneg, hcomparisonPrimalBound⟩ :=
    primalConstants_bounds_of_scaled_corrections h hdelta.le hbeta.le htauRho.le hkappa.le
      hpenaltySmall hcomparisonSmall hgradientLipschitz
  have hmultiplierPrimalBound := multiplierPrimalConstant_le_of_primal_bounds h hbeta
    htauLower hprimalNonneg hprimalBound hcomparisonNonneg hcomparisonPrimalBound
  exact ⟨hparameterBound, hcomparisonBound, hmodelBound, hmultiplierPrimalBound⟩

/-- Proposition 2.4: fixed regularity data admit accuracy-independent scalar NR-LALM
parameters with a fixed penalty ratio and multiplier bound of order `beta * delta`. -/
theorem existsParametersOfLargeBeta (h : EqualityConstrained.Regularity f c) :
    ∃ delta tauRho beta₀ : ℝ,
      0 < delta ∧ 0 < tauRho ∧ 0 < beta₀ ∧
        ∃ multiplierBound : ℝ → ℝ,
          multiplierBound =Θ[atTop] (fun beta ↦ beta * delta) ∧
            ∀ beta ≥ beta₀, ∃ params : AdmissibleParameters h,
              params.values = (delta, beta, tauRho * beta, multiplierBound beta) := by
  -- First obtain the real scalar witnesses and their four uniform inequalities.
  obtain ⟨delta, tauRho, kappa, beta₀, hdelta, htauRho, hkappa, hbeta₀, hbounds⟩ :=
    existsPositiveScalarAdmissibilityScales h
  refine ⟨delta, tauRho, beta₀, hdelta, htauRho, hbeta₀,
    fun beta ↦ kappa * (beta * delta), ?_, ?_⟩
  · -- Multiplication by the fixed nonzero coefficient preserves Theta equivalence.
    exact (isTheta_refl (fun beta : ℝ ↦ beta * delta) atTop).const_mul_left hkappa.ne'
  · intro beta hbetaThreshold
    obtain ⟨hparameter, hcomparison, hmodel, hmultiplier⟩ := hbounds beta hbetaThreshold
    have hbeta : 0 < beta := lt_of_lt_of_le hbeta₀ hbetaThreshold
    have hrho : 0 < tauRho * beta := mul_pos htauRho hbeta
    have hmultiplierBound : 0 < kappa * (beta * delta) := by positivity
    -- Convert the four positive real values to unit-valued parameters once.
    obtain ⟨deltaUnit, hdeltaUnit⟩ := existsNNRealUnit_coe_eq_of_pos delta hdelta
    obtain ⟨betaUnit, hbetaUnit⟩ := existsNNRealUnit_coe_eq_of_pos beta hbeta
    obtain ⟨rhoUnit, hrhoUnit⟩ := existsNNRealUnit_coe_eq_of_pos (tauRho * beta) hrho
    obtain ⟨multiplierUnit, hmultiplierUnit⟩ :=
      existsNNRealUnit_coe_eq_of_pos (kappa * (beta * delta)) hmultiplierBound
    -- Rewrite the real inequalities to the unit representatives before constructing the record.
    have hparameterUnit :
        ((h.gradientBound + betaUnit * deltaUnit +
            rhoUnit * h.constraintGradientBound * linearizationConstant h * deltaUnit ^ 2) /
            h.licqModulus : ℝ) ≤ multiplierUnit := by
      simpa only [hdeltaUnit, hbetaUnit, hrhoUnit, hmultiplierUnit] using hparameter
    have hcomparisonUnit :
        (h.gradientBound / betaUnit +
            3 * h.constraintGradientBound * multiplierUnit /
              (betaUnit + rhoUnit * h.licqModulus ^ 2) : ℝ) ≤ deltaUnit := by
      simpa only [hdeltaUnit, hbetaUnit, hrhoUnit, hmultiplierUnit] using hcomparison
    have hmodelUnit :
        modelConstant h deltaUnit rhoUnit multiplierUnit ≤ 3 * betaUnit / 8 := by
      simpa only [hdeltaUnit, hbetaUnit, hrhoUnit, hmultiplierUnit] using hmodel
    have hmultiplierUnitBound :
        8 * multiplierPrimalConstant h deltaUnit betaUnit rhoUnit multiplierUnit / betaUnit ≤
          rhoUnit := by
      simpa only [hdeltaUnit, hbetaUnit, hrhoUnit, hmultiplierUnit] using hmultiplier
    let params : AdmissibleParameters h :=
      { delta := deltaUnit
        beta := betaUnit
        rho := rhoUnit
        multiplierBound := multiplierUnit
        parameterBound_le := hparameterUnit
        comparisonBound_le := hcomparisonUnit
        modelConstant_le := hmodelUnit
        multiplierPrimalConstant_le := hmultiplierUnitBound }
    refine ⟨params, ?_⟩
    -- The coordinate view now reduces to the four prescribed coercion equations.
    rw [AdmissibleParameters.values_def]
    dsimp [params]
    exact Prod.ext hdeltaUnit (Prod.ext hbetaUnit (Prod.ext hrhoUnit hmultiplierUnit))

end LALM

end
