/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_3.GaussianLikelihood

public section

noncomputable section

open GaussianLikelihood
open scoped BigOperators

universe u

section

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Helper for Exercise 4.3: summing the deviations from the sample mean gives zero. -/
lemma sum_sub_sampleMean_eq_zero (d : ι → ℝ) :
    ∑ i, (d i - sampleMean d) = 0 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty ι›))
  -- Rewrite the sum of centered observations using the defining formula for the sample mean.
  calc
    ∑ i, (d i - sampleMean d)
        = ∑ i, d i - ∑ i, sampleMean d := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i, d i - (Fintype.card ι : ℝ) * sampleMean d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ i, d i - (Fintype.card ι : ℝ) * ((∑ i, d i) / Fintype.card ι) := by
          rw [sampleMean_def]
    _ = 0 := by
          field_simp [hcard]
          ring

/-- Helper for Exercise 4.3: the quadratic loss decomposes around the sample mean. -/
lemma sum_sub_sq_eq_sum_sub_sampleMean_sq_add (d : ι → ℝ) (mean : ℝ) :
    ∑ i, (d i - mean) ^ 2
      = ∑ i, (d i - sampleMean d) ^ 2
          + (Fintype.card ι : ℝ) * (mean - sampleMean d) ^ 2 := by
  have hzero : ∑ i, (d i - sampleMean d) = 0 := sum_sub_sampleMean_eq_zero d
  have hexpand :
      ∀ i,
        (d i - mean) ^ 2
          = (d i - sampleMean d) ^ 2
              + 2 * (sampleMean d - mean) * (d i - sampleMean d)
              + (sampleMean d - mean) ^ 2 := by
    intro i
    ring
  -- Expand the square and let the centered linear term vanish by the previous lemma.
  calc
    ∑ i, (d i - mean) ^ 2
        = ∑ i,
            ((d i - sampleMean d) ^ 2
              + 2 * (sampleMean d - mean) * (d i - sampleMean d)
              + (sampleMean d - mean) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hexpand i]
    _ = ∑ i, (d i - sampleMean d) ^ 2
          + 2 * (sampleMean d - mean) * ∑ i, (d i - sampleMean d)
          + (Fintype.card ι : ℝ) * (sampleMean d - mean) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ i, (d i - sampleMean d) ^ 2
          + (Fintype.card ι : ℝ) * (sampleMean d - mean) ^ 2 := by
          rw [hzero, mul_zero, add_zero]
    _ = ∑ i, (d i - sampleMean d) ^ 2
          + (Fintype.card ι : ℝ) * (mean - sampleMean d) ^ 2 := by
          ring

omit [Nonempty ι] in
/-- Helper for Exercise 4.3: the sample likelihood is strictly positive for positive variance. -/
lemma gaussianLikelihood_pos (d : ι → ℝ) (mean variance : ℝ) (hvariance : 0 < variance) :
    0 < gaussianLikelihood d mean variance := by
  let v : NNReal := ⟨variance, le_of_lt hvariance⟩
  have hvnn : v ≠ 0 := by
    have hvpos : 0 < v := by
      exact_mod_cast hvariance
    exact ne_of_gt hvpos
  -- In the positive-variance branch every Gaussian pdf factor is positive.
  rw [gaussianLikelihood_def, dif_pos hvariance]
  refine Finset.prod_pos ?_
  intro i hi
  simpa [v] using ProbabilityTheory.gaussianPDFReal_pos mean v (d i) hvnn

/-- Helper for Exercise 4.3: the log of one Gaussian pdf factor has the standard quadratic form. -/
lemma log_gaussianPdf_eq (x mean variance : ℝ) (hvariance : 0 < variance) :
    let v : NNReal := ⟨variance, le_of_lt hvariance⟩
    Real.log (ProbabilityTheory.gaussianPDFReal mean v x)
      = -(Real.log (2 * Real.pi * variance)) / 2
          + (-(x - mean) ^ 2 / (2 * variance)) := by
  intro v
  -- Expose the Gaussian pdf definition, then separate the logarithm of the product.
  rw [ProbabilityTheory.gaussianPDFReal_def]
  rw [Real.log_mul, Real.log_inv, Real.log_exp]
  · rw [Real.log_sqrt]
    · have hcoev : (v : ℝ) = variance := by
        rfl
      rw [hcoev]
      ring
    · positivity
  · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity))
  · exact Real.exp_ne_zero _

omit [Nonempty ι] in
/-- Helper for Exercise 4.3: the positive-variance Gaussian sample log-likelihood has a quadratic
normal form. -/
lemma log_gaussianLikelihood_eq (d : ι → ℝ) (mean variance : ℝ) (hvariance : 0 < variance) :
    Real.log (gaussianLikelihood d mean variance)
      = -(Fintype.card ι : ℝ) * Real.log (2 * Real.pi * variance) / 2
          - (∑ i, (d i - mean) ^ 2) / (2 * variance) := by
  have hvnn : (⟨variance, le_of_lt hvariance⟩ : NNReal) ≠ 0 := by
    have hvpos : 0 < (⟨variance, le_of_lt hvariance⟩ : NNReal) := by
      exact_mod_cast hvariance
    exact ne_of_gt hvpos
  -- Convert the product likelihood into a sum of pointwise log-densities.
  rw [gaussianLikelihood_def, dif_pos hvariance, Real.log_prod]
  · calc
      ∑ i,
          Real.log (ProbabilityTheory.gaussianPDFReal mean ⟨variance, le_of_lt hvariance⟩ (d i))
          = ∑ i,
              (-(Real.log (2 * Real.pi * variance)) / 2
                + (-(d i - mean) ^ 2 / (2 * variance))) := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa using log_gaussianPdf_eq (d i) mean variance hvariance
      _ = ∑ i, (-(Real.log (2 * Real.pi * variance)) / 2)
            + ∑ i, (-(d i - mean) ^ 2 / (2 * variance)) := by
            rw [Finset.sum_add_distrib]
      _ = (Fintype.card ι : ℝ) * (-(Real.log (2 * Real.pi * variance)) / 2)
            + ∑ i, (-(d i - mean) ^ 2 / (2 * variance)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = -(Fintype.card ι : ℝ) * Real.log (2 * Real.pi * variance) / 2
            - (∑ i, (d i - mean) ^ 2) / (2 * variance) := by
            have hsumNeg :
                ∑ i, (-(d i - mean) ^ 2 / (2 * variance))
                  = -(∑ i, (d i - mean) ^ 2) / (2 * variance) := by
              rw [← Finset.sum_div, Finset.sum_neg_distrib]
            rw [hsumNeg]
            ring
  · intro i hi
    exact (ProbabilityTheory.gaussianPDFReal_pos _ _ _ hvnn).ne'

omit [Nonempty ι] in
/-- Helper for Exercise 4.3: the mean-parameter Gaussian log-likelihood is a constant minus a
quadratic error term. -/
lemma log_gaussianLikelihood_mean_eq (d : ι → ℝ) (mean variance : ℝ) (hvariance : 0 < variance) :
    ProbabilityTheory.logLikelihood (fun mean' ↦ gaussianLikelihood d mean' variance) mean
      = -(Fintype.card ι : ℝ) * Real.log (2 * Real.pi * variance) / 2
          - (∑ i, (d i - mean) ^ 2) / (2 * variance) := by
  -- The log-likelihood is just `Real.log` of the frozen-data likelihood.
  rw [ProbabilityTheory.logLikelihood_apply]
  exact log_gaussianLikelihood_eq d mean variance hvariance

/-- Helper for Exercise 4.3: the variance-parameter Gaussian log-likelihood separates into a
constant term and the scalar objective `v ↦ log v + a / v`. -/
lemma log_gaussianLikelihood_variance_eq
    (mean : ℝ) (d : ι → ℝ) (variance : ℝ) (hvariance : 0 < variance) :
    ProbabilityTheory.logLikelihood (fun variance' ↦ gaussianLikelihood d mean variance') variance
      = -(Fintype.card ι : ℝ) * Real.log (2 * Real.pi) / 2
          - ((Fintype.card ι : ℝ) / 2)
              * (Real.log variance + centeredSquareAverage mean d / variance) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty ι›))
  have htwopi : (2 * Real.pi : ℝ) ≠ 0 := by
    positivity
  have hlogmul :
      Real.log (2 * Real.pi * variance) = Real.log (2 * Real.pi) + Real.log variance := by
    rw [show 2 * Real.pi * variance = (2 * Real.pi) * variance by ring]
    rw [Real.log_mul htwopi hvariance.ne']
  -- Rewrite the generic log-likelihood form so that the optimized scalar becomes explicit.
  rw [ProbabilityTheory.logLikelihood_apply, log_gaussianLikelihood_eq d mean variance hvariance]
  rw [hlogmul, centeredSquareAverage_def]
  field_simp [hcard]
  ring

/-- Helper for Exercise 4.3: the scalar function `v ↦ log v + a / v` is minimized at `v = a`. -/
lemma log_add_div_le_at_self (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    Real.log a + 1 ≤ Real.log v + a / v := by
  have hratio : 0 < a / v := by
    positivity
  -- Apply the standard tangent-line upper bound for `log` to the ratio `a / v`.
  have hlog : Real.log (a / v) ≤ a / v - 1 := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div ha.ne' hv.ne'] at hlog
  linarith

/-- Exercise 4.3 (1): for a finite nonempty independent Gaussian sample with known variance, the
sample mean is a maximum-likelihood estimator for the common mean. This covers the source's
positive-variance case; when `variance ≤ 0`, `gaussianLikelihood d mean variance = 0` for every
`mean`, so the statement is trivial. -/
theorem isGaussianMeanMLE_sampleMean (d : ι → ℝ) (variance : ℝ) :
    ProbabilityTheory.IsMLE (fun mean ↦ gaussianLikelihood d mean variance) (sampleMean d) := by
  by_cases hvariance : 0 < variance
  · -- Route correction: after restricting to positive variance, maximize the log-likelihood.
    rw [ProbabilityTheory.isMLE_iff_isMaxOn_logLikelihood]
    · rw [isMaxOn_univ_iff]
      intro mean
      -- Compare the quadratic losses using the completed-square identity.
      rw [log_gaussianLikelihood_mean_eq d mean variance hvariance]
      rw [log_gaussianLikelihood_mean_eq d (sampleMean d) variance hvariance]
      have hquad :
          ∑ i, (d i - sampleMean d) ^ 2 ≤ ∑ i, (d i - mean) ^ 2 := by
        rw [sum_sub_sq_eq_sum_sub_sampleMean_sq_add d mean]
        nlinarith [sq_nonneg (mean - sampleMean d), show 0 ≤ (Fintype.card ι : ℝ) by positivity]
      have hdiv :
          (∑ i, (d i - sampleMean d) ^ 2) / (2 * variance)
            ≤ (∑ i, (d i - mean) ^ 2) / (2 * variance) := by
        exact div_le_div_of_nonneg_right hquad (by positivity)
      linarith
    · intro mean
      exact gaussianLikelihood_pos d mean variance hvariance
  · -- Outside the positive-variance regime the likelihood is identically zero.
    rw [ProbabilityTheory.isMLE_iff, isMaxOn_univ_iff]
    intro mean
    rw [gaussianLikelihood_def, gaussianLikelihood_def, dif_neg hvariance, dif_neg hvariance]

/-- Exercise 4.3 (2): for a finite nonempty independent Gaussian sample with known mean, the
average squared deviation from that mean is a maximum-likelihood estimator for the variance on
the positive-variance domain, provided this candidate variance is strictly positive. -/
theorem isGaussianVarianceMLE_centeredSquareAverage (mean : ℝ) (d : ι → ℝ)
    (hvariance : 0 < centeredSquareAverage mean d) :
    ProbabilityTheory.IsMLEOn (fun variance ↦ gaussianLikelihood d mean variance) (Set.Ioi (0 : ℝ))
      (centeredSquareAverage mean d) := by
  rw [ProbabilityTheory.isMLEOn_iff_isMaxOn_logLikelihood]
  · refine ⟨hvariance, ?_⟩
    intro variance hvariance_mem
    have hvariance' : 0 < variance := hvariance_mem
    -- Reduce the comparison to the scalar inequality for `log v + a / v`.
    change
      ProbabilityTheory.logLikelihood (fun variance' ↦ gaussianLikelihood d mean variance') variance
        ≤ ProbabilityTheory.logLikelihood
            (fun variance' ↦ gaussianLikelihood d mean variance')
            (centeredSquareAverage mean d)
    rw [log_gaussianLikelihood_variance_eq mean d variance hvariance']
    rw [log_gaussianLikelihood_variance_eq mean d (centeredSquareAverage mean d) hvariance]
    have hscalar :
        Real.log (centeredSquareAverage mean d) + 1
          ≤ Real.log variance + centeredSquareAverage mean d / variance := by
      exact log_add_div_le_at_self (centeredSquareAverage mean d) variance hvariance hvariance'
    have hself : centeredSquareAverage mean d / centeredSquareAverage mean d = 1 := by
      exact div_self hvariance.ne'
    rw [hself]
    nlinarith [hscalar, show 0 ≤ (Fintype.card ι : ℝ) by positivity]
  · intro variance hvariance_mem
    exact gaussianLikelihood_pos d mean variance hvariance_mem

end
