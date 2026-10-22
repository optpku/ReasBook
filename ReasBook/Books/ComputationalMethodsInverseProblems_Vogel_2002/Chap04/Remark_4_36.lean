/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_26.MapEstimator
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_15.MinimumVarianceLinear
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Remark_4_36.Covariance
import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_17

public section

noncomputable section

open scoped Matrix ProbabilityTheory

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {m : Type w} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- Helper for Remark 4.36: under the centered linear data model, the observation process
`Z` also has mean zero. -/
lemma linearObservation_mean_zero
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {N Z : Ω → EuclideanSpace ℝ m}
    {K : Matrix m n ℝ}
    (hX_memLp : MeasureTheory.MemLp X 2 μ)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (hX_mean_zero : μ[X] = 0)
    (hN_mean_zero : μ[N] = 0)
    (h_model : Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω) :
    μ[Z] = 0 := by
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hX_int : MeasureTheory.Integrable X μ := hX_memLp.integrable h_two_le
  have hN_int : MeasureTheory.Integrable N μ := hN_memLp.integrable h_two_le
  have hKX_memLp : MeasureTheory.MemLp (fun ω ↦ K.toEuclideanLin (X ω)) 2 μ := by
    simpa using hX_memLp.continuousLinearMap_comp K.toEuclideanLin.toContinuousLinearMap
  have hKX_int : MeasureTheory.Integrable (fun ω ↦ K.toEuclideanLin (X ω)) μ :=
    hKX_memLp.integrable h_two_le
  have hKX_mean : μ[fun ω ↦ K.toEuclideanLin (X ω)] = K.toEuclideanLin μ[X] := by
    simpa using ContinuousLinearMap.integral_comp_comm K.toEuclideanLin.toContinuousLinearMap hX_int
  -- Rewrite the observation mean using the linear model and integrate termwise.
  rw [h_model, MeasureTheory.integral_add hKX_int hN_int]
  -- Commute the forward operator through the expectation of `X`.
  rw [hKX_mean]
  -- The centered signal and noise assumptions force the observation mean to vanish.
  rw [hX_mean_zero, hN_mean_zero]
  simp

/-- Helper for Remark 4.36: under the centered linear model, the covariance-form estimator
acts pointwise by the covariance gain matrix on each observation. -/
lemma covarianceFormulaEstimator_apply_linearModel
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {N Z : Ω → EuclideanSpace ℝ m}
    {K : Matrix m n ℝ} {C_X : Matrix n n ℝ} {C_N : Matrix m m ℝ}
    (hX_memLp : MeasureTheory.MemLp X 2 μ)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (h_indep : ProbabilityTheory.IndepFun X N μ)
    (hX_mean_zero : μ[X] = 0)
    (hN_mean_zero : μ[N] = 0)
    (hX_cov : covarianceMatrix μ X = C_X)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω)
    (ω : Ω) :
    covarianceFormulaEstimator μ X Z ω =
      Matrix.toEuclideanLin (C_X * Kᵀ * (K * C_X * Kᵀ + C_N)⁻¹) (Z ω) := by
  -- Expand the covariance estimator and remove the centering terms using the model hypotheses.
  rw [covarianceFormulaEstimator_apply]
  rw [hX_mean_zero]
  rw [linearObservation_mean_zero hX_memLp hN_memLp hX_mean_zero hN_mean_zero h_model]
  rw [crossCovarianceMatrix_linearModel hX_memLp hN_memLp h_indep hX_cov h_model]
  rw [covarianceMatrix_linearModel hX_memLp hN_memLp h_indep hX_cov hN_cov h_model]
  -- Route correction: keep the proof in the normalized gain form and avoid unfolding larger APIs.
  simp [Matrix.mul_assoc]

/-- Helper for Remark 4.36: the covariance-gain matrix and the precision-form estimator induce
the same linear map on each observation vector. -/
lemma covarianceGain_apply_eq_precisionEstimator
    {K : Matrix m n ℝ} {C_X : Matrix n n ℝ} {C_N : Matrix m m ℝ}
    (hC_X : IsUnit C_X)
    (hC_N : IsUnit C_N)
    (h_precision : IsUnit (Kᵀ * C_N⁻¹ * K + C_X⁻¹))
    (z : EuclideanSpace ℝ m) :
    Matrix.toEuclideanLin (C_X * Kᵀ * (K * C_X * Kᵀ + C_N)⁻¹) z =
      LinearGaussian.precisionEstimator K C_N C_X z := by
  -- Transport the matrix gain identity from Exercise 4.17 to its action on `z`.
  simpa [LinearGaussian.precisionEstimator_eq, Matrix.mul_assoc] using
    congrArg (fun M ↦ Matrix.toEuclideanLin M z)
      (LinearGaussian.covarianceGain_eq_precisionGain K C_X C_N hC_X hC_N h_precision)

/-- Remark 4.36. Under the zero-mean independent linear data model
`Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω`, the covariance-form minimum-variance
linear estimator agrees with the precision-form estimator
`LinearGaussian.precisionEstimator K C_N C_X ∘ Z`. The Gaussian
assumption belongs only to the MAP derivation context, not to this gain-identity
statement. -/
theorem covarianceFormulaEstimator_eq_precisionEstimator
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {N Z : Ω → EuclideanSpace ℝ m}
    {K : Matrix m n ℝ} {C_X : Matrix n n ℝ} {C_N : Matrix m m ℝ}
    (hX_memLp : MeasureTheory.MemLp X 2 μ)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (h_indep : ProbabilityTheory.IndepFun X N μ)
    (hX_mean_zero : μ[X] = 0)
    (hN_mean_zero : μ[N] = 0)
    (hX_cov : covarianceMatrix μ X = C_X)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω)
    (hC_X : IsUnit C_X)
    (hC_N : IsUnit C_N)
    (h_precision : IsUnit (Kᵀ * C_N⁻¹ * K + C_X⁻¹)) :
    covarianceFormulaEstimator μ X Z =
      LinearGaussian.precisionEstimator K C_N C_X ∘ Z := by
  funext ω
  -- First normalize the covariance-form estimator to the covariance gain matrix.
  rw [covarianceFormulaEstimator_apply_linearModel hX_memLp hN_memLp h_indep hX_mean_zero
    hN_mean_zero hX_cov hN_cov h_model]
  -- Then replace the covariance gain by the precision gain from Exercise 4.17.
  simpa using covarianceGain_apply_eq_precisionEstimator hC_X hC_N h_precision (Z ω)

/-- The observation-level form of
`ProbabilityTheory.covarianceFormulaEstimator_eq_precisionEstimator`. -/
theorem covarianceFormulaEstimator_apply_eq_precisionEstimator
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} {N Z : Ω → EuclideanSpace ℝ m}
    {K : Matrix m n ℝ} {C_X : Matrix n n ℝ} {C_N : Matrix m m ℝ}
    (hX_memLp : MeasureTheory.MemLp X 2 μ)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (h_indep : ProbabilityTheory.IndepFun X N μ)
    (hX_mean_zero : μ[X] = 0)
    (hN_mean_zero : μ[N] = 0)
    (hX_cov : covarianceMatrix μ X = C_X)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin (X ω) + N ω)
    (hC_X : IsUnit C_X)
    (hC_N : IsUnit C_N)
    (h_precision : IsUnit (Kᵀ * C_N⁻¹ * K + C_X⁻¹))
    (ω : Ω) :
    covarianceFormulaEstimator μ X Z ω =
      LinearGaussian.precisionEstimator K C_N C_X (Z ω) := by
  simpa using congrArg (fun F ↦ F ω)
    (covarianceFormulaEstimator_eq_precisionEstimator
      hX_memLp hN_memLp h_indep hX_mean_zero hN_mean_zero hX_cov hN_cov h_model
      hC_X hC_N h_precision)

end

end ProbabilityTheory
