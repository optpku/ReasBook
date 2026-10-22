/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_31.BestLinearUnbiased
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_12.Covariance
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_35
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Theorem_4_32.Operator
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Probability.Moments.Variance

public section

noncomputable section

open scoped Matrix ProbabilityTheory

open LinearGaussian

namespace ProbabilityTheory

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {m : Type w} [Fintype m] [DecidableEq m]

/-- Helper for Theorem 4.32: composing two matrix-induced Euclidean operators is the same as
applying the product matrix once. -/
lemma toEuclideanLin_mul_apply
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) (x : EuclideanSpace ℝ m) :
    A.toEuclideanLin (B.toEuclideanLin x) = (A * B).toEuclideanLin x := by
  -- Move to coordinate functions so the claim becomes `mulVec_mulVec`.
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

omit [Fintype n] [DecidableEq n] in
/-- Helper for Theorem 4.32: covariance matrices are symmetric. -/
lemma covarianceMatrix_isSymm_local
    {μ : MeasureTheory.Measure Ω} {X : Ω → EuclideanSpace ℝ n} :
    Matrix.IsSymm (covarianceMatrix μ X) := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  rw [covarianceMatrix_apply, covarianceMatrix_apply, covariance_comm]

omit [DecidableEq n] in
/-- Helper for Theorem 4.32: covariance matrices of finite random vectors are positive
semidefinite. -/
lemma covarianceMatrix_posSemidef_of_memLp
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} (hX : MeasureTheory.MemLp X 2 μ) :
    (covarianceMatrix μ X).PosSemidef := sorry

/-- Helper for Theorem 4.32: an invertible covariance matrix is positive definite once the
noise covariance is known to be positive semidefinite. -/
lemma covarianceMatrixPosDef_of_isUnit
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {C_N : Matrix m m ℝ} {N : Ω → EuclideanSpace ℝ m}
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (hN_cov : covarianceMatrix μ N = C_N)
    (hC_N : IsUnit C_N) :
    C_N.PosDef := by
  -- Upgrade the covariance matrix from semidefinite to definite by combining positivity
  -- of covariance with the assumed invertibility of `C_N`.
  have hpsd : (covarianceMatrix μ N).PosSemidef :=
    covarianceMatrix_posSemidef_of_memLp hN_memLp
  rw [hN_cov] at hpsd
  exact (hpsd.posDef_iff_isUnit).2 hC_N

/-- Helper for Theorem 4.32: the weighted Gramian `Kᵀ * C_N⁻¹ * K` is positive definite when
`K` has full column rank and `C_N` is positive definite. -/
lemma weightedGramianPosDef
    {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N_posDef : C_N.PosDef) :
    (Kᵀ * C_N⁻¹ * K).PosDef := sorry

omit [DecidableEq n] in
/-- Helper for Theorem 4.32: a centered random vector has second moment matrix equal to its
covariance matrix. -/
lemma secondMomentMatrix_eq_covarianceMatrix_of_centered
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ n} (hX : MeasureTheory.MemLp X 2 μ)
    (h_mean_zero : μ[X] = 0) :
    secondMomentMatrix μ X = covarianceMatrix μ X := by
  have hXcoord : ∀ k, MeasureTheory.MemLp (fun ω ↦ X ω k) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX
  ext i j
  have hXi : μ[fun ω ↦ X ω i] = 0 := by
    simpa [MeasureTheory.eval_integral_piLp
      (fun k ↦ (hXcoord k).integrable (by norm_num)) i] using
      congrArg (fun x : EuclideanSpace ℝ n ↦ x i) h_mean_zero
  have hXj : μ[fun ω ↦ X ω j] = 0 := by
    simpa [MeasureTheory.eval_integral_piLp
      (fun k ↦ (hXcoord k).integrable (by norm_num)) j] using
      congrArg (fun x : EuclideanSpace ℝ n ↦ x j) h_mean_zero
  rw [secondMomentMatrix_apply, covarianceMatrix_apply]
  rw [ProbabilityTheory.covariance_eq_sub (hXcoord i) (hXcoord j)]
  simp [hXi, hXj]

/-- Helper for Theorem 4.32: the precision-form Gauss-Markov coefficient is a left inverse of
`K` when `K` has full column rank and `C_N` is positive definite. -/
lemma gaussMarkovOperator_mul
    {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N_posDef : C_N.PosDef) :
    gaussMarkovOperator K C_N * K = 1 := sorry

/-- Helper for Theorem 4.32: transposing the Gauss-Markov coefficient gives the clean covariance
identity `C_N * B̂ᵀ = K * (Kᵀ * C_N⁻¹ * K)⁻¹`. -/
lemma covarianceMul_gaussMarkovOperator_transpose
    {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N_posDef : C_N.PosDef) :
    C_N * (gaussMarkovOperator K C_N)ᵀ =
      K * (Kᵀ * C_N⁻¹ * K)⁻¹ := sorry

/-- Helper for Theorem 4.32: every unbiased coefficient matrix rewrites the BLUE objective to the
deterministic trace `trace (B * C_N * Bᵀ)`. -/
lemma blueObjective_eq_trace_of_unbiasedLinearEstimator
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {x : EuclideanSpace ℝ n} {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    {N Z : Ω → EuclideanSpace ℝ m} (B : Matrix n m ℝ)
    (hBK : B * K = 1)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (hN_mean_zero : μ[N] = 0)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin x + N ω) :
    blueObjective μ x (linearEstimator B Z) = Matrix.trace (B * C_N * Bᵀ) := by
  have hBN_memLp : MeasureTheory.MemLp (linearEstimator B N) 2 μ := by
    rw [show linearEstimator B N = fun ω ↦ B.toEuclideanLin (N ω) by
      funext ω
      rw [linearEstimator_apply]]
    exact hN_memLp.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hSignal :
      B.toEuclideanLin (K.toEuclideanLin x) = x := by
    calc
      B.toEuclideanLin (K.toEuclideanLin x) = (B * K).toEuclideanLin x := by
        exact ProbabilityTheory.toEuclideanLin_mul_apply B K x
      _ = x := by
        simp [hBK]
  have hPointwise :
      (fun ω ↦ linearEstimator B Z ω - x) = linearEstimator B N := by
    -- Use the unbiasedness constraint `B * K = 1` to remove the deterministic signal term.
    funext ω
    rw [h_model, linearEstimator_apply, linearEstimator_apply]
    calc
      B.toEuclideanLin (K.toEuclideanLin x + N ω) - x
          = (B.toEuclideanLin (K.toEuclideanLin x) + B.toEuclideanLin (N ω)) - x := by
              simp
      _ = (x + B.toEuclideanLin (N ω)) - x := by rw [hSignal]
      _ = B.toEuclideanLin (N ω) := by simp
  have hNormPointwise :
      (fun ω ↦ ‖linearEstimator B Z ω - x‖ ^ 2) = fun ω ↦ ‖linearEstimator B N ω‖ ^ 2 := by
    funext ω
    have hPointwiseAt : linearEstimator B Z ω - x = linearEstimator B N ω := by
      simpa using congrArg (fun f : Ω → EuclideanSpace ℝ n ↦ f ω) hPointwise
    simp [hPointwiseAt]
  -- Convert the expectation of the squared norm into a trace of the second-moment matrix.
  rw [blueObjective_def]
  calc
    ∫ ω, ‖linearEstimator B Z ω - x‖ ^ 2 ∂μ
        = ∫ ω, ‖linearEstimator B N ω‖ ^ 2 ∂μ := by rw [hNormPointwise]
    _ = Matrix.trace (secondMomentMatrix μ (linearEstimator B N)) := by
          rw [ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix hBN_memLp]
    _ = Matrix.trace (B * secondMomentMatrix μ N * Bᵀ) := by
          rw [MinimumVarianceLinear.secondMomentMatrix_linearEstimator hN_memLp B]
    _ = Matrix.trace (B * C_N * Bᵀ) := by
          rw [secondMomentMatrix_eq_covarianceMatrix_of_centered hN_memLp hN_mean_zero, hN_cov]

/-- Helper for Theorem 4.32: completing the square around the Gauss-Markov coefficient leaves a
nonnegative remainder trace. -/
lemma gaussMarkovTraceCompletion
    {K : Matrix m n ℝ} {C_N : Matrix m m ℝ} (B : Matrix n m ℝ)
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N_posDef : C_N.PosDef)
    (hBK : B * K = 1) :
    Matrix.trace (B * C_N * Bᵀ) =
      Matrix.trace
          (gaussMarkovOperator K C_N * C_N * (gaussMarkovOperator K C_N)ᵀ) +
        Matrix.trace
          ((B - gaussMarkovOperator K C_N) * C_N * (B - gaussMarkovOperator K C_N)ᵀ) := by
  let B0 : Matrix n m ℝ := gaussMarkovOperator K C_N
  let G : Matrix n n ℝ := Kᵀ * C_N⁻¹ * K
  have hB0K : B0 * K = 1 :=
    gaussMarkovOperator_mul h_fullRank hC_N_posDef
  have hC_N_transpose : C_Nᵀ = C_N := by
    exact hC_N_posDef.1.eq
  have hCovTranspose : C_N * B0ᵀ = K * G⁻¹ := by
    simpa [B0, G] using
      covarianceMul_gaussMarkovOperator_transpose h_fullRank hC_N_posDef
  let M : Matrix n m ℝ := B - B0
  have hMK : M * K = 0 := by
    -- The perturbation matrix lies in the nullspace imposed by the unbiasedness constraint.
    simp [M, Matrix.sub_mul, hBK, hB0K]
  have hMixedRight : M * C_N * B0ᵀ = 0 := by
    -- Rewrite the covariance-side term through `C_N * B0ᵀ = K * G⁻¹` and use `M * K = 0`.
    calc
      M * C_N * B0ᵀ = M * (C_N * B0ᵀ) := by rw [Matrix.mul_assoc]
      _ = M * (K * G⁻¹) := by rw [hCovTranspose]
      _ = (M * K) * G⁻¹ := by rw [← Matrix.mul_assoc]
      _ = 0 := by simp [hMK]
  have hMixedLeft : B0 * C_N * Mᵀ = 0 := by
    -- The left mixed term is the transpose of the right mixed term.
    have hTranspose := congrArg Matrix.transpose hMixedRight
    simpa [Matrix.transpose_mul, hC_N_transpose, Matrix.mul_assoc] using hTranspose
  have hDecomp : B = B0 + M := by
    simp [B0, M]
  have hTraceRight :
      Matrix.trace (B * C_N * B0ᵀ) = Matrix.trace (B0 * C_N * B0ᵀ) := by
    -- Expand the right mixed trace and discard the vanishing perturbation term.
    calc
      Matrix.trace (B * C_N * B0ᵀ)
          = Matrix.trace ((B0 + M) * C_N * B0ᵀ) := by rw [hDecomp]
      _ = Matrix.trace ((B0 * C_N + M * C_N) * B0ᵀ) := by
            rw [Matrix.add_mul]
      _ = Matrix.trace (B0 * C_N * B0ᵀ + M * C_N * B0ᵀ) := by
            rw [Matrix.add_mul]
      _ = Matrix.trace (B0 * C_N * B0ᵀ) := by
            rw [Matrix.trace_add, hMixedRight]
            simp
  have hTraceLeft :
      Matrix.trace (B0 * C_N * Bᵀ) = Matrix.trace (B0 * C_N * B0ᵀ) := by
    -- Expand the left mixed trace and discard the transposed vanishing term.
    calc
      Matrix.trace (B0 * C_N * Bᵀ)
          = Matrix.trace (B0 * C_N * (B0 + M)ᵀ) := by rw [hDecomp]
      _ = Matrix.trace (B0 * C_N * (B0ᵀ + Mᵀ)) := by rw [Matrix.transpose_add]
      _ = Matrix.trace (B0 * C_N * B0ᵀ + B0 * C_N * Mᵀ) := by
            rw [Matrix.mul_add]
      _ = Matrix.trace (B0 * C_N * B0ᵀ) := by
            rw [Matrix.trace_add, hMixedLeft]
            simp
  have hRemainder :
      Matrix.trace (M * C_N * Mᵀ) =
        Matrix.trace (B * C_N * Bᵀ) -
          Matrix.trace (B * C_N * B0ᵀ) -
          Matrix.trace (B0 * C_N * Bᵀ) +
          Matrix.trace (B0 * C_N * B0ᵀ) := by
    -- Expand the perturbation square exactly as in the textbook completion-of-the-square step.
    calc
      Matrix.trace (M * C_N * Mᵀ)
          = Matrix.trace (((B - B0) * C_N) * (B - B0)ᵀ) := by
              simp [M, Matrix.mul_assoc]
      _ = Matrix.trace (((B * C_N) - (B0 * C_N)) * (Bᵀ - B0ᵀ)) := by
            simp [Matrix.sub_mul, Matrix.transpose_sub]
      _ = Matrix.trace (((B * C_N) * Bᵀ - (B * C_N) * B0ᵀ) -
            ((B0 * C_N) * Bᵀ - (B0 * C_N) * B0ᵀ)) := by
            rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      _ = Matrix.trace ((B * C_N) * Bᵀ - (B * C_N) * B0ᵀ) -
            Matrix.trace ((B0 * C_N) * Bᵀ - (B0 * C_N) * B0ᵀ) := by
            rw [Matrix.trace_sub]
      _ = (Matrix.trace ((B * C_N) * Bᵀ) - Matrix.trace ((B * C_N) * B0ᵀ)) -
            (Matrix.trace ((B0 * C_N) * Bᵀ) - Matrix.trace ((B0 * C_N) * B0ᵀ)) := by
            rw [Matrix.trace_sub, Matrix.trace_sub]
      _ = _ := by ring
  -- After substituting the vanishing mixed traces, only the quadratic remainder survives.
  rw [hTraceRight, hTraceLeft] at hRemainder
  linarith

/-- thm_4_32 (Theorem 4.32, Gauss-Markov). Under the linear observation model
`Z = fun ω ↦ K.toEuclideanLin x + N ω` with zero-mean noise of covariance `C_N`,
nonsingular `C_N`, and full-rank `K`, the estimator
`linearEstimator (LinearGaussian.gaussMarkovOperator K C_N) Z` is a best linear
unbiased estimator of `x` from `Z`. -/
theorem isBestLinearUnbiasedEstimator_gaussMarkov
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {x : EuclideanSpace ℝ n} {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    {N Z : Ω → EuclideanSpace ℝ m}
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N : IsUnit C_N)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (hN_mean_zero : μ[N] = 0)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin x + N ω) :
    IsBestLinearUnbiasedEstimator μ x Z
      (linearEstimator (gaussMarkovOperator K C_N) Z) := sorry

/-- The Gauss-Markov estimator belongs to the Chapter 4 BLUE admissible class under the
hypotheses of Theorem 4.32. -/
theorem isBestLinearUnbiasedEstimator_gaussMarkov_mem_blueAdmissibleSet
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {x : EuclideanSpace ℝ n} {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    {N Z : Ω → EuclideanSpace ℝ m}
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N : IsUnit C_N)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (hN_mean_zero : μ[N] = 0)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin x + N ω) :
    linearEstimator (gaussMarkovOperator K C_N) Z ∈ blueAdmissibleSet μ x Z := sorry

/-- The Gauss-Markov estimator minimizes `blueObjective μ x` on the Chapter 4 BLUE admissible
class under the hypotheses of Theorem 4.32. -/
theorem isBestLinearUnbiasedEstimator_gaussMarkov_optimal
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {x : EuclideanSpace ℝ n} {K : Matrix m n ℝ} {C_N : Matrix m m ℝ}
    {N Z : Ω → EuclideanSpace ℝ m}
    (h_fullRank : Function.Injective K.toEuclideanLin)
    (hC_N : IsUnit C_N)
    (hN_memLp : MeasureTheory.MemLp N 2 μ)
    (hN_mean_zero : μ[N] = 0)
    (hN_cov : covarianceMatrix μ N = C_N)
    (h_model : Z = fun ω ↦ K.toEuclideanLin x + N ω) :
    IsMinOn (blueObjective μ x) (blueAdmissibleSet μ x Z)
      (linearEstimator (gaussMarkovOperator K C_N) Z) := sorry

end

end ProbabilityTheory
