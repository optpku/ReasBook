/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.WhiteNoise
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_35
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

noncomputable section

open scoped Matrix

namespace FilterRegularization

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {A : Matrix n n ℝ} {gTrue : EuclideanSpace ℝ n}
variable {η : Ω → EuclideanSpace ℝ n} {σ : ℝ}

/-- The predictive error vector attached to a fixed influence matrix `A`, noiseless
data vector `gTrue`, and noise realization `noise`. -/
def predictiveError
    (A : Matrix n n ℝ) (gTrue noise : EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  regularizedResidual A gTrue + A.toEuclideanLin noise

/-- The defining formula for `predictiveError`. -/
@[simp] theorem predictiveError_eq
    (A : Matrix n n ℝ) (gTrue noise : EuclideanSpace ℝ n) :
    predictiveError A gTrue noise = regularizedResidual A gTrue + A.toEuclideanLin noise := by
  -- This is the defining expansion of `predictiveError`.
  rfl

/-- The fixed-`A` expected predictive risk is the expectation of
`predictiveRisk (predictiveError A gTrue (η ω))`. -/
def expectedPredictiveRisk
    (μ : MeasureTheory.Measure Ω) (A : Matrix n n ℝ)
    (gTrue : EuclideanSpace ℝ n) (η : Ω → EuclideanSpace ℝ n) : ℝ :=
  ∫ ω, predictiveRisk (predictiveError A gTrue (η ω)) ∂μ

/-- The defining formula for `expectedPredictiveRisk`. -/
@[simp] theorem expectedPredictiveRisk_def
    (μ : MeasureTheory.Measure Ω) (A : Matrix n n ℝ)
    (gTrue : EuclideanSpace ℝ n) (η : Ω → EuclideanSpace ℝ n) :
    expectedPredictiveRisk μ A gTrue η =
      ∫ ω, predictiveRisk (predictiveError A gTrue (η ω)) ∂μ := by
  -- This is the defining integral for `expectedPredictiveRisk`.
  rfl

/-- The fixed-`A` expected residual risk is the expectation of
`predictiveRisk (regularizedResidual A (gTrue + η ω))`. -/
def expectedResidualRisk
    (μ : MeasureTheory.Measure Ω) (A : Matrix n n ℝ)
    (gTrue : EuclideanSpace ℝ n) (η : Ω → EuclideanSpace ℝ n) : ℝ :=
  ∫ ω, predictiveRisk (regularizedResidual A (gTrue + η ω)) ∂μ

/-- The defining formula for `expectedResidualRisk`. -/
@[simp] theorem expectedResidualRisk_def
    (μ : MeasureTheory.Measure Ω) (A : Matrix n n ℝ)
    (gTrue : EuclideanSpace ℝ n) (η : Ω → EuclideanSpace ℝ n) :
    expectedResidualRisk μ A gTrue η =
      ∫ ω, predictiveRisk (regularizedResidual A (gTrue + η ω)) ∂μ := by
  -- This is the defining integral for `expectedResidualRisk`.
  rfl

/-- Helper for Proposition 7.8: `regularizedResidual` distributes over adding a
noise vector to the data vector. -/
lemma regularizedResidual_add_eq
    (A : Matrix n n ℝ) (g noise : EuclideanSpace ℝ n) :
    regularizedResidual A (g + noise) =
      regularizedResidual A g + (A - 1).toEuclideanLin noise := by
  -- Normalize both sides to the same linear map `(A - 1).toEuclideanLin`.
  rw [regularizedResidual_eq, regularizedResidual_eq]
  simpa using ((A - 1).toEuclideanLin.map_add g noise)

/-- Helper for Proposition 7.8: the mean-zero white-noise hypothesis remains
zero after applying a fixed matrix and pairing with a fixed vector. -/
lemma integral_inner_const_toEuclideanLin_noise_eq_zero
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (b : EuclideanSpace ℝ n) (B : Matrix n n ℝ) :
    ∫ ω, inner ℝ b (B.toEuclideanLin (η ω)) ∂μ = 0 := by
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hNoiseLp : MeasureTheory.MemLp (fun ω ↦ B.toEuclideanLin (η ω)) 2 μ := by
    simpa using hη.memLp.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hNoiseInt : MeasureTheory.Integrable (fun ω ↦ B.toEuclideanLin (η ω)) μ :=
    hNoiseLp.integrable h_two_le
  have hEtaInt : MeasureTheory.Integrable η μ := hη.memLp.integrable h_two_le
  have hMeanZero :
      ∫ ω, B.toEuclideanLin (η ω) ∂μ = 0 := by
    -- Commute the fixed linear map through the integral and use `hη.mean_zero`.
    rw [show ∫ ω, B.toEuclideanLin (η ω) ∂μ = B.toEuclideanLin (∫ ω, η ω ∂μ) by
      simpa using
        ContinuousLinearMap.integral_comp_comm B.toEuclideanLin.toContinuousLinearMap hEtaInt]
    rw [hη.mean_zero]
    simp
  -- Rewrite the scalar pairing integral through the vector-valued mean.
  rw [integral_inner hNoiseInt, hMeanZero]
  simp

/-- Helper for Proposition 7.8: the expected squared norm of the linear image
of semidiscrete white noise is the corresponding transpose-mul trace. -/
lemma integral_sqNorm_toEuclideanLin_noise_eq_sigma_sq_trace_transpose_mul
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (B : Matrix n n ℝ) :
    ∫ ω, ‖B.toEuclideanLin (η ω)‖ ^ 2 ∂μ =
      σ ^ 2 * Matrix.trace (Bᵀ * B) := by
  have hLinearEq :
      (fun ω ↦ B.toEuclideanLin (η ω)) = ProbabilityTheory.linearEstimator B η := by
    funext ω
    rw [ProbabilityTheory.linearEstimator_apply]
  have hNoiseLp : MeasureTheory.MemLp (fun ω ↦ B.toEuclideanLin (η ω)) 2 μ := by
    simpa using hη.memLp.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hCycle : Matrix.trace (B * Bᵀ) = Matrix.trace (Bᵀ * B) := by
    -- Cycle the trace once to move the transpose factor to the front.
    simpa using (Matrix.trace_mul_cycle (1 : Matrix n n ℝ) B Bᵀ)
  -- Convert the expected squared norm to a trace and then insert the isotropic second moment.
  calc
    ∫ ω, ‖B.toEuclideanLin (η ω)‖ ^ 2 ∂μ
        = Matrix.trace (ProbabilityTheory.secondMomentMatrix μ (fun ω ↦ B.toEuclideanLin (η ω))) := by
            rw [ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix hNoiseLp]
    _ = Matrix.trace (B * ProbabilityTheory.secondMomentMatrix μ η * Bᵀ) := by
          rw [hLinearEq, ProbabilityTheory.MinimumVarianceLinear.secondMomentMatrix_linearEstimator
            hη.memLp B]
    _ = Matrix.trace (B * (σ ^ 2 • (1 : Matrix n n ℝ)) * Bᵀ) := by
          rw [hη.secondMoment_eq]
    _ = Matrix.trace (σ ^ 2 • (B * 1 * Bᵀ)) := by
          simp
    _ = (σ ^ 2 : ℝ) • Matrix.trace (B * 1 * Bᵀ) := by
          rw [Matrix.trace_smul]
    _ = σ ^ 2 * Matrix.trace (B * 1 * Bᵀ) := by
          simp
    _ = σ ^ 2 * Matrix.trace (B * Bᵀ) := by
          simp
    _ = σ ^ 2 * Matrix.trace (Bᵀ * B) := by
          rw [hCycle]

/-- Under the Chapter 7 semidiscrete white-noise model, the expected predictive
risk splits into the deterministic bias term and the transpose-mul trace
variance term. -/
theorem expectedPredictiveRisk_eq_bias_add_trace_transpose_mul
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (A : Matrix n n ℝ) (gTrue : EuclideanSpace ℝ n) :
    expectedPredictiveRisk μ A gTrue η =
      predictiveRisk (regularizedResidual A gTrue) +
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (Aᵀ * A) := by
  let bias : EuclideanSpace ℝ n := regularizedResidual A gTrue
  let noise : Ω → EuclideanSpace ℝ n := fun ω ↦ A.toEuclideanLin (η ω)
  let invCard : ℝ := (Fintype.card n : ℝ)⁻¹
  let cross : Ω → ℝ := fun ω ↦ (2 * invCard) * inner ℝ bias (noise ω)
  let variance : Ω → ℝ := fun ω ↦ invCard * ‖noise ω‖ ^ 2
  let constBias : Ω → ℝ := fun _ ↦ predictiveRisk bias
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hNoiseLp : MeasureTheory.MemLp noise 2 μ := by
    -- The predictive noise term is a fixed continuous linear image of `η`.
    simpa [noise] using hη.memLp.continuousLinearMap_comp A.toEuclideanLin.toContinuousLinearMap
  have hNoiseInt : MeasureTheory.Integrable noise μ := hNoiseLp.integrable h_two_le
  have hNoiseSqInt : MeasureTheory.Integrable (fun ω ↦ ‖noise ω‖ ^ 2) μ := by
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 2) hNoiseLp (by decide)
  have hCrossInt : MeasureTheory.Integrable cross μ := by
    -- The cross term is a constant multiple of the integrable scalar pairing.
    simpa [cross, noise, bias, invCard, mul_assoc, mul_left_comm, mul_comm] using
      (hNoiseInt.const_inner bias).const_mul (2 * invCard)
  have hVarianceInt : MeasureTheory.Integrable variance μ := by
    -- The variance term is a constant multiple of the squared-norm integrand.
    simpa [variance, invCard] using hNoiseSqInt.const_mul invCard
  have hConstBiasInt : MeasureTheory.Integrable constBias μ :=
    MeasureTheory.integrable_const _
  have hPointwise :
      (fun ω ↦ predictiveRisk (predictiveError A gTrue (η ω))) =
        fun ω ↦ constBias ω + cross ω + variance ω := by
    -- Expand `‖bias + noise‖^2` into bias, cross, and variance pieces.
    funext ω
    rw [predictiveError_eq, predictiveRisk_def]
    simp [bias, noise, cross, variance, constBias, invCard, div_eq_mul_inv, norm_add_sq_real,
      real_inner_comm]
    ring
  have hAssoc :
      (fun ω ↦ constBias ω + cross ω + variance ω) =
        fun ω ↦ constBias ω + (cross ω + variance ω) := by
    funext ω
    ring
  have hSplit :
      ∫ ω, constBias ω + (cross ω + variance ω) ∂μ =
        ∫ ω, constBias ω ∂μ + ∫ ω, cross ω + variance ω ∂μ := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := constBias) (g := cross + variance)
        hConstBiasInt (hCrossInt.add hVarianceInt))
  have hCrossVarianceSplit :
      ∫ ω, cross ω + variance ω ∂μ = ∫ ω, cross ω ∂μ + ∫ ω, variance ω ∂μ := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := cross) (g := variance) hCrossInt hVarianceInt)
  have hCrossZero : ∫ ω, cross ω ∂μ = 0 := by
    -- The white-noise mean-zero condition kills the mixed term.
    rw [show cross = fun ω ↦ (2 * invCard) * inner ℝ bias (noise ω) by
      funext ω
      simp [cross]]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_inner_const_toEuclideanLin_noise_eq_zero (μ := μ) (η := η) (σ := σ) hη bias A]
    simp
  have hVariance :
      ∫ ω, variance ω ∂μ = (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (Aᵀ * A) := by
    -- The variance term is the normalized trace of `Aᵀ * A`.
    rw [show variance = fun ω ↦ invCard * ‖noise ω‖ ^ 2 by
      funext ω
      simp [variance]]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_sqNorm_toEuclideanLin_noise_eq_sigma_sq_trace_transpose_mul
      (μ := μ) (η := η) (σ := σ) hη A]
    simp [invCard, div_eq_mul_inv, mul_left_comm, mul_comm]
  -- Route correction: after normalizing to `bias + A η`, the rest is a flat integral split.
  rw [expectedPredictiveRisk_def, hPointwise, hAssoc, hSplit, hCrossVarianceSplit, hCrossZero,
    hVariance, MeasureTheory.integral_const]
  simp [bias]

/-- Under the Chapter 7 semidiscrete white-noise model, the expected residual
risk splits into the deterministic bias term and the transpose-mul trace
variance term for `A - 1`. -/
theorem expectedResidualRisk_eq_bias_add_trace_transpose_mul
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (A : Matrix n n ℝ) (gTrue : EuclideanSpace ℝ n) :
    expectedResidualRisk μ A gTrue η =
      predictiveRisk (regularizedResidual A gTrue) +
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((A - 1)ᵀ * (A - 1)) := by
  let bias : EuclideanSpace ℝ n := regularizedResidual A gTrue
  let noise : Ω → EuclideanSpace ℝ n := fun ω ↦ (A - 1).toEuclideanLin (η ω)
  let invCard : ℝ := (Fintype.card n : ℝ)⁻¹
  let cross : Ω → ℝ := fun ω ↦ (2 * invCard) * inner ℝ bias (noise ω)
  let variance : Ω → ℝ := fun ω ↦ invCard * ‖noise ω‖ ^ 2
  let constBias : Ω → ℝ := fun _ ↦ predictiveRisk bias
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hNoiseLp : MeasureTheory.MemLp noise 2 μ := by
    -- The residual noise term is a fixed continuous linear image of `η`.
    simpa [noise] using
      hη.memLp.continuousLinearMap_comp (A - 1).toEuclideanLin.toContinuousLinearMap
  have hNoiseInt : MeasureTheory.Integrable noise μ := hNoiseLp.integrable h_two_le
  have hNoiseSqInt : MeasureTheory.Integrable (fun ω ↦ ‖noise ω‖ ^ 2) μ := by
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 2) hNoiseLp (by decide)
  have hCrossInt : MeasureTheory.Integrable cross μ := by
    -- The cross term is a constant multiple of the integrable scalar pairing.
    simpa [cross, noise, bias, invCard, mul_assoc, mul_left_comm, mul_comm] using
      (hNoiseInt.const_inner bias).const_mul (2 * invCard)
  have hVarianceInt : MeasureTheory.Integrable variance μ := by
    -- The variance term is a constant multiple of the squared-norm integrand.
    simpa [variance, invCard] using hNoiseSqInt.const_mul invCard
  have hConstBiasInt : MeasureTheory.Integrable constBias μ :=
    MeasureTheory.integrable_const _
  have hPointwise :
      (fun ω ↦ predictiveRisk (regularizedResidual A (gTrue + η ω))) =
        fun ω ↦ constBias ω + cross ω + variance ω := by
    -- Rewrite the residual into deterministic bias plus `(A - 1)`-noise.
    funext ω
    rw [regularizedResidual_add_eq]
    rw [predictiveRisk_def]
    simp [bias, noise, cross, variance, constBias, invCard, div_eq_mul_inv, norm_add_sq_real]
    ring
  have hAssoc :
      (fun ω ↦ constBias ω + cross ω + variance ω) =
        fun ω ↦ constBias ω + (cross ω + variance ω) := by
    funext ω
    ring
  have hSplit :
      ∫ ω, constBias ω + (cross ω + variance ω) ∂μ =
        ∫ ω, constBias ω ∂μ + ∫ ω, cross ω + variance ω ∂μ := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := constBias) (g := cross + variance)
        hConstBiasInt (hCrossInt.add hVarianceInt))
  have hCrossVarianceSplit :
      ∫ ω, cross ω + variance ω ∂μ = ∫ ω, cross ω ∂μ + ∫ ω, variance ω ∂μ := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := cross) (g := variance) hCrossInt hVarianceInt)
  have hCrossZero : ∫ ω, cross ω ∂μ = 0 := by
    -- The white-noise mean-zero condition again removes the mixed term.
    rw [show cross = fun ω ↦ (2 * invCard) * inner ℝ bias (noise ω) by
      funext ω
      simp [cross]]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_inner_const_toEuclideanLin_noise_eq_zero
      (μ := μ) (η := η) (σ := σ) hη bias (A - 1)]
    simp
  have hVariance :
      ∫ ω, variance ω ∂μ =
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((A - 1)ᵀ * (A - 1)) := by
    -- The variance term is the normalized trace of `(A - 1)ᵀ * (A - 1)`.
    rw [show variance = fun ω ↦ invCard * ‖noise ω‖ ^ 2 by
      funext ω
      simp [variance]]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_sqNorm_toEuclideanLin_noise_eq_sigma_sq_trace_transpose_mul
      (μ := μ) (η := η) (σ := σ) hη (A - 1)]
    simp [invCard, div_eq_mul_inv, mul_assoc, mul_comm]
  -- Route correction: normalize the residual integrand first, then repeat the same split.
  rw [expectedResidualRisk_def, hPointwise, hAssoc, hSplit, hCrossVarianceSplit, hCrossZero,
    hVariance, MeasureTheory.integral_const]
  simp [bias]

end

end FilterRegularization

end
