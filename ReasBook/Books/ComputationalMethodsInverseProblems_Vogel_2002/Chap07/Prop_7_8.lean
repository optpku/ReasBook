/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_1
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5.SpectralRepresentation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_8.Risk
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Symmetric

public section

noncomputable section

open scoped BigOperators Matrix

namespace FilterRegularization

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {K Rα U V : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
variable {fTrue : EuclideanSpace ℝ n} {η : Ω → EuclideanSpace ℝ n} {σ : ℝ}

/-- Proposition 7.8 source object: `Aα` is the influence matrix attached to the
forward matrix `K` and the reconstruction matrix `Rα`. -/
def Aα (K Rα : Matrix n n ℝ) : Matrix n n ℝ :=
  influenceMatrix K Rα

omit [DecidableEq n] in
 /-- The source object `Aα` is the canonical influence matrix `K * Rα`. -/
@[simp] theorem Aα_def (K Rα : Matrix n n ℝ) :
    Aα K Rα = K * Rα := by
  simp [Aα]

/-- Proposition 7.8 source object: the predictive-error vector `pα` under the
Chapter 7 semidiscrete model. -/
def pα
    (K Rα : Matrix n n ℝ) (fTrue : EuclideanSpace ℝ n)
    (η : Ω → EuclideanSpace ℝ n) : Ω → EuclideanSpace ℝ n :=
  fun ω ↦ predictiveError (Aα K Rα) (K.toEuclideanLin fTrue) (η ω)

omit [MeasurableSpace Ω] in
 /-- Evaluate the Chapter 7 predictive-error vector `pα` at a sample `ω`. -/
@[simp] theorem pα_apply
    (K Rα : Matrix n n ℝ) (fTrue : EuclideanSpace ℝ n)
    (η : Ω → EuclideanSpace ℝ n) (ω : Ω) :
    pα K Rα fTrue η ω =
      predictiveError (Aα K Rα) (K.toEuclideanLin fTrue) (η ω) := by
  simp [pα]

/-- Proposition 7.8 source object: the residual vector `rα` under the Chapter 7
semidiscrete model. -/
def rα
    (K Rα : Matrix n n ℝ) (fTrue : EuclideanSpace ℝ n)
    (η : Ω → EuclideanSpace ℝ n) : Ω → EuclideanSpace ℝ n :=
  fun ω ↦ regularizedResidual (Aα K Rα) (K.toEuclideanLin fTrue + η ω)

omit [MeasurableSpace Ω] in
 /-- Evaluate the Chapter 7 residual vector `rα` at a sample `ω`. -/
@[simp] theorem rα_apply
    (K Rα : Matrix n n ℝ) (fTrue : EuclideanSpace ℝ n)
    (η : Ω → EuclideanSpace ℝ n) (ω : Ω) :
    rα K Rα fTrue η ω =
      regularizedResidual (Aα K Rα) (K.toEuclideanLin fTrue + η ω) := by
  simp [rα]

/-- The backend expected predictive risk for `Aα` is exactly the expectation of
the normalized squared Chapter 7 predictive-error vector `pα`. -/
@[simp] theorem expectedPredictiveRisk_Aα_eq_integral_pα
    (μ : MeasureTheory.Measure Ω) (K Rα : Matrix n n ℝ)
    (fTrue : EuclideanSpace ℝ n) (η : Ω → EuclideanSpace ℝ n) :
    expectedPredictiveRisk μ (Aα K Rα) (K.toEuclideanLin fTrue) η =
      ∫ ω, predictiveRisk (pα K Rα fTrue η ω) ∂μ := by
  rw [expectedPredictiveRisk_def]
  simp [pα]

/-- The backend expected residual risk for `Aα` is exactly the expectation of
the normalized squared Chapter 7 residual vector `rα`. -/
@[simp] theorem expectedResidualRisk_Aα_eq_integral_rα
    (μ : MeasureTheory.Measure Ω) (K Rα : Matrix n n ℝ)
    (fTrue : EuclideanSpace ℝ n) (η : Ω → EuclideanSpace ℝ n) :
    expectedResidualRisk μ (Aα K Rα) (K.toEuclideanLin fTrue) η =
      ∫ ω, predictiveRisk (rα K Rα fTrue η ω) ∂μ := by
  rw [expectedResidualRisk_def]
  simp [rα]

/-- Under the Chapter 7 SVD/filter-factor setup, the source influence matrix
`Aα` has the spectral representation `(7.39)`. -/
theorem Aα_hasInfluenceMatrixSpectralRep
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    HasInfluenceMatrixSpectralRep (Aα K Rα) U wα s := by
  exact HasInfluenceMatrixSpectralRep.ofOrthogonalEq hRα.orthogonalU <|
    by simpa [Aα] using influenceMatrix_eq_spectralRep K U V Rα wα s hK hRα

/-- Helper for Proposition 7.8: subtracting the identity from a spectral
influence matrix subtracts `1` from each spectral weight in the same
orthogonal basis. -/
lemma sub_one_eq_orthogonalDiagonal_sub_one
    (A : Matrix n n ℝ)
    (hA : HasInfluenceMatrixSpectralRep A U wα s) :
    A - 1 = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1) * Uᵀ := by
  have hUUt : U * Uᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hA.orthogonal
  -- Rewrite the identity in the same orthogonal basis before subtracting diagonals.
  calc
    A - 1
        = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Uᵀ -
            U * Matrix.diagonal (fun _ : n ↦ (1 : ℝ)) * Uᵀ := by
              rw [hA.eq_spectralRep, ← hUUt]
              simp
    _ = U *
          ((Matrix.diagonal (fun i ↦ wα (s i ^ 2)) -
            Matrix.diagonal (fun _ : n ↦ (1 : ℝ))) *
            Uᵀ) := by
            simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
    _ = U * (Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1) * Uᵀ) := by
          rw [Matrix.diagonal_sub]
    _ = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1) * Uᵀ := by
          simp [Matrix.mul_assoc]

/-- Helper for Proposition 7.8: multiplying the residual factor `(A - 1)` by
`K` combines the filter deviation with the singular values. -/
lemma sub_one_mul_forward_eq_orthogonalDiagonal
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (A : Matrix n n ℝ)
    (hA : HasInfluenceMatrixSpectralRep A U wα s) :
    (A - 1) * K =
      U * Matrix.diagonal (fun i ↦ (wα (s i ^ 2) - 1) * s i) * Vᵀ := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hA.orthogonal
  -- Put both factors into the common orthogonal-diagonal form and cancel `Uᵀ * U`.
  calc
    (A - 1) * K
        = (U * Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1) * Uᵀ) *
            (U * Matrix.diagonal s * Vᵀ) := by
              rw [sub_one_eq_orthogonalDiagonal_sub_one (A := A) hA, hK]
    _ = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1) * (Uᵀ * U) *
          Matrix.diagonal s * Vᵀ := by
            simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1) *
          Matrix.diagonal s * Vᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i ↦ (wα (s i ^ 2) - 1) * s i) * Vᵀ := by
          simp [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

/-- Helper for Proposition 7.8: an orthogonal matrix preserves Euclidean norm
squares through `Matrix.toEuclideanLin`. -/
lemma orthogonalGroup_toEuclideanLin_norm_sq_eq
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hAtA : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := A)).mp hA
  -- Expand both norms into coordinate sums and cancel the middle orthogonal factor.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  calc
    ∑ i, (A *ᵥ x.ofLp) i ^ 2 = (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
          simp [dotProduct, pow_two]
    _ = x.ofLp ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ x.ofLp)) := by
          rw [Matrix.dotProduct_transpose_mulVec]
    _ = x.ofLp ⬝ᵥ x.ofLp := by
          simp [Matrix.mulVec_mulVec, hAtA]
    _ = ∑ i, x.ofLp i ^ 2 := by
          simp [dotProduct, pow_two]

/-- Backend bridge. For a symmetric influence matrix `A`, the expected
predictive risk rewrites from the generic transpose-mul variance term to the
source trace term `trace (A ^ 2)`. -/
theorem expectedPredictiveRisk_eq_bias_add_trace_sq_of_isSymm
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (A : Matrix n n ℝ)
    (hA : Matrix.IsSymm A) :
    expectedPredictiveRisk μ A (K.toEuclideanLin fTrue) η =
      predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) +
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (A ^ 2) := by
  -- Reuse the backend risk decomposition and only rewrite the symmetric variance term.
  calc
    expectedPredictiveRisk μ A (K.toEuclideanLin fTrue) η
        = predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) +
            (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (Aᵀ * A) := by
              simpa using
                expectedPredictiveRisk_eq_bias_add_trace_transpose_mul
                  hη A (K.toEuclideanLin fTrue)
    _ = predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) +
          (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (A ^ 2) := by
          rw [hA.eq]
          congr 1
          simp [pow_two]

/-- Backend bridge. For a symmetric influence matrix `A`, the expected residual
risk rewrites from the generic transpose-mul variance term to the source trace
term `trace ((A - 1) ^ 2)`. -/
theorem expectedResidualRisk_eq_bias_add_trace_sub_one_sq_of_isSymm
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (A : Matrix n n ℝ)
    (hA : Matrix.IsSymm A) :
    expectedResidualRisk μ A (K.toEuclideanLin fTrue) η =
      predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) +
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((A - 1) ^ 2) := by
  have hSubSymm : Matrix.IsSymm (A - 1) := by
    -- Symmetry is stable under subtracting the identity matrix.
    rw [Matrix.IsSymm]
    calc
      (A - 1)ᵀ = Aᵀ - (1 : Matrix n n ℝ)ᵀ := by simp
      _ = A - 1 := by rw [hA.eq]; simp
  -- Reuse the backend residual decomposition and rewrite the symmetric square term.
  calc
    expectedResidualRisk μ A (K.toEuclideanLin fTrue) η
        = predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) +
            (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((A - 1)ᵀ * (A - 1)) := by
              simpa using
                expectedResidualRisk_eq_bias_add_trace_transpose_mul
                  hη A (K.toEuclideanLin fTrue)
    _ = predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) +
          (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((A - 1) ^ 2) := by
          rw [hSubSymm.eq]
          congr 1
          simp [pow_two]

/-- Backend bridge for Proposition 7.8. Under the Chapter 7 SVD of `K` and the
influence-matrix spectral representation of `A`, the deterministic bias term
rewrites as the spectral sum in `(7.46)` and `(7.47)`. -/
theorem predictiveRisk_regularizedResidual_eq_spectralBias_of_spectralRep
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (A : Matrix n n ℝ)
    (hA : HasInfluenceMatrixSpectralRep A U wα s) :
    predictiveRisk (regularizedResidual A (K.toEuclideanLin fTrue)) =
      (1 / (Fintype.card n : ℝ)) *
        ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 * s i ^ 2 * (((Vᵀ).toEuclideanLin fTrue) i) ^ 2 := by
  have hVtV : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hV
  have hResidual :
      regularizedResidual A (K.toEuclideanLin fTrue) = ((A - 1) * K).toEuclideanLin fTrue := by
    -- Express the residual as the matrix product `(A - 1) * K` acting on `fTrue`.
    apply WithLp.ofLp_injective
    simp [regularizedResidual_eq, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]
  have hMul :
      (A - 1) * K =
        U * Matrix.diagonal (fun i ↦ (wα (s i ^ 2) - 1) * s i) * Vᵀ :=
    sub_one_mul_forward_eq_orthogonalDiagonal hK A hA
  let ξ : EuclideanSpace ℝ n := (Vᵀ).toEuclideanLin fTrue
  let d : n → ℝ := fun i ↦ (wα (s i ^ 2) - 1) * s i
  have hCompose :
      (U * Matrix.diagonal d * Vᵀ).toEuclideanLin fTrue =
        U.toEuclideanLin ((Matrix.diagonal d).toEuclideanLin ξ) := by
    -- Reassociate the matrix action instead of unfolding the final risk formula in place.
    apply WithLp.ofLp_injective
    simp [ξ, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hDiagNorm :
      ‖(Matrix.diagonal d).toEuclideanLin ξ‖ ^ 2 =
        ∑ i : n, (d i) ^ 2 * (ξ i) ^ 2 := by
    -- A diagonal matrix acts coordinatewise, so the norm square becomes a coordinate sum.
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change ((Matrix.diagonal d *ᵥ ξ.ofLp) i) ^ 2 = d i ^ 2 * ξ.ofLp i ^ 2
    rw [Matrix.mulVec_diagonal]
    ring_nf
  have hSum :
      ∑ i : n, (d i) ^ 2 * (ξ i) ^ 2 =
        ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 * s i ^ 2 * (((Vᵀ).toEuclideanLin fTrue) i) ^ 2 := by
    -- Expand the diagonal coefficient into the source bias expression.
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp [d, ξ]
    ring_nf
  -- Normalize the residual to orthogonal-diagonal form, drop the orthogonal factor, and read off
  -- the remaining diagonal coordinates.
  rw [predictiveRisk_def, hResidual, hMul, hCompose]
  rw [orthogonalGroup_toEuclideanLin_norm_sq_eq U hA.orthogonal
    ((Matrix.diagonal d).toEuclideanLin ξ)]
  rw [hDiagNorm, hSum]
  ring

/-- Backend bridge for Proposition 7.8. Under the Chapter 7 influence-matrix
spectral representation of `A`, the trace term `trace ((A - 1) ^ 2)` rewrites
as the sum of squared filter deviations. -/
theorem influenceMatrix_trace_sub_one_sq_of_spectralRep
    (A : Matrix n n ℝ)
    (hA : HasInfluenceMatrixSpectralRep A U wα s) :
    Matrix.trace ((A - 1) ^ 2) =
      ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 := by
  -- First rewrite `A - 1` in the common orthogonal basis, then square and trace that normal form.
  rw [sub_one_eq_orthogonalDiagonal_sub_one (A := A) hA]
  rw [orthogonalDiagonal_sq_eq (U := U) (d := fun i ↦ wα (s i ^ 2) - 1) hA.orthogonal]
  simpa using
    trace_orthogonalDiagonal_eq_sum (U := U)
      (fun i ↦ (wα (s i ^ 2) - 1) ^ 2) hA.orthogonal

/-- Proposition 7.8 `(7.46)`, first displayed equality. Under the Chapter 7 SVD
and filter-factor representation of `Rα`, the expected normalized squared
predictive error `pα` equals the common bias term plus the variance trace term
`trace ((Aα K Rα) ^ 2)`. -/
theorem expectedPredictiveRisk_pα_eq_bias_add_trace_sq
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    (∫ ω, predictiveRisk (pα K Rα fTrue η ω) ∂μ) =
      predictiveRisk (regularizedResidual (Aα K Rα) (K.toEuclideanLin fTrue)) +
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((Aα K Rα) ^ 2) := by
  rw [← expectedPredictiveRisk_Aα_eq_integral_pα]
  exact expectedPredictiveRisk_eq_bias_add_trace_sq_of_isSymm hη (Aα K Rα) <|
    influenceMatrix_isSymm_of_filterRep K U V Rα wα s hK hRα

/-- Proposition 7.8 `(7.47)`, first displayed equality. Under the Chapter 7 SVD
and filter-factor representation of `Rα`, the expected normalized squared
residual `rα` equals the common bias term plus the variance trace term
`trace ((Aα K Rα - 1) ^ 2)`. -/
theorem expectedResidualRisk_rα_eq_bias_add_trace_sub_one_sq
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    (∫ ω, predictiveRisk (rα K Rα fTrue η ω) ∂μ) =
      predictiveRisk (regularizedResidual (Aα K Rα) (K.toEuclideanLin fTrue)) +
        (σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace ((Aα K Rα - 1) ^ 2) := by
  rw [← expectedResidualRisk_Aα_eq_integral_rα]
  exact expectedResidualRisk_eq_bias_add_trace_sub_one_sq_of_isSymm hη (Aα K Rα) <|
    influenceMatrix_isSymm_of_filterRep K U V Rα wα s hK hRα

/-- Proposition 7.8 `(7.46)`, second displayed equality. Under the Chapter 7
SVD/filter-factor setup, the expected normalized squared predictive error `pα`
rewrites to the spectral sum formula printed in the source. -/
theorem expectedPredictiveRisk_pα_eq_spectralSum
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    (∫ ω, predictiveRisk (pα K Rα fTrue η ω) ∂μ) =
      (1 / (Fintype.card n : ℝ)) *
          ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 * s i ^ 2 * (((Vᵀ).toEuclideanLin fTrue) i) ^ 2 +
        (σ ^ 2 / (Fintype.card n : ℝ)) * ∑ i : n, (wα (s i ^ 2)) ^ 2 := by
  let hA : HasInfluenceMatrixSpectralRep (Aα K Rα) U wα s :=
    Aα_hasInfluenceMatrixSpectralRep hK hRα
  rw [expectedPredictiveRisk_pα_eq_bias_add_trace_sq hη hK hRα]
  rw [predictiveRisk_regularizedResidual_eq_spectralBias_of_spectralRep
    hRα.orthogonalV hK (Aα K Rα) hA]
  rw [influenceMatrix_trace_sq_of_spectralRep hA]

/-- Proposition 7.8 `(7.47)`, second displayed equality. Under the Chapter 7
SVD/filter-factor setup, the expected normalized squared residual `rα` rewrites
to the spectral sum formula printed in the source. -/
theorem expectedResidualRisk_rα_eq_spectralSum
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    (∫ ω, predictiveRisk (rα K Rα fTrue η ω) ∂μ) =
      (1 / (Fintype.card n : ℝ)) *
          ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 * s i ^ 2 * (((Vᵀ).toEuclideanLin fTrue) i) ^ 2 +
        (σ ^ 2 / (Fintype.card n : ℝ)) * ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 := by
  let hA : HasInfluenceMatrixSpectralRep (Aα K Rα) U wα s :=
    Aα_hasInfluenceMatrixSpectralRep hK hRα
  rw [expectedResidualRisk_rα_eq_bias_add_trace_sub_one_sq hη hK hRα]
  rw [predictiveRisk_regularizedResidual_eq_spectralBias_of_spectralRep
    hRα.orthogonalV hK (Aα K Rα) hA]
  rw [influenceMatrix_trace_sub_one_sq_of_spectralRep (Aα K Rα) hA]

end

end FilterRegularization

end
