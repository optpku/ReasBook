/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Remark_4_33.LeastSquares
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Theorem_4_32

public section

noncomputable section

open scoped Matrix

namespace LinearGaussian

universe u v

section

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- Helper for Remark 4.33: the inverse of the isotropic covariance matrix
`(σ ^ 2) • 1` is the reciprocal scalar multiple of the identity. -/
private lemma scalarIdentityInverse (σ : ℝ) (hσ : σ ≠ 0) :
    ((σ ^ 2) • (1 : Matrix m m ℝ))⁻¹ = (σ ^ 2)⁻¹ • (1 : Matrix m m ℝ) := by
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  -- Introduce the scalar inverse once so `Matrix.inv_smul` applies to the identity matrix.
  letI : Invertible (σ ^ 2) := invertibleOfNonzero hσ_sq_ne
  simpa using
    (Matrix.inv_smul (A := (1 : Matrix m m ℝ)) (k := σ ^ 2) (h := by simp))

omit [Fintype n] [DecidableEq n] in
/-- Helper for Remark 4.33: after inverting the isotropic covariance, the weighted
Gramian becomes a scalar multiple of `Kᵀ * K`. -/
private lemma scaledGramian_eq_smul_gramian (K : Matrix m n ℝ) (σ : ℝ) :
    Kᵀ * ((σ ^ 2)⁻¹ • (1 : Matrix m m ℝ)) * K =
      (σ ^ 2)⁻¹ • (Kᵀ * K) := by
  -- Push the scalar through the two matrix products until only the Gramian remains.
  simp

omit [DecidableEq m] in
/-- Helper for Remark 4.33: scaling `Kᵀ * K` by the nonzero scalar `(σ ^ 2)⁻¹`
does not change whether its determinant is a unit. -/
private lemma scaledGramianDetIsUnitIff (K : Matrix m n ℝ) (σ : ℝ) (hσ : σ ≠ 0) :
    IsUnit (((σ ^ 2)⁻¹ • (Kᵀ * K)).det) ↔ IsUnit ((Kᵀ * K).det) := by
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hScalarUnit : IsUnit (((σ ^ 2)⁻¹) ^ Fintype.card n) := by
    exact IsUnit.pow _ (inv_ne_zero hσ_sq_ne).isUnit
  -- Rewrite the determinant of the scalar multiple and cancel the unit scalar factor.
  rw [Matrix.det_smul]
  simpa [mul_comm] using
    (Units.isUnit_units_mul hScalarUnit.unit ((Kᵀ * K).det))

/-- Remark 4.33. If `C_N = σ^2 • 1` with `σ ≠ 0`, then the Gauss-Markov
operator from Theorem 4.32 reduces to the ordinary least-squares operator
`(Kᵀ * K)⁻¹ * Kᵀ`. -/
theorem gaussMarkovOperator_scalar_eq_ordinaryOperator
    (K : Matrix m n ℝ) (σ : ℝ) (hσ : σ ≠ 0) :
    gaussMarkovOperator K ((σ ^ 2) • (1 : Matrix m m ℝ)) =
      LeastSquares.ordinaryOperator K := by
  have hσ_sq_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  -- Rewrite both operators into their matrix formulas and normalize the scalar covariance inverse.
  rw [LinearGaussian.gaussMarkovOperator_def, LeastSquares.ordinaryOperator_def]
  rw [scalarIdentityInverse (m := m) σ hσ, scaledGramian_eq_smul_gramian K σ]
  by_cases hGramUnit : IsUnit ((Kᵀ * K).det)
  · have hScaledInv :
        ((σ ^ 2)⁻¹ • (Kᵀ * K))⁻¹ = (σ ^ 2) • (Kᵀ * K)⁻¹ := by
      -- Pull the scalar factor out of the inverse in the invertible Gramian branch.
      letI : Invertible ((σ ^ 2)⁻¹) := invertibleOfNonzero (inv_ne_zero hσ_sq_ne)
      simpa [hσ_sq_ne] using
        (Matrix.inv_smul (A := (Kᵀ * K)) (k := (σ ^ 2)⁻¹) (h := hGramUnit))
    rw [hScaledInv]
    -- Cancel the scalar factor against the inverted covariance on the right.
    simp [smul_smul, hσ_sq_ne]
  · have hScaledNotUnit : ¬ IsUnit (((σ ^ 2)⁻¹ • (Kᵀ * K)).det) := by
      exact mt (scaledGramianDetIsUnitIff K σ hσ).mp hGramUnit
    -- In the singular branch both nonsingular inverses are definitionally zero.
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hScaledNotUnit,
      Matrix.nonsing_inv_apply_not_isUnit _ hGramUnit]
    simp

/-- Observation-level form of
`LinearGaussian.gaussMarkovOperator_scalar_eq_ordinaryOperator`. -/
theorem apply_gaussMarkovOperator_scalar_eq_ordinarySolution
    (K : Matrix m n ℝ) (z : EuclideanSpace ℝ m) (σ : ℝ) (hσ : σ ≠ 0) :
    Matrix.toEuclideanLin (gaussMarkovOperator K ((σ ^ 2) • (1 : Matrix m m ℝ))) z =
      LeastSquares.ordinarySolution K z := by
  -- First identify the two operator matrices, then apply both sides to the observation vector.
  rw [LeastSquares.ordinarySolution_eq]
  simpa using congrArg (fun A ↦ Matrix.toEuclideanLin A z)
    (gaussMarkovOperator_scalar_eq_ordinaryOperator K σ hσ)

end

end LinearGaussian

/- Remark 4.33 uses the current Chapter 4 BLUE owner
`ProbabilityTheory.IsBestLinearUnbiasedEstimator` and the Gauss-Markov theorem
`ProbabilityTheory.isBestLinearUnbiasedEstimator_gaussMarkov`, while the
deterministic comparison problem is owned by the following least-squares
declarations together with the Chapter 3 energy norm `Matrix.energyNorm`. -/

#check ProbabilityTheory.IsBestLinearUnbiasedEstimator
#check ProbabilityTheory.isBestLinearUnbiasedEstimator_gaussMarkov
#check Matrix.energyNorm
#check LeastSquares.weightedResidualObjective
#check LeastSquares.IsWeightedLeastSquaresSolution
#check LeastSquares.ordinaryOperator
#check LeastSquares.ordinarySolution
