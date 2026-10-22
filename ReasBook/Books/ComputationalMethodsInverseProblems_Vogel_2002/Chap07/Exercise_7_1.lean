/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5

public section

open scoped Matrix

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Helper for Exercise 7.1: multiplying a singular value by its filter quotient
recovers the filter weight, with `wα 0 = 0` handling the zero singular-value
case. -/
lemma singularValueMul_filterQuotient_eq_weight
    (wα : ℝ → ℝ) (s : n → ℝ) (hw0 : wα 0 = 0) :
    ∀ i, s i * (wα (s i ^ 2) / s i) = wα (s i ^ 2) := by
  intro i
  -- Split on the singular value so the zero-denominator case is handled by `hw0`.
  by_cases hs : s i = 0
  · simp [hs, hw0]
  · simpa using (mul_div_cancel₀ (a := wα (s i ^ 2)) (b := s i) hs)

/-- Helper for Exercise 7.1: the product of the two diagonal factors in the
filter representation collapses to the spectral weight diagonal. -/
lemma singularValueDiagonal_mul_filterDiagonal_eq
    (wα : ℝ → ℝ) (s : n → ℝ) (hw0 : wα 0 = 0) :
    Matrix.diagonal s * Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) =
      Matrix.diagonal (fun i ↦ wα (s i ^ 2)) := by
  -- Rewrite the diagonal product entrywise using the scalar quotient identity.
  simpa [Matrix.diagonal_mul_diagonal] using
    congrArg Matrix.diagonal
      (funext (singularValueMul_filterQuotient_eq_weight wα s hw0))

/-- Exercise 7.1 (1). If `K = U * Matrix.diagonal s * Vᵀ` and `Rα` has the
Chapter 7 reconstruction spectral representation `(7.36)`,
then `influenceMatrix K Rα = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Uᵀ`. -/
theorem influenceMatrix_eq_spectralRep
    (K U V Rα : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    influenceMatrix K Rα = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Uᵀ := by
  have hVtV : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hRα.orthogonalV
  -- Expand `Aα = K * Rα` and reassociate so the orthogonal cancellation is explicit.
  calc
    influenceMatrix K Rα
        = U * Matrix.diagonal s * (Vᵀ * V) *
            Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) * Uᵀ := by
          rw [influenceMatrix_def, hK, hRα.eq_spectralRep]
          simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal s * Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) * Uᵀ := by
          -- Use orthogonality of `V` to collapse the middle factor to the identity.
          rw [hVtV]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Uᵀ := by
          -- Collapse the remaining diagonal product via the scalar filter identity.
          simpa [Matrix.mul_assoc] using
            congrArg (fun M ↦ U * M * Uᵀ)
              (singularValueDiagonal_mul_filterDiagonal_eq wα s hRα.filter_zero)

/-- Exercise 7.1 (2). Under the same SVD and filter-representation hypotheses,
`influenceMatrix K Rα` is symmetric. -/
theorem influenceMatrix_isSymm_of_filterRep
    (K U V Rα : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    Matrix.IsSymm (influenceMatrix K Rα) :=
  -- Reuse the spectral-representation symmetry theorem after computing `Aα`.
  influenceMatrix_isSymm_of_spectralRep <|
    HasInfluenceMatrixSpectralRep.ofOrthogonalEq hRα.orthogonalU
      (influenceMatrix_eq_spectralRep K U V Rα wα s hK hRα)

end
