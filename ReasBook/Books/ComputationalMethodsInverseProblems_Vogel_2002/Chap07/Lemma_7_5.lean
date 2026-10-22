/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5.SpectralRepresentation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

noncomputable section

open scoped BigOperators Matrix

/-!
The item-owned foundation module
`Book.Ch7.Lemma_7_5.SpectralRepresentation` records the exact Chapter 7 matrix
representations `(7.36)` and `(7.39)` as reusable source-faithful owners.
This file keeps the labeled consequences from Lemma 7.5 itself.
-/

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Lemma 7.5: the trace of an orthogonal conjugate of a diagonal
matrix is the sum of its diagonal entries. -/
lemma trace_orthogonalDiagonal_eq_sum
    {U : Matrix n n ℝ} (d : n → ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    Matrix.trace (U * Matrix.diagonal d * Uᵀ) = ∑ i, d i := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hU
  -- Cycle the trace so the orthogonal factor collapses to the identity.
  calc
    Matrix.trace (U * Matrix.diagonal d * Uᵀ)
        = Matrix.trace (Uᵀ * U * Matrix.diagonal d) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle U (Matrix.diagonal d) Uᵀ)
    _ = Matrix.trace (Matrix.diagonal d) := by
          rw [hUtU]
          simp
    _ = ∑ i, d i := Matrix.trace_diagonal d

/-- Helper for Lemma 7.5: squaring an orthogonal conjugate of a diagonal matrix
keeps the same orthogonal basis and squares the diagonal entries. -/
lemma orthogonalDiagonal_sq_eq
    {U : Matrix n n ℝ} (d : n → ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ) :
    (U * Matrix.diagonal d * Uᵀ) ^ 2 =
      U * Matrix.diagonal (fun i ↦ d i ^ 2) * Uᵀ := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hU
  -- Expand the square once and cancel the orthogonal middle factor.
  calc
    (U * Matrix.diagonal d * Uᵀ) ^ 2
        = (U * Matrix.diagonal d * Uᵀ) * (U * Matrix.diagonal d * Uᵀ) := by
            rw [pow_two]
    _ = U * (Matrix.diagonal d * (Uᵀ * U) * Matrix.diagonal d) * Uᵀ := by
          simp [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal d * Matrix.diagonal d) * Uᵀ := by
          rw [hUtU]
          simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i ↦ d i ^ 2) * Uᵀ := by
          rw [Matrix.diagonal_mul_diagonal]
          simp [Matrix.mul_assoc, pow_two]

/-- Helper for Lemma 7.5: the matrix `Rᵀ * R` of a biorthogonal diagonal
factorization is an orthogonal conjugate with squared diagonal coefficients. -/
lemma transposeMul_biorthogonalDiagonal_eq
    {U V : Matrix n n ℝ} (c : n → ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ) :
    (V * Matrix.diagonal c * Uᵀ)ᵀ * (V * Matrix.diagonal c * Uᵀ) =
      U * Matrix.diagonal (fun i ↦ c i ^ 2) * Uᵀ := by
  have hVtV : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hV
  -- Rewrite the transpose once, then cancel the orthogonal factor on the left basis.
  calc
    (V * Matrix.diagonal c * Uᵀ)ᵀ * (V * Matrix.diagonal c * Uᵀ)
        = (U * Matrix.diagonal c * Vᵀ) * (V * Matrix.diagonal c * Uᵀ) := by
            simp [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = U * (Matrix.diagonal c * (Vᵀ * V) * Matrix.diagonal c) * Uᵀ := by
          simp [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal c * Matrix.diagonal c) * Uᵀ := by
          rw [hVtV]
          simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i ↦ c i ^ 2) * Uᵀ := by
          rw [Matrix.diagonal_mul_diagonal]
          simp [Matrix.mul_assoc, pow_two]

/-- Lemma 7.5 (1). If the influence matrix `Aα` has the Chapter 7 spectral
representation from `(7.39)`, then `Aα` is symmetric. -/
theorem influenceMatrix_isSymm_of_spectralRep
    {Aα U : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
    (hAα : HasInfluenceMatrixSpectralRep Aα U wα s) :
    Matrix.IsSymm Aα := by
  -- Expand the stored spectral representation and transpose it directly.
  rw [Matrix.IsSymm, hAα.eq_spectralRep]
  simp [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- Lemma 7.5 (2). Under the Chapter 7 spectral representation from `(7.39)`,
the trace of `Aα` is `∑ i, wα (s i ^ 2)`. -/
theorem influenceMatrix_trace_of_spectralRep
    {Aα U : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
    (hAα : HasInfluenceMatrixSpectralRep Aα U wα s) :
    Matrix.trace Aα = ∑ i, wα (s i ^ 2) := by
  -- Reduce the trace to the diagonal entries in the orthogonal basis from `(7.39)`.
  rw [hAα.eq_spectralRep]
  simpa using
    trace_orthogonalDiagonal_eq_sum (U := U) (fun i ↦ wα (s i ^ 2)) hAα.orthogonal

/-- Lemma 7.5 (3). Under the Chapter 7 spectral representation from `(7.39)`,
`trace (Aαᵀ * Aα) = trace (Aα ^ 2)`. Over `ℝ`, this is the source formula
`trace (Aα^* * Aα) = trace (Aα ^ 2)`. -/
theorem influenceMatrix_trace_transpose_mul_eq_trace_sq_of_spectralRep
    {Aα U : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
    (hAα : HasInfluenceMatrixSpectralRep Aα U wα s) :
    Matrix.trace (Aαᵀ * Aα) = Matrix.trace (Aα ^ 2) := by
  have hsymm : Matrix.IsSymm Aα :=
    influenceMatrix_isSymm_of_spectralRep hAα
  -- Symmetry identifies `Aαᵀ` with `Aα`, after which the product is exactly `Aα ^ 2`.
  calc
    Matrix.trace (Aαᵀ * Aα) = Matrix.trace (Aα * Aα) := by
      rw [hsymm.eq]
    _ = Matrix.trace (Aα ^ 2) := by
      rw [pow_two]

/-- Lemma 7.5 (4). Under the Chapter 7 spectral representation from `(7.39)`,
`trace (Aα ^ 2) = ∑ i, (wα (s i ^ 2)) ^ 2`. -/
theorem influenceMatrix_trace_sq_of_spectralRep
    {Aα U : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
    (hAα : HasInfluenceMatrixSpectralRep Aα U wα s) :
    Matrix.trace (Aα ^ 2) = ∑ i, (wα (s i ^ 2)) ^ 2 := by
  -- Normalize the square to the same orthogonal basis with squared diagonal weights.
  rw [hAα.eq_spectralRep, orthogonalDiagonal_sq_eq (U := U) (hU := hAα.orthogonal)]
  simpa using
    trace_orthogonalDiagonal_eq_sum (U := U) (fun i ↦ (wα (s i ^ 2)) ^ 2) hAα.orthogonal

/-- Lemma 7.5 (5). If the reconstruction operator `Rα` has the Chapter 7
representation from `(7.36)`, then
`trace (Rαᵀ * Rα) = ∑ i, (wα (s i ^ 2)) ^ 2 / (s i ^ 2)`. Over `ℝ`, this is the
source formula `trace (Rα^* * Rα) = ∑ i, (wα (s i ^ 2)) ^ 2 / (s i ^ 2)`. -/
theorem reconstruction_trace_transpose_mul_of_spectralRep
    {Rα U V : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    Matrix.trace (Rαᵀ * Rα) = ∑ i, (wα (s i ^ 2)) ^ 2 / (s i ^ 2) := by
  -- Rewrite `Rαᵀ * Rα` to the orthogonal diagonal form coming from `(7.36)`.
  rw [hRα.eq_spectralRep,
    transposeMul_biorthogonalDiagonal_eq (U := U) (V := V)
      (c := fun i ↦ wα (s i ^ 2) / s i) hRα.orthogonalV]
  calc
    Matrix.trace
        (U * Matrix.diagonal (fun i ↦ (wα (s i ^ 2) / s i) ^ 2) * Uᵀ)
        = ∑ i, (wα (s i ^ 2) / s i) ^ 2 := by
            simpa using
              trace_orthogonalDiagonal_eq_sum (U := U)
                (fun i ↦ (wα (s i ^ 2) / s i) ^ 2) hRα.orthogonalU
    _ = ∑ i, (wα (s i ^ 2)) ^ 2 / (s i ^ 2) := by
          -- Normalize each scalar square quotient to the source expression.
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [div_pow]

end
