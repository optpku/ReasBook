/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped Matrix MatrixOrder

namespace Matrix

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Exercise 3.6. For an SPD matrix `M` with an orthogonal eigendecomposition
`M = V * Matrix.diagonal eigvals * Vᵀ`, the textbook diagonal square-root expression
agrees with the canonical matrix square root `CFC.sqrt M`. -/
theorem cfcSqrt_eq_orthogonalDiagonalization
    (M V : Matrix n n ℝ) (eigvals : n → ℝ) (hspd : M.PosDef)
    (hdiag : M = V * diagonal eigvals * Vᵀ) (hV : Vᵀ * V = 1) :
    CFC.sqrt M = V * diagonal (fun i ↦ Real.sqrt (eigvals i)) * Vᵀ := by
  let S := V * diagonal (fun i ↦ Real.sqrt (eigvals i)) * Vᵀ
  -- The orthogonality relation gives the inverse needed to transport positivity.
  have hV_unit : IsUnit V := IsUnit.of_mul_eq_one_right Vᵀ hV
  -- Pull the positive-semidefinite structure back to the diagonal factor.
  have hdiag_psd : (V * diagonal eigvals * Vᵀ).PosSemidef := by
    simpa [hdiag] using hspd.posSemidef
  have hdiag_diag_psd : (diagonal eigvals).PosSemidef := by
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (U := V) (x := diagonal eigvals) hV_unit).1 <|
      by simpa [Matrix.star_eq_conjTranspose] using hdiag_psd
  -- Each diagonal entry is an eigenvalue, so positivity of the diagonal matrix
  -- gives `eigvals i ≥ 0`.
  have heig_nonneg : ∀ i, 0 ≤ eigvals i := by
    intro i
    simpa using hdiag_diag_psd.diag_nonneg (i := i)
  -- The candidate square root is nonnegative because it is an orthogonal
  -- conjugate of a nonnegative diagonal matrix.
  have hS_psd : S.PosSemidef := by
    exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (U := V) (x := diagonal (fun i ↦ Real.sqrt (eigvals i))) hV_unit).2 <|
      by
        refine Matrix.PosSemidef.diagonal ?_
        intro i
        exact Real.sqrt_nonneg (eigvals i)
  have hS_nonneg : 0 ≤ S := hS_psd.nonneg
  -- Squaring the diagonal square root reduces entrywise to `Real.sq_sqrt`.
  have hdiag_sqrt_sq :
      diagonal (fun i ↦ Real.sqrt (eigvals i)) * diagonal (fun i ↦ Real.sqrt (eigvals i)) =
        diagonal eigvals := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [heig_nonneg]
    · simp [hij]
  -- Expand the square once, collapse the middle factor with `Vᵀ * V = 1`, and recover `M`.
  have hS_sq : S * S = M := by
    calc
      S * S
          = V * diagonal (fun i ↦ Real.sqrt (eigvals i)) * (Vᵀ * V) *
              diagonal (fun i ↦ Real.sqrt (eigvals i)) * Vᵀ := by
              simp [S, Matrix.mul_assoc]
      _ = V * diagonal (fun i ↦ Real.sqrt (eigvals i)) *
            diagonal (fun i ↦ Real.sqrt (eigvals i)) * Vᵀ := by
            simp [hV, Matrix.mul_assoc]
      _ = V * diagonal eigvals * Vᵀ := by
            simpa [Matrix.mul_assoc] using congrArg (fun X ↦ V * X * Vᵀ) hdiag_sqrt_sq
      _ = M := hdiag.symm
  -- The CFC square root is characterized by being the unique nonnegative square root.
  simpa [S] using (CFC.sqrt_eq_iff M S hspd.posSemidef.nonneg hS_nonneg).2 hS_sq

/-- Exercise 3.6. If an SPD matrix `M` admits an eigendecomposition
`M = V * Matrix.diagonal eigvals * Vᵀ` with `Vᵀ * V = 1`, then the textbook
diagonal square-root expression squares to `M`. This is the source-facing
specialization of the canonical square law `CFC.sqrt_mul_sqrt_self`. -/
theorem orthogonalDiagonalSqrtSq
    (M V : Matrix n n ℝ) (eigvals : n → ℝ) (hspd : M.PosDef)
    (hdiag : M = V * diagonal eigvals * Vᵀ) (hV : Vᵀ * V = 1) :
    (V * diagonal (fun i ↦ Real.sqrt (eigvals i)) * Vᵀ) ^ 2 = M := by
  rw [← cfcSqrt_eq_orthogonalDiagonalization M V eigvals hspd hdiag hV]
  simpa [pow_two] using (CFC.sqrt_mul_sqrt_self M : CFC.sqrt M * CFC.sqrt M = M)

/-- Canonical orthogonal-group version of `orthogonalDiagonalSqrtSq`. -/
theorem orthogonalDiagonalSqrtSq_of_mem_orthogonalGroup
    (M V : Matrix n n ℝ) (eigvals : n → ℝ) (hspd : M.PosDef)
    (hdiag : M = V * diagonal eigvals * Vᵀ) (hV : V ∈ orthogonalGroup n ℝ) :
    (V * diagonal (fun i ↦ Real.sqrt (eigvals i)) * Vᵀ) ^ 2 = M := by
  have hV' : Vᵀ * V = 1 := Iff.mp (mem_orthogonalGroup_iff' n ℝ) hV
  exact orthogonalDiagonalSqrtSq M V eigvals hspd hdiag hV'

end

end Matrix
