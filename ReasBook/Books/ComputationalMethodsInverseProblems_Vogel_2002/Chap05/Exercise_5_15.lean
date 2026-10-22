/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

public section

open WithLp (toLp)
open scoped Matrix
open scoped Matrix.Norms.Frobenius

universe u v w

namespace Matrix

/-- Left multiplication by a bundled unitary matrix preserves the Frobenius norm. -/
theorem frobenius_norm_mul_eq_of_unitary
    {n : Type u} {m : Type v} {𝕜 : Type w}
    [Fintype n] [DecidableEq n] [Fintype m] [RCLike 𝕜]
    (U : Matrix.unitaryGroup n 𝕜) (A : Matrix n m 𝕜) :
    ‖(U : Matrix n n 𝕜) * A‖ = ‖A‖ := by
  have hsum :
      ∑ i, ∑ j, ‖((U : Matrix n n 𝕜) * A) i j‖ ^ (2 : ℝ) =
        ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    calc
      ∑ i : n, ∑ j : m, ‖((U : Matrix n n 𝕜) * A) i j‖ ^ (2 : ℝ)
          = ∑ j : m, ∑ i : n, ‖((U : Matrix n n 𝕜) * A) i j‖ ^ (2 : ℝ) := by
              simpa using
                (Finset.sum_comm :
                  (∑ i : n, ∑ j : m, ‖((U : Matrix n n 𝕜) * A) i j‖ ^ (2 : ℝ)) =
                    ∑ j : m, ∑ i : n, ‖((U : Matrix n n 𝕜) * A) i j‖ ^ (2 : ℝ))
      _ = ∑ j : m, ∑ i : n, ‖A i j‖ ^ (2 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            have hUnitary :
                ((Matrix.toEuclideanCLM :
                    Matrix n n 𝕜 ≃⋆ₐ[𝕜]
                      (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n))
                  (U : Matrix n n 𝕜)) ∈
                  unitary (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) := by
              exact Unitary.map_mem
                (Matrix.toEuclideanCLM :
                  Matrix n n 𝕜 ≃⋆ₐ[𝕜]
                    (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n))
                U.2
            have hmul_col :
                (U : Matrix n n 𝕜) *ᵥ A.col j = ((U : Matrix n n 𝕜) * A).col j := by
              ext i
              simp [Matrix.mulVec, Matrix.col_apply, Matrix.mul_apply, dotProduct]
            have hcol :
                ‖toLp 2 (((U : Matrix n n 𝕜) * A).col j)‖ = ‖toLp 2 (A.col j)‖ := by
              simpa [hmul_col] using
                ContinuousLinearMap.norm_map_of_mem_unitary hUnitary (toLp 2 (A.col j))
            have hsq : ‖toLp 2 (((U : Matrix n n 𝕜) * A).col j)‖ ^ 2 = ‖toLp 2 (A.col j)‖ ^ 2 := by
              exact congrArg (fun x : ℝ ↦ x ^ (2 : ℕ)) hcol
            simpa [PiLp.norm_sq_eq_of_L2, Matrix.col_apply, Real.rpow_natCast] using hsq
      _ = ∑ i : n, ∑ j : m, ‖A i j‖ ^ (2 : ℝ) := by
            simpa using
              (Finset.sum_comm : (∑ j : m, ∑ i : n, ‖A i j‖ ^ (2 : ℝ)) =
                ∑ i : n, ∑ j : m, ‖A i j‖ ^ (2 : ℝ))
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def, hsum]

/-- Exercise 5.15. If `U` is a unitary matrix, then left multiplication by `U`
preserves the Frobenius norm: `‖U * A‖ = ‖A‖`. -/
theorem frobenius_norm_mul_eq_of_mem_unitary
    {n : Type u} {m : Type v} {𝕜 : Type w}
    [Fintype n] [DecidableEq n] [Fintype m] [RCLike 𝕜]
    {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) (A : Matrix n m 𝕜) :
    ‖U * A‖ = ‖A‖ := by
  simpa using frobenius_norm_mul_eq_of_unitary ⟨U, hU⟩ A

end Matrix
