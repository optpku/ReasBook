/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius

universe u v

private lemma toEuclideanLin_apply_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ ≤ ‖A‖ * ‖x‖ := by
  have hmulVec :
      ‖replicateCol (Fin 1) (A.mulVec x.ofLp)‖ = ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ :=
    frobenius_norm_replicateCol (ι := Fin 1) (v := A.mulVec x.ofLp)
  have hx :
      ‖replicateCol (Fin 1) x.ofLp‖ = ‖WithLp.toLp 2 x.ofLp‖ :=
    frobenius_norm_replicateCol (ι := Fin 1) (v := x.ofLp)
  calc
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ = ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ := by
      change ‖A.toEuclideanLin x‖ = _
      rfl
    _ = ‖replicateCol (Fin 1) (A.mulVec x.ofLp)‖ := by
      symm
      exact hmulVec
    _ = ‖A * replicateCol (Fin 1) x.ofLp‖ := by
      rw [← replicateCol_mulVec]
    _ ≤ ‖A‖ * ‖replicateCol (Fin 1) x.ofLp‖ := frobenius_norm_mul A _
    _ = ‖A‖ * ‖WithLp.toLp 2 x.ofLp‖ := by
      rw [hx]
    _ = ‖A‖ * ‖x‖ := by
      rfl

namespace Matrix

/-- The continuous linear map induced by a matrix on Euclidean space has operator norm bounded by
its Frobenius norm. -/
theorem toEuclideanLin_opNorm_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
      A.toEuclideanLin.toContinuousLinearMap (norm_nonneg A) fun x ↦ ?_
  simpa using toEuclideanLin_apply_le_frobenius_norm A x

end Matrix

/-- Example 2.19: the operator norm of the continuous linear map induced by a matrix is bounded by
its Frobenius norm. -/
theorem matrix_operator_norm_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖A‖ :=
  Matrix.toEuclideanLin_opNorm_le_frobenius_norm A
