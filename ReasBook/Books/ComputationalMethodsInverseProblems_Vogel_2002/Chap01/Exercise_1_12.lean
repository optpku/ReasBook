/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_12.Operator

public section

noncomputable section

open scoped Matrix

namespace Tikhonov

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Exercise 1.12. For an orthogonal SVD `K = U * Matrix.diagonal s * Vᵀ` and
positive regularization parameter `α`, the operator representation
`((Kᵀ * K + α • 1)⁻¹ * Kᵀ) d` agrees with the Tikhonov filter representation
with diagonal entries `s i / (s i ^ 2 + α)`. -/
theorem exercise_1_12
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ) (d : EuclideanSpace ℝ n)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    Matrix.toEuclideanLin (operator K α) d =
      Matrix.toEuclideanLin
        (V * Matrix.diagonal (fun i ↦ s i / (s i ^ 2 + α)) * Uᵀ) d := by
  -- Reuse the imported operator/SVD identity and only normalize the diagonal coefficient.
  simpa [filterScalar_eq_ratio] using
    operator_apply_eq_svdFilter K U V s α d hα_pos hU hV hK

/-- Companion API for `exercise_1_12` under its descriptive theorem name. -/
theorem operatorRepresentation_eq_filterRepresentation
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ) (d : EuclideanSpace ℝ n)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    Matrix.toEuclideanLin (operator K α) d =
      Matrix.toEuclideanLin
        (V * Matrix.diagonal (fun i ↦ s i / (s i ^ 2 + α)) * Uᵀ) d := by
  -- The descriptive companion theorem is exactly the main exercise statement.
  exact exercise_1_12 K U V s α d hα_pos hU hV hK

end Tikhonov
