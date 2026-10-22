/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.44: the textbook adjoint transformation of a linear map between finite-dimensional
real inner product spaces is the canonical mathlib construction `LinearMap.adjoint`. -/
recall LinearMap.adjoint

section

variable {V : Type u} {E : Type v}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: this is exactly `LinearMap.adjoint_inner_left` with the two sides swapped into the
-- textbook order.
/-- The adjoint transformation satisfies the defining inner-product relation. -/
theorem adjoint_transformation_inner_eq (A : V →ₗ[ℝ] E) (x : V) (y : E) :
    inner ℝ y (A x) = inner ℝ (A.adjoint y) x := by
  simpa using (A.adjoint_inner_left x y).symm

end

section

variable {m n : ℕ}

-- Proof sketch: specialize `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` to real matrices and
-- simplify `conjTranspose` to `transpose`.
/-- For a real matrix acting on Euclidean spaces, the adjoint linear map is represented by the
transpose matrix. -/
theorem matrix_transpose_toEuclideanLin_eq_adjoint (A : Matrix (Fin m) (Fin n) ℝ) :
    A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
  simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

end
