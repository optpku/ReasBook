/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import Mathlib
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Hermitian

open Matrix

noncomputable section

@[expose] public section

variable {m n : ℕ}

/-- The real square matrices indexed by `Fin n` used for Chapter 7 regularized normal
matrices. -/
abbrev MatrixN (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The real Jacobian matrices with `m` residual rows and `n` variable columns. -/
abbrev JacobianMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The regularized normal matrix `J(x)ᵀ J(x) + μ • D(x)` from `(7.3.27)`. -/
def levenbergMarquardtRegularizedNormalMatrix
    (J : JacobianMatrix m n) (D : MatrixN n) (μ : ℝ) : MatrixN n :=
  Jᵀ * J + μ • D

/-- The source damping matrix `diag (diag (J(x)ᵀ * J(x)))` from `(7.3.27)`. -/
def levenbergMarquardtSourceDampingMatrix
    (J : JacobianMatrix m n) : MatrixN n :=
  Matrix.diagonal (fun i : Fin n ↦ (Jᵀ * J) i i)

/-- The source Levenberg-Marquardt family `J(x)ᵀ * J(x) + μ • diag (diag (J(x)ᵀ * J(x)))`
from `(7.3.27)`. -/
def sourceLevenbergMarquardtRegularizedNormalMatrix
    (J : JacobianMatrix m n) (μ : ℝ) : MatrixN n :=
  levenbergMarquardtRegularizedNormalMatrix J
    (levenbergMarquardtSourceDampingMatrix J) μ

/-- Expand the regularized normal matrix `Jᵀ * J + μ • D`. -/
@[simp] theorem levenbergMarquardtRegularizedNormalMatrix_eq
    (J : JacobianMatrix m n) (D : MatrixN n) (μ : ℝ) :
    levenbergMarquardtRegularizedNormalMatrix J D μ = Jᵀ * J + μ • D :=
  rfl

/-- Expand the source damping matrix `diag (diag (Jᵀ * J))`. -/
@[simp] theorem levenbergMarquardtSourceDampingMatrix_eq
    (J : JacobianMatrix m n) :
    levenbergMarquardtSourceDampingMatrix J =
      Matrix.diagonal (fun i : Fin n ↦ (Jᵀ * J) i i) :=
  rfl

/-- The source damping matrix reads off the diagonal of `Jᵀ * J` on the diagonal. -/
@[simp] theorem levenbergMarquardtSourceDampingMatrix_apply_diag
    (J : JacobianMatrix m n) (i : Fin n) :
    levenbergMarquardtSourceDampingMatrix J i i = (Jᵀ * J) i i := by
  simp [levenbergMarquardtSourceDampingMatrix_eq]

/-- The source damping matrix vanishes off the diagonal. -/
@[simp] theorem levenbergMarquardtSourceDampingMatrix_apply_offDiag
    (J : JacobianMatrix m n) {i j : Fin n} (hij : i ≠ j) :
    levenbergMarquardtSourceDampingMatrix J i j = 0 := by
  simp [levenbergMarquardtSourceDampingMatrix_eq, hij]

/-- Expand the source Levenberg-Marquardt matrix into the explicit source spelling. -/
@[simp] theorem sourceLevenbergMarquardtRegularizedNormalMatrix_eq
    (J : JacobianMatrix m n) (μ : ℝ) :
    sourceLevenbergMarquardtRegularizedNormalMatrix J μ =
      Jᵀ * J + μ • levenbergMarquardtSourceDampingMatrix J :=
  rfl

/-- A real square matrix is a positive definite diagonal damping matrix in the source sense when
it is `Matrix.diagonal d` for some strictly positive diagonal entries `d`. -/
def IsPositiveDefiniteDiagonalMatrix (M : MatrixN n) : Prop :=
  ∃ d : Fin n → ℝ, M = Matrix.diagonal d ∧ ∀ i : Fin n, 0 < d i

/-- A positive definite diagonal matrix in the source sense is Hermitian. -/
theorem IsPositiveDefiniteDiagonalMatrix.isHermitian {M : MatrixN n}
    (hM : IsPositiveDefiniteDiagonalMatrix M) :
    M.IsHermitian := by
  rcases hM with ⟨d, rfl, hd⟩
  exact Matrix.isHermitian_diagonal d

/-- A positive definite diagonal matrix in the source sense is positive definite in
`Matrix.PosDef`. -/
theorem IsPositiveDefiniteDiagonalMatrix.posDef {M : MatrixN n}
    (hM : IsPositiveDefiniteDiagonalMatrix M) :
    M.PosDef := by
  rcases hM with ⟨d, rfl, hd⟩
  -- Mathlib already characterizes positive definite diagonal matrices by pointwise positivity.
  simpa using (Matrix.PosDef.diagonal hd)

/-- For a positive definite diagonal damping matrix `D`, the regularized normal matrices
`J(x)ᵀ * J(x) + μ • D` from `(7.3.27)` are positive definite for every `μ > 0`. -/
theorem levenbergMarquardtRegularizedNormalMatrix_posDef
    (J : JacobianMatrix m n) (D : MatrixN n) (hD : IsPositiveDefiniteDiagonalMatrix D)
    {μ : ℝ} (hμ : 0 < μ) :
    (levenbergMarquardtRegularizedNormalMatrix J D μ).PosDef := by
  have hGram : (Jᵀ * J).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self J
  have hScaled : (μ • D).PosDef := (hD.posDef).smul hμ
  -- A positive semidefinite Gram term plus a positive definite damping term is positive definite.
  simpa [levenbergMarquardtRegularizedNormalMatrix] using Matrix.PosDef.posSemidef_add hGram hScaled

/-- For a positive definite diagonal damping matrix `D`, the regularized normal matrix
`J(x)ᵀ * J(x) + μ • D` is Hermitian for every positive damping parameter `μ`. -/
theorem levenbergMarquardtRegularizedNormalMatrix_isHermitian
    (J : JacobianMatrix m n) (D : MatrixN n) (hD : IsPositiveDefiniteDiagonalMatrix D)
    (μ : Set.Ioi (0 : ℝ)) :
    (levenbergMarquardtRegularizedNormalMatrix J D μ.1).IsHermitian := by
  simpa [levenbergMarquardtRegularizedNormalMatrix] using
    (Matrix.isHermitian_conjTranspose_mul_self J).add
      ((hD.isHermitian).smul (IsSelfAdjoint.all μ.1))

end
