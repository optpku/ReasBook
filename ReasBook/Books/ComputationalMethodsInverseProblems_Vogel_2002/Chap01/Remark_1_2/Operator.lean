/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Diagonal

public section

noncomputable section

open scoped Matrix

namespace FilterRegularization

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The square finite-dimensional spectral-filter reconstruction matrix in an
orthogonal SVD basis. -/
@[expose]
def operatorMatrix (U V : Matrix n n ℝ) (s : n → ℝ) (w : ℝ → ℝ → ℝ) (α : ℝ) :
    Matrix n n ℝ :=
  V * Matrix.diagonal (fun i ↦ w α (s i ^ 2) / s i) * Uᵀ

/-- The defining formula for `FilterRegularization.operatorMatrix`. -/
theorem operatorMatrix_def
    (U V : Matrix n n ℝ) (s : n → ℝ) (w : ℝ → ℝ → ℝ) (α : ℝ) :
    operatorMatrix U V s w α =
      V * Matrix.diagonal (fun i ↦ w α (s i ^ 2) / s i) * Uᵀ := by
  unfold operatorMatrix
  rfl

/-- The square finite-dimensional spectral-filter reconstruction operator in
`EuclideanSpace`, induced by `FilterRegularization.operatorMatrix`. -/
@[expose]
def operator (U V : Matrix n n ℝ) (s : n → ℝ) (w : ℝ → ℝ → ℝ) (α : ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin (operatorMatrix U V s w α)

/-- Applying `FilterRegularization.operator` agrees with applying
`FilterRegularization.operatorMatrix` through `Matrix.toEuclideanLin`. -/
theorem operator_apply
    (U V : Matrix n n ℝ) (s : n → ℝ) (w : ℝ → ℝ → ℝ) (α : ℝ)
    (d : EuclideanSpace ℝ n) :
    operator U V s w α d = Matrix.toEuclideanLin (operatorMatrix U V s w α) d := by
  unfold operator
  rfl

end FilterRegularization
