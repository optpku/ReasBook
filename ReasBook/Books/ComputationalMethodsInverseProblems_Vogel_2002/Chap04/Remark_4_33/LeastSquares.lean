/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

open scoped Matrix

namespace LeastSquares

universe u v

section WeightedResidual

variable {m : Type u} {n : Type v}
variable [Fintype m] [Fintype n] [DecidableEq n]

/-- The weighted residual objective `Matrix.energyNorm W hW (K.toEuclideanLin x - y)` for a
positive-definite weight matrix `W`. -/
def weightedResidualObjective (K : Matrix m n ℝ) (W : Matrix m m ℝ) (hW : W.PosDef)
    (y : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) : ℝ :=
  Matrix.energyNorm W hW (K.toEuclideanLin x - y)

/-- The defining formula for `LeastSquares.weightedResidualObjective`. -/
theorem weightedResidualObjective_def (K : Matrix m n ℝ) (W : Matrix m m ℝ) (hW : W.PosDef)
    (y : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    weightedResidualObjective K W hW y x = Matrix.energyNorm W hW (K.toEuclideanLin x - y) :=
  by
    simp [weightedResidualObjective]

/-- A vector is a weighted least-squares solution when it minimizes
`weightedResidualObjective K W hW y` on `Set.univ`. -/
def IsWeightedLeastSquaresSolution (K : Matrix m n ℝ) (W : Matrix m m ℝ) (hW : W.PosDef)
    (y : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) : Prop :=
  IsMinOn (weightedResidualObjective K W hW y) Set.univ x

/-- The defining characterization of `LeastSquares.IsWeightedLeastSquaresSolution`. -/
theorem IsWeightedLeastSquaresSolution_iff (K : Matrix m n ℝ) (W : Matrix m m ℝ)
    (hW : W.PosDef)
    (y : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    IsWeightedLeastSquaresSolution K W hW y x ↔
      IsMinOn (weightedResidualObjective K W hW y) Set.univ x :=
  Iff.rfl

end WeightedResidual

section OrdinaryLeastSquares

variable {m : Type u} {n : Type v}
variable [Fintype m] [Fintype n] [DecidableEq n]

/-- The ordinary least-squares operator matrix `(Kᵀ * K)⁻¹ * Kᵀ`. -/
def ordinaryOperator (K : Matrix m n ℝ) : Matrix n m ℝ :=
  (Kᵀ * K)⁻¹ * Kᵀ

/-- The defining formula for `LeastSquares.ordinaryOperator`. -/
theorem ordinaryOperator_def (K : Matrix m n ℝ) :
    ordinaryOperator K = (Kᵀ * K)⁻¹ * Kᵀ :=
  by
    simp [ordinaryOperator]

end OrdinaryLeastSquares

section OrdinarySolution

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- The ordinary least-squares solution obtained by applying `ordinaryOperator K`
to the data vector. -/
def ordinarySolution (K : Matrix m n ℝ) (y : EuclideanSpace ℝ m) : EuclideanSpace ℝ n :=
  Matrix.toEuclideanLin (ordinaryOperator K) y

/-- The defining formula for `LeastSquares.ordinarySolution`. -/
theorem ordinarySolution_eq (K : Matrix m n ℝ) (y : EuclideanSpace ℝ m) :
    ordinarySolution K y = Matrix.toEuclideanLin (ordinaryOperator K) y :=
  by
    simp [ordinarySolution]

end OrdinarySolution

end LeastSquares
