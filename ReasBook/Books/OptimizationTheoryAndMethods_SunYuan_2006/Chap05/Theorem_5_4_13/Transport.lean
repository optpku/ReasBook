/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section

open scoped Matrix.Norms.L2Operator
public section

section Chapter05Theorem5413Transport

variable {n : ℕ}

/-- The ambient Euclidean space `ℝ^n` used in the Broyden rank-one transport API. -/
abbrev BroydenPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The Euclidean linear endomorphisms of `BroydenPoint n`. -/
abbrev BroydenOperator (n : ℕ) := BroydenPoint n →L[ℝ] BroydenPoint n

/-- The square real matrices representing Jacobian approximations in dimension `n`. -/
abbrev BroydenMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Transport a Jacobian approximation matrix to the corresponding Euclidean linear map. -/
noncomputable abbrev matrixToOperator (B : BroydenMatrix n) : BroydenOperator n :=
  (Matrix.toEuclideanCLM : BroydenMatrix n ≃⋆ₐ[ℝ] BroydenOperator n) B

/-- Transport a Euclidean linear map to its matrix in the standard basis. -/
noncomputable abbrev operatorToMatrix (B : BroydenOperator n) : BroydenMatrix n :=
  (Matrix.toEuclideanCLM : BroydenMatrix n ≃⋆ₐ[ℝ] BroydenOperator n).symm B

@[simp] theorem operatorToMatrix_matrixToOperator (B : BroydenMatrix n) :
    operatorToMatrix (matrixToOperator B) = B := by
  simp [operatorToMatrix, matrixToOperator]

@[simp] theorem matrixToOperator_operatorToMatrix (B : BroydenOperator n) :
    matrixToOperator (operatorToMatrix B) = B := by
  simp [operatorToMatrix, matrixToOperator]

/-- The matrix corresponding to `fderiv ℝ F x` under the Euclidean-space/matrix equivalence. -/
noncomputable abbrev fderivMatrix (F : BroydenPoint n → BroydenPoint n)
    (x : BroydenPoint n) : BroydenMatrix n :=
  operatorToMatrix (fderiv ℝ F x)

end Chapter05Theorem5413Transport
