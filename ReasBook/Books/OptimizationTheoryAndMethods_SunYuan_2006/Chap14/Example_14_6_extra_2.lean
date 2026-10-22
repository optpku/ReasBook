/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_1_extra_1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ResidualPoint" => EuclideanSpace ℝ (Fin m)

-- Source-facing layer: the residual vector and its norm-minimization objective for `A x = b`.
-- Core/canonical owner: the Euclidean matrix action `Matrix.toEuclideanLin A`.
-- Bridge/view: the coordinate formula `WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)`, together with
-- the Chapter 7 squared least-squares owner specialized to the linear residual.

/-- The residual vector `A x - b` for the linear system `A x = b`, viewed as a point of
`EuclideanSpace ℝ (Fin m)`. -/
def linearSystemResidual
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) : ResidualPoint :=
  Matrix.toEuclideanLin A x - b

/-- Evaluating `linearSystemResidual A b x` gives the canonical Euclidean residual
`Matrix.toEuclideanLin A x - b`. -/
theorem linearSystemResidual_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    linearSystemResidual A b x = Matrix.toEuclideanLin A x - b := rfl

/-- The canonical Euclidean residual `Matrix.toEuclideanLin A x - b` agrees with the coordinate
formula `WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)`. -/
theorem linearSystemResidual_eq_coordinate
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    linearSystemResidual A b x = WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp) := by
  rw [linearSystemResidual, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  rfl

/-- Chapter14 Example 14.6-extra-2 (1): for a linear system `A x = b` with
`A : Matrix (Fin m) (Fin n) ℝ`, right-hand side `b : ℝ^m`, and a chosen norm
`ν : AddGroupNorm ResidualPoint` on
the residual space `ResidualPoint = EuclideanSpace ℝ (Fin m)`, the associated data-fitting
objective is `x ↦ ν (linearSystemResidual A b x)`. Minimizing this objective
formalizes the source problem `min_{x ∈ ℝ^n} ‖A x - b‖`. -/
def linearResidualObjective
    (ν : AddGroupNorm ResidualPoint)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) : Point → ℝ :=
  fun x ↦ ν (linearSystemResidual A b x)

/-- Evaluating `linearResidualObjective ν A b` unfolds to the canonical residual norm
`ν (Matrix.toEuclideanLin A x - b)`. -/
theorem linearResidualObjective_apply
    (ν : AddGroupNorm ResidualPoint)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    linearResidualObjective ν A b x =
      ν (Matrix.toEuclideanLin A x - b) := rfl

/-- The data-fitting objective may also be read in coordinates as
`x ↦ ν (WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp))`. -/
theorem linearResidualObjective_eq_coordinate
    (ν : AddGroupNorm ResidualPoint)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    linearResidualObjective ν A b x =
      ν (WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)) := by
  calc
    linearResidualObjective ν A b x = ν (linearSystemResidual A b x) := rfl
    _ = ν (WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)) :=
      congrArg ν (linearSystemResidual_eq_coordinate A b x)

/-- Chapter14 Example 14.6-extra-2 (2): if the chosen norm in `(14.6.3)` is the Euclidean
`2`-norm, then the resulting data-fitting objective is the Euclidean residual objective
`x ↦ ‖A x - b‖₂`. -/
def euclideanLinearResidualObjective
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) : Point → ℝ :=
  linearResidualObjective (normAddGroupNorm ResidualPoint) A b

/-- Evaluating `euclideanLinearResidualObjective A b` unfolds to the Euclidean norm of the canonical
residual `Matrix.toEuclideanLin A x - b`. -/
theorem euclideanLinearResidualObjective_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    euclideanLinearResidualObjective A b x = ‖Matrix.toEuclideanLin A x - b‖ := rfl

/-- The Euclidean residual objective is also the Euclidean norm of the coordinate residual
`WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)`. -/
theorem euclideanLinearResidualObjective_eq_coordinate
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    euclideanLinearResidualObjective A b x = ‖WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)‖ := by
  calc
    euclideanLinearResidualObjective A b x = ‖linearSystemResidual A b x‖ := rfl
    _ = ‖WithLp.toLp 2 (A.mulVec x.ofLp - b.ofLp)‖ :=
      congrArg norm (linearSystemResidual_eq_coordinate A b x)

/-- `euclideanLinearResidualObjective A b` is the Euclidean-norm specialization of
`linearResidualObjective`. -/
theorem linearResidualObjective_euclidean_eq_euclideanLinearResidualObjective
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) :
    linearResidualObjective (normAddGroupNorm ResidualPoint) A b =
      euclideanLinearResidualObjective A b := rfl

/-- The Chapter 7 least-squares objective for the linear residual `linearSystemResidual A b`
is one-half the square of the Euclidean residual objective from this example. -/
theorem nonlinearLeastSquaresObjective_linearSystemResidual_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : ResidualPoint) (x : Point) :
    nonlinearLeastSquaresObjective (linearSystemResidual A b) x =
      ((1 : ℝ) / 2) * (euclideanLinearResidualObjective A b x) ^ (2 : ℕ) := by
  calc
    nonlinearLeastSquaresObjective (linearSystemResidual A b) x
        = ((1 : ℝ) / 2) * ‖linearSystemResidual A b x‖ ^ (2 : ℕ) := by
            simpa using nonlinearLeastSquaresObjective_eq_half_norm_sq (linearSystemResidual A b) x
    _ = ((1 : ℝ) / 2) * (euclideanLinearResidualObjective A b x) ^ (2 : ℕ) := by
      rfl

#print axioms linearResidualObjective
#print axioms euclideanLinearResidualObjective

end
