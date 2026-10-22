/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace
open scoped SecondOrderDerivativeBlocks

variable {n m : ℕ}

namespace LpApproximationBoxProblem

open LpApproximationEpigraphPoint

/-
Definition 5.4.9.9 lies in the Chapter 5 box-constrained `ℓ_p` approximation / explicit-structure
Newton-system domain.

Sampled owner declarations:
- `LpApproximationBoxProblem` in `Definition_5_4_9_1`, the chapter owner for the primitive
  box-constrained `ℓ_p` approximation data `(p, a, b, α, β)`;
- `problem.StrictBarrierModelPoint` and `problem.barrierModelBarrierDomain` in
  `Definition_5_4_9_5`, the strict-domain owner already established for the logarithmic barrier
  and its interior points;
- `separableLogBarrierF4` in `Definition_5_4_8_12`, the Chapter 5 owner for the scalar barrier
  whose second derivatives supply the Newton blocks;
- `secondOrderDerivativeBlock11`, `secondOrderDerivativeBlock12`, and
  `secondOrderDerivativeBlock22` in `Definition_5_4_9_8`, the source-facing Hessian-block owners
  used to form the diagonal Newton coefficients.

Best owner abstraction:
- source-facing: the current-point Newton shorthands attached to a strict barrier-model point;
- core/canonical: `LpApproximationBoxProblem n m` together with `problem.StrictBarrierModelPoint`;
- bridge/view: the matrix-level Newton-system surface that consumes these shorthands directly.

Primitive data:
- `problem : LpApproximationBoxProblem n m`;
- `decision : problem.StrictBarrierModelPoint`.

Derived API:
- `decision.newtonSystemResidual`;
- `κ[decision]`, `Λ₀[decision]`, `Λ₁[decision]`, `Λ₂[decision]`, `D[decision]`;
- `A[problem]`.

The Chapter 5 Newton blocks are Hessian data of the logarithmic barrier, so they are only
mathematically meaningful on the strict barrier domain from `Definition_5_4_9_5`. This refinement
keeps the same formulas, but moves their public owner to `problem.StrictBarrierModelPoint` instead
of letting Lean totalize them at arbitrary lifted points.
-/

/-- The constraint matrix `A ∈ ℝ^{n × m}` with columns `a₁, ..., aₘ`. -/
def newtonSystemConstraintMatrix
    (problem : LpApproximationBoxProblem n m) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun i j ↦ problem.a j i

namespace StrictBarrierModelPoint

/-- Definition 5.4.9.9: the residual shorthand `sᵢ = ⟪aᵢ, x⟫ - b⁽ⁱ⁾` at the current strict
barrier-model point, used in the Newton-system diagonal matrices. -/
def newtonSystemResidual
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    Fin m → ℝ :=
  fun i ↦ ⟪problem.a i, decision.1.point⟫ - problem.b i

-- Proof sketch: unfold `newtonSystemResidual`; the displayed identity is its defining formula.
/-- The residual entries of `decision.newtonSystemResidual` are the shorthands
`sᵢ = ⟪aᵢ, x⟫ - b⁽ⁱ⁾`. -/
theorem newtonSystemResidual_apply
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem)
    (i : Fin m) :
    decision.newtonSystemResidual i =
      ⟪problem.a i, decision.1.point⟫ - problem.b i :=
  rfl

-- Proof sketch: unfold `newtonSystemResidual`; the right-hand side is exactly its defining
-- residual function.
/-- Expanding `decision.newtonSystemResidual` recovers the residual function
`i ↦ ⟪aᵢ, x⟫ - b⁽ⁱ⁾`. -/
theorem newtonSystemResidual_def
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.newtonSystemResidual =
      fun i ↦ ⟪problem.a i, decision.1.point⟫ - problem.b i :=
  rfl

attribute [simp] newtonSystemResidual_apply newtonSystemResidual_def

/-- The coupling scalar `κ = (ξ - ∑ᵢ τ⁽ⁱ⁾)⁻²` of the Newton system, attached to the current strict
barrier-model point. -/
def newtonSystemKappa
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) : ℝ :=
  1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) ^ (2 : ℕ)

/-- The diagonal matrix `Λ₀` with entries
`1 / (x⁽ⁱ⁾ - α⁽ⁱ⁾)^2 + 1 / (β⁽ⁱ⁾ - x⁽ⁱ⁾)^2`. -/
def newtonSystemLambda0
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i ↦
    1 / (decision.1.point i - problem.α i) ^ (2 : ℕ) +
      1 / (problem.β i - decision.1.point i) ^ (2 : ℕ)

/-- The diagonal matrix `Λ₁` with entries `h₁₁(sᵢ, τ⁽ⁱ⁾)` coming from the Chapter 5 scalar
barrier `separableLogBarrierF4 problem.p`. For the one-dimensional `y`-variable, the Hessian block
`secondOrderDerivativeBlock11` is a continuous linear endomorphism of `ℝ`, so the scalar entry is
its value at `1`. -/
def newtonSystemLambda1
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun i ↦
    let s := decision.newtonSystemResidual i
    let τ := decision.1.residualSlack i
    (h₁₁[(separableLogBarrierF4 problem.p)](s, τ)) 1

/-- The diagonal matrix `Λ₂` with entries `h₁₂(sᵢ, τ⁽ⁱ⁾)` coming from the Chapter 5 scalar
barrier `separableLogBarrierF4 problem.p`. -/
def newtonSystemLambda2
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun i ↦
    let s := decision.newtonSystemResidual i
    let τ := decision.1.residualSlack i
    h₁₂[(separableLogBarrierF4 problem.p)](s, τ)

/-- The diagonal matrix `D` with entries `h₂₂(sᵢ, τ⁽ⁱ⁾)` coming from the Chapter 5 scalar
barrier `separableLogBarrierF4 problem.p`. -/
def newtonSystemD
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun i ↦
    let s := decision.newtonSystemResidual i
    let τ := decision.1.residualSlack i
    h₂₂[(separableLogBarrierF4 problem.p)](s, τ)

/- The textbook vector `\bar e_m = (1, \dots, 1)` is the canonical constant-one function in
`ℝ^m`. -/
example : Fin m → ℝ := 1

-- Proof sketch: unfold `newtonSystemKappa`; the right-hand side is exactly the defining
-- reciprocal-square formula.
/-- Expanding `newtonSystemKappa decision` recovers the reciprocal square of
`ξ - ∑ i, τ⁽ⁱ⁾`. -/
@[simp] theorem newtonSystemKappa_eq
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    newtonSystemKappa decision =
      1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) ^ (2 : ℕ) :=
  rfl

-- Proof sketch: unfold `newtonSystemLambda0`; the matrix is defined as this diagonal matrix.
/-- Expanding `newtonSystemLambda0 decision` recovers the diagonal matrix whose `i`-th entry is
`1 / (x⁽ⁱ⁾ - α⁽ⁱ⁾)^2 + 1 / (β⁽ⁱ⁾ - x⁽ⁱ⁾)^2`. -/
@[simp] theorem newtonSystemLambda0_eq_diagonal
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    newtonSystemLambda0 decision =
      Matrix.diagonal (fun i ↦
        1 / (decision.1.point i - problem.α i) ^ (2 : ℕ) +
          1 / (problem.β i - decision.1.point i) ^ (2 : ℕ)) :=
  rfl

-- Proof sketch: unfold `newtonSystemLambda1`; the matrix is defined by diagonalizing the scalar
-- `h₁₁` block entries.
/-- Expanding `newtonSystemLambda1 decision` recovers the diagonal matrix with entries
`h₁₁(sᵢ, τ⁽ⁱ⁾)`. -/
@[simp] theorem newtonSystemLambda1_eq_diagonal
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    newtonSystemLambda1 decision =
      Matrix.diagonal (fun i ↦
        let s := decision.newtonSystemResidual i
        let τ := decision.1.residualSlack i
        (h₁₁[(separableLogBarrierF4 problem.p)](s, τ)) 1) :=
  rfl

-- Proof sketch: unfold `newtonSystemLambda2`; the matrix is defined by diagonalizing the scalar
-- `h₁₂` block entries.
/-- Expanding `newtonSystemLambda2 decision` recovers the diagonal matrix with entries
`h₁₂(sᵢ, τ⁽ⁱ⁾)`. -/
@[simp] theorem newtonSystemLambda2_eq_diagonal
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    newtonSystemLambda2 decision =
      Matrix.diagonal (fun i ↦
        let s := decision.newtonSystemResidual i
        let τ := decision.1.residualSlack i
        h₁₂[(separableLogBarrierF4 problem.p)](s, τ)) :=
  rfl

-- Proof sketch: unfold `newtonSystemD`; the matrix is defined by diagonalizing the scalar `h₂₂`
-- block entries.
/-- Expanding `newtonSystemD decision` recovers the diagonal matrix with entries
`h₂₂(sᵢ, τ⁽ⁱ⁾)`. -/
@[simp] theorem newtonSystemD_eq_diagonal
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    newtonSystemD decision =
      Matrix.diagonal (fun i ↦
        let s := decision.newtonSystemResidual i
        let τ := decision.1.residualSlack i
        h₂₂[(separableLogBarrierF4 problem.p)](s, τ)) :=
  rfl

end StrictBarrierModelPoint

-- Proof sketch: unfold `newtonSystemConstraintMatrix`; the `(i, j)` entry is the `i`-th
-- coordinate of the `j`-th column vector `aⱼ`.
/-- The entries of `A[problem]` are the coordinates of the vectors
`a₁, ..., aₘ`. -/
@[simp] theorem newtonSystemConstraintMatrix_apply
    (problem : LpApproximationBoxProblem n m)
    (i : Fin n) (j : Fin m) :
    newtonSystemConstraintMatrix problem i j = problem.a j i :=
  rfl

end LpApproximationBoxProblem

namespace LpBarrierNewtonSystem

/-- Source-facing Newton-system notation for the coupling scalar attached to a strict
barrier-model point. -/
scoped notation:max "κ[" decision:arg "]" =>
  LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemKappa decision

/-- Source-facing Newton-system notation for the `x`-block diagonal matrix. -/
scoped notation:max "Λ₀[" decision:arg "]" =>
  LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda0 decision

/-- Source-facing Newton-system notation for the `h₁₁` diagonal matrix. -/
scoped notation:max "Λ₁[" decision:arg "]" =>
  LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda1 decision

/-- Source-facing Newton-system notation for the `h₁₂` diagonal matrix. -/
scoped notation:max "Λ₂[" decision:arg "]" =>
  LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda2 decision

/-- Source-facing Newton-system notation for the `h₂₂` diagonal matrix. -/
scoped notation:max "D[" decision:arg "]" =>
  LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD decision

/-- Source-facing Newton-system notation for the constraint matrix with columns `a₁, ..., aₘ`. -/
scoped notation:max "A[" problem:arg "]" =>
  LpApproximationBoxProblem.newtonSystemConstraintMatrix problem

end LpBarrierNewtonSystem

open scoped LpBarrierNewtonSystem

end
