/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

noncomputable section

section Chapter09Theorem911

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace QuadraticProgram

/-- The quadratic-program objective transport is differentiable at every point of the Chapter 8
bridge problem. -/
theorem toConstrainedOptimizationProblem_differentiableAt_objective
    (P : QuadraticProgram n me mi) (xStar : Point) :
    DifferentiableAt ℝ P.toConstrainedOptimizationProblem.objective
      ((EuclideanSpace.equiv (Fin n) ℝ) xStar) := by
  sorry

/-- Every transported quadratic-program constraint is differentiable at every point of the
Chapter 8 bridge problem. -/
theorem toConstrainedOptimizationProblem_hasConstraintGradientsAt
    (P : QuadraticProgram n me mi) (xStar : Point) :
    P.toConstrainedOptimizationProblem.HasConstraintGradientsAt
      ((EuclideanSpace.equiv (Fin n) ℝ) xStar) := by
  sorry

/-- The quadratic-program objective transport is `C²` at every point of the Chapter 8 bridge
problem. -/
theorem toConstrainedOptimizationProblem_contDiffAt_objective
    (P : QuadraticProgram n me mi) (xStar : Point) :
    ContDiffAt ℝ 2 P.toConstrainedOptimizationProblem.objective
      ((EuclideanSpace.equiv (Fin n) ℝ) xStar) := by
  sorry

/-- Every transported quadratic-program constraint is `C²` at every point of the Chapter 8
bridge problem. -/
theorem toConstrainedOptimizationProblem_contDiffAt_constraint
    (P : QuadraticProgram n me mi) (xStar : Point) :
    ∀ i : Fin (me + mi),
      ContDiffAt ℝ 2 (P.toConstrainedOptimizationProblem.constraint i)
        ((EuclideanSpace.equiv (Fin n) ℝ) xStar) := by
  sorry

/-- The Chapter 8 constraint qualification is automatic for the affine-constraint bridge of a
quadratic program. -/
theorem toConstrainedOptimizationProblem_constraintQualificationAt
    (P : QuadraticProgram n me mi) (xStar : Point)
    (hxStar : xStar ∈ P.feasibleSet) :
    P.toConstrainedOptimizationProblem.ConstraintQualificationAt
      ((EuclideanSpace.equiv (Fin n) ℝ) xStar) := by
  sorry

/-- For quadratic programs, the Chapter 8 Lagrangian Hessian quadratic form is exactly the
source matrix quadratic form `dᵀ G d`. -/
theorem toConstrainedOptimizationProblem_lagrangianHessianQuadratic_eq
    (P : QuadraticProgram n me mi) (xStar : Point) (lamStar : Fin (me + mi) → ℝ) (d : Point) :
    P.toConstrainedOptimizationProblem.lagrangianHessianQuadratic
        ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar
        ((EuclideanSpace.equiv (Fin n) ℝ) d) =
      inner ℝ d (Matrix.toEuclideanLin P.G d) := by
  sorry

/-- The Chapter 9 second-order necessary condition for `P` at `(xStar, lamStar)`, kept as a thin
source-facing bridge over the Chapter 8 owner
`P.toConstrainedOptimizationProblem.linearizedNullConstraintDirections`. -/
abbrev HasSecondOrderNecessaryCondition
    (P : QuadraticProgram n me mi) (xStar : Point) (lamStar : Fin (me + mi) → ℝ) : Prop :=
  ∀ d : Point,
    (EuclideanSpace.equiv (Fin n) ℝ d) ∈
      P.toConstrainedOptimizationProblem.linearizedNullConstraintDirections
        ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar →
      0 ≤ inner ℝ d (Matrix.toEuclideanLin P.G d)

/-- Unfolding `P.HasSecondOrderNecessaryCondition xStar lamStar` gives the quadratic-form
nonnegativity condition on the Chapter 8 null-constraint directions. -/
theorem hasSecondOrderNecessaryCondition_iff
    (P : QuadraticProgram n me mi) (xStar : Point) (lamStar : Fin (me + mi) → ℝ) :
    P.HasSecondOrderNecessaryCondition xStar lamStar ↔
      ∀ d : Point,
        (EuclideanSpace.equiv (Fin n) ℝ d) ∈
          P.toConstrainedOptimizationProblem.linearizedNullConstraintDirections
            ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar →
          0 ≤ inner ℝ d (Matrix.toEuclideanLin P.G d) :=
  Iff.rfl

/-- The source quadratic-form condition is exactly the Chapter 8 Lagrangian-Hessian
nonnegativity condition after transporting the quadratic program to
`P.toConstrainedOptimizationProblem`. -/
theorem hasSecondOrderNecessaryCondition_iff_lagrangianHessianQuadratic_nonneg
    (P : QuadraticProgram n me mi) (xStar : Point) (lamStar : Fin (me + mi) → ℝ) :
    P.HasSecondOrderNecessaryCondition xStar lamStar ↔
      ∀ d : Point,
        (EuclideanSpace.equiv (Fin n) ℝ d) ∈
          P.toConstrainedOptimizationProblem.linearizedNullConstraintDirections
            ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar →
          0 ≤
            P.toConstrainedOptimizationProblem.lagrangianHessianQuadratic
              ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar
              ((EuclideanSpace.equiv (Fin n) ℝ) d) := by
  constructor
  · intro h d hd
    simpa [P.toConstrainedOptimizationProblem_lagrangianHessianQuadratic_eq xStar lamStar d]
      using h d hd
  · intro h d hd
    simpa [P.toConstrainedOptimizationProblem_lagrangianHessianQuadratic_eq xStar lamStar d]
      using h d hd

/-- Chapter09 Theorem 9.1.1: if `xStar` is a feasible local minimizer of the quadratic program
`P`, then there exists a multiplier vector `λ*` for the associated constrained optimization
problem such that `(xStar, λ*)` satisfies the Chapter 8 KKT conditions and `dᵀ G d ≥ 0` on the
Chapter 8 set
`P.toConstrainedOptimizationProblem.linearizedNullConstraintDirections
((EuclideanSpace.equiv (Fin n) ℝ) xStar) λ*`,
which is the source critical cone `G(xStar, λ*)` for the quadratic program. -/
theorem exists_isKKTPoint_with_secondOrderNecessaryCondition
    (P : QuadraticProgram n me mi) (xStar : Point)
    (hxStar : xStar ∈ P.feasibleSet)
    (hLocalMin : IsLocalMinOn P.objective P.feasibleSet xStar) :
    ∃ lamStar : Fin (me + mi) → ℝ,
      P.toConstrainedOptimizationProblem.IsKKTPoint
          ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar ∧
        P.HasSecondOrderNecessaryCondition xStar lamStar := by
  sorry

end QuadraticProgram

end Chapter09Theorem911
