/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_6_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_7_3
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

section

local notation "Point" => LagrangeNewtonPoint
local notation "Multiplier" => LagrangeNewtonMultiplier

-- Domain-style sampling for this file:
-- * primary domain: concrete equality-constrained SQP, exact-penalty, and second-order
--   correction constructions;
-- * inspected owner declarations:
--   `EqualityConstrainedProblem`,
--   `exercise125Problem.toStandardPenaltyProblem.l1ExactPenalty`,
--   `isSqpSubproblemSolution`,
--   `IsSecondOrderCorrectionSubproblemSolution`;
-- * core/canonical owner: the chapter's equality-constrained problem together with its SQP
--   subproblem and exact-penalty surfaces;
-- * source-facing data kept here: the concrete objective, constraint, path, and explicit
--   Exercise 12.5 step formulas.

/-- The point `x̄ = (cos θ, sin θ)` from Exercise 12.5. -/
def exercise125Point (θ : ℝ) : Point 2 :=
  EuclideanSpace.single 0 (Real.cos θ) + EuclideanSpace.single 1 (Real.sin θ)

/-- The objective `f(x) = -x₁ + 10 * (x₁^2 + x₂^2)` of Exercise 12.5. -/
def exercise125Objective (x : Point 2) : ℝ :=
  -x 0 + 10 * ((x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ))

/-- The equality constraint `c(x) = x₁^2 + x₂^2 - 1` of Exercise 12.5. -/
def exercise125Constraint (x : Point 2) : ℝ :=
  (x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ) - 1

/-- Exercise 12.5 as an equality-constrained problem with objective `exercise125Objective`
and the single equality constraint `exercise125Constraint`. -/
def exercise125Problem : EqualityConstrainedProblem 2 1 where
  objective := exercise125Objective
  constraint := fun _ ↦ exercise125Constraint

/-- The Exercise 12.5 SQP Hessian model `B = I`. -/
def exercise125Hessian : Point 2 →L[ℝ] Point 2 :=
  ContinuousLinearMap.id ℝ (Point 2)

/-- The single-column linearized constraint Jacobian `A(x̄(θ))`, viewed as a continuous linear
map `ℝ → ℝ²`. -/
def exercise125ConstraintJacobian (θ : ℝ) : Multiplier 1 →L[ℝ] Point 2 :=
  ((EuclideanSpace.proj 0 : Multiplier 1 →L[ℝ] ℝ).smulRight
    (gradient exercise125Constraint (exercise125Point θ)))

/-- The unique constraint component of `exercise125Problem` is `exercise125Constraint`. -/
@[simp] theorem exercise125Problem_constraint_apply (x : Point 2) :
    exercise125Problem.constraint 0 x = exercise125Constraint x :=
  rfl

/-- The unique coordinate of `exercise125Problem.constraintVector x` is
`exercise125Constraint x`. -/
@[simp] theorem exercise125Problem_constraintVector_apply (x : Point 2) :
    exercise125Problem.constraintVector x 0 = exercise125Constraint x := by
  exact EqualityConstrainedProblem.constraintVector_apply exercise125Problem x 0

/-- For the single Exercise 12.5 equality constraint, the canonical linearized feasibility
predicate reduces to the scalar source equation
`⟪∇ c(x̄(θ)), d⟫ = -c(x̄(θ))`. -/
theorem exercise125SubproblemFeasible_iff (θ : ℝ) (d : Point 2) :
    satisfiesSqpLinearizedConstraints
      (exercise125ConstraintJacobian θ)
      (exercise125Problem.constraintVector (exercise125Point θ))
      d ↔
      inner ℝ (gradient exercise125Constraint (exercise125Point θ)) d =
        -exercise125Constraint (exercise125Point θ) := sorry

/-- The explicit SQP step `d = (sin^2 θ, -sin θ * cos θ)` obtained from the subproblem with
`B = I`. -/
def exercise125SqpStep (θ : ℝ) : Point 2 :=
  EuclideanSpace.single 0 (Real.sin θ ^ (2 : ℕ)) +
    EuclideanSpace.single 1 (-(Real.sin θ * Real.cos θ))

/-- The trial point `x̄ + d` of Exercise 12.5. -/
def exercise125TrialPoint (θ : ℝ) : Point 2 :=
  exercise125Point θ + exercise125SqpStep θ

/-- The explicit second-order correction step
`d̂ = (-(1 / 2) * cos θ * sin^2 θ, -(1 / 2) * sin^3 θ)`. -/
def exercise125CorrectionStep (θ : ℝ) : Point 2 :=
  EuclideanSpace.single 0 (-((1 / 2 : ℝ) * Real.cos θ * Real.sin θ ^ (2 : ℕ))) +
    EuclideanSpace.single 1 (-((1 / 2 : ℝ) * Real.sin θ ^ (3 : ℕ)))

/-- The corrected trial point `x̄ + d + d̂` of Exercise 12.5. -/
def exercise125CorrectedPoint (θ : ℝ) : Point 2 :=
  exercise125Point θ + exercise125SqpStep θ + exercise125CorrectionStep θ

/-- For the single Exercise 12.5 equality constraint, the chapter exact-penalty owner reduces to
the source scalar formula `f(x) + σ * |c(x)|`. -/
theorem exercise125L1ExactPenalty_eq (σ : ℝ) (x : Point 2) :
    exercise125Problem.toStandardPenaltyProblem.l1ExactPenalty σ x =
      exercise125Objective x + σ * |exercise125Constraint x| := sorry

#print axioms exercise125Point
#print axioms exercise125Objective
#print axioms exercise125Constraint
#print axioms exercise125Problem
#print axioms exercise125Hessian
#print axioms exercise125ConstraintJacobian
#print axioms exercise125SqpStep
#print axioms exercise125TrialPoint
#print axioms exercise125CorrectionStep
#print axioms exercise125CorrectedPoint

/-- Chapter12 Exercise 12.5 (1): the explicit step `exercise125SqpStep θ` solves the SQP
quadratic subproblem at `x̄ = (cos θ, sin θ)` with `B = I`, expressed through the chapter's
source-facing SQP solution owner. -/
theorem exercise125SqpStep_isSolution (θ : ℝ) :
    isSqpSubproblemSolution
      (gradient exercise125Objective (exercise125Point θ))
      exercise125Hessian
      (exercise125ConstraintJacobian θ)
      (exercise125Problem.constraintVector (exercise125Point θ))
      (exercise125SqpStep θ) := sorry

/-- Chapter12 Exercise 12.5 (2): for every penalty parameter `σ ≥ 0`, the `L₁` exact penalty
function increases from `x̄` to the trial point `x̄ + d` whenever `sin θ ≠ 0`, expressed
through the chapter's canonical exact-penalty owner. -/
theorem exercise125_penalty_lt_atTrialPoint
    {σ θ : ℝ} (hσ : 0 ≤ σ) (hθ : Real.sin θ ≠ 0) :
    exercise125Problem.toStandardPenaltyProblem.l1ExactPenalty σ (exercise125Point θ) <
      exercise125Problem.toStandardPenaltyProblem.l1ExactPenalty σ
        (exercise125TrialPoint θ) := sorry

/-- Chapter12 Exercise 12.5 (3): the explicit vector `exercise125CorrectionStep θ` solves the
second-order correction subproblem associated to the base SQP step, expressed through the
chapter's canonical second-order correction owner. -/
theorem exercise125CorrectionStep_isSolution (θ : ℝ) :
    IsSecondOrderCorrectionSubproblemSolution
      (gradient exercise125Objective (exercise125Point θ))
      (exercise125SqpStep θ)
      exercise125Hessian
      (exercise125ConstraintJacobian θ)
      (exercise125Problem.constraintVector (exercise125TrialPoint θ))
      (exercise125CorrectionStep θ) := sorry

/-- Chapter12 Exercise 12.5 (4): for every `σ ≥ 0`, the corrected point `x̄ + d + d̂` has
smaller `L₁` exact penalty value than `x̄` once `|θ|` is sufficiently small and nonzero. -/
theorem exercise125_penalty_atCorrectedPoint_lt
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ δ > 0, ∀ {θ : ℝ}, 0 < |θ| → |θ| < δ →
      exercise125Problem.toStandardPenaltyProblem.l1ExactPenalty σ
          (exercise125CorrectedPoint θ) <
        exercise125Problem.toStandardPenaltyProblem.l1ExactPenalty σ
          (exercise125Point θ) := sorry

end
