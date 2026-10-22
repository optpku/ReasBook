/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Defs
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_7_3

noncomputable section

open Filter

section

local notation "Multiplier" => LagrangeNewtonMultiplier

-- Domain sampling for this file:
-- * source-facing layer: the concrete Maratos data `f`, `c`, `x̄(ε)`, `d̄(ε)`;
-- * core/canonical layer: `EqualityConstrainedProblem`,
--   `IsMinOn`, `sqpSubproblemObjective`, `satisfiesSqpLinearizedConstraints`, and
--   `maratosProblem.toStandardPenaltyProblem.l1ExactPenalty` through
--   `Chapter12/Theorem_12_7_3`;
-- * bridge/view layer here: the Maratos example as a concrete equality-constrained problem plus
--   its single-column linearized constraint Jacobian and Hessian model.
--
-- The file therefore keeps only the concrete Maratos data locally and reuses the chapter owner
-- declarations for the SQP subproblem and `L₁` exact penalty surfaces.

/-- The Maratos-effect objective is `f(u, v) = 3 * v^2 - 2 * u`. -/
def maratosObjective (x : Point 2) : ℝ :=
  3 * (x 1) ^ (2 : ℕ) - 2 * x 0

/-- The Maratos-effect equality constraint is `c(u, v) = u - v^2`. -/
def maratosConstraint (x : Point 2) : ℝ :=
  x 0 - (x 1) ^ (2 : ℕ)

/-- The reference solution `x* = (0, 0)` in the Maratos example. -/
def maratosSolution : Point 2 :=
  0

/-- The Maratos example as the equality-constrained problem with objective `maratosObjective`
and the single equality constraint `maratosConstraint`. -/
def maratosProblem : EqualityConstrainedProblem 2 1 where
  objective := maratosObjective
  constraint := fun _ ↦ maratosConstraint

/-- The source path `x̄(ε) = (ε^2, ε)` used to exhibit the Maratos effect. -/
def maratosPath (ε : ℝ) : Point 2 :=
  EuclideanSpace.single 0 (ε ^ (2 : ℕ)) + EuclideanSpace.single 1 ε

/-- The QP step `d̄(ε) = (-2 * ε^2, -ε)` attached to `maratosPath ε`. -/
def maratosStep (ε : ℝ) : Point 2 :=
  EuclideanSpace.single 0 (-2 * ε ^ (2 : ℕ)) + EuclideanSpace.single 1 (-ε)

/-- The trial point `x̄(ε) + d̄(ε)` produced by the Maratos example. -/
def maratosTrialPoint (ε : ℝ) : Point 2 :=
  maratosPath ε + maratosStep ε

/-- The Hessian model `B = diag(0, 2)` used in the Maratos SQP subproblem, so that
`(1 / 2) * ⟪d, B d⟫ = d₂^2`. -/
def maratosHessian : Point 2 →L[ℝ] Point 2 :=
  ((EuclideanSpace.proj 1 : Point 2 →L[ℝ] ℝ).smulRight
    (EuclideanSpace.single 1 (2 : ℝ)))

/-- The single-column linearized constraint Jacobian `A(x̄(ε))` for the Maratos example,
viewed as a continuous linear map `ℝ → ℝ²`. -/
def maratosConstraintJacobian (ε : ℝ) : Multiplier 1 →L[ℝ] Point 2 :=
  ((EuclideanSpace.proj 0 : Multiplier 1 →L[ℝ] ℝ).smulRight
    (gradient maratosConstraint (maratosPath ε)))

/-- The unique constraint component of `maratosProblem` is `maratosConstraint`. -/
@[simp] theorem maratosProblem_constraint_apply (x : Point 2) :
    maratosProblem.constraint 0 x = maratosConstraint x :=
  rfl

/-- The unique coordinate of `maratosProblem.constraintVector x` is `maratosConstraint x`. -/
@[simp] theorem maratosProblem_constraintVector_apply (x : Point 2) :
    maratosProblem.constraintVector x 0 = maratosConstraint x := by
  exact EqualityConstrainedProblem.constraintVector_apply maratosProblem x 0

/-- For the single Maratos equality constraint, the canonical linearized feasibility predicate
reduces to the scalar source equation
`⟪∇ c(x̄(ε)), d⟫ = -c(x̄(ε))`. -/
theorem maratosSubproblemFeasible_iff (ε : ℝ) (d : Point 2) :
    satisfiesSqpLinearizedConstraints
      (maratosConstraintJacobian ε)
      (maratosProblem.constraintVector (maratosPath ε))
      d ↔
      inner ℝ (gradient maratosConstraint (maratosPath ε)) d =
        -maratosConstraint (maratosPath ε) := sorry

/-- For the single Maratos equality constraint, the chapter exact-penalty owner reduces to the
source scalar formula `f(x) + σ * |c(x)|`. -/
theorem maratosL1ExactPenalty_eq (σ : ℝ) (x : Point 2) :
    maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ x =
      maratosObjective x + σ * |maratosConstraint x| := sorry

#print axioms maratosObjective
#print axioms maratosConstraint
#print axioms maratosSolution
#print axioms maratosProblem
#print axioms maratosPath
#print axioms maratosStep
#print axioms maratosTrialPoint
#print axioms maratosHessian
#print axioms maratosConstraintJacobian

/-- Chapter12 Remark 12.4-extra-1 (1): `maratosStep ε = d̄(ε)` solves the quadratic programming
subproblem `(12.4.6)`-`(12.4.7)`, expressed through the chapter's canonical SQP subproblem
owner. -/
theorem maratosStep_isMinOn_smoothExactPenaltySubproblem (ε : ℝ) :
    IsMinOn
      (sqpSubproblemObjective
        (gradient maratosObjective (maratosPath ε))
        maratosHessian)
      {d |
        satisfiesSqpLinearizedConstraints
          (maratosConstraintJacobian ε)
          (maratosProblem.constraintVector (maratosPath ε))
          d}
      (maratosStep ε) := sorry

/-- Chapter12 Remark 12.4-extra-1 (2): the trial-point error satisfies the quadratic-order
estimate `(12.4.9)`,
`‖maratosTrialPoint ε - maratosSolution‖ = O(‖maratosPath ε - maratosSolution‖^2)` at `ε = 0`. -/
theorem maratosExample_trialPointError_isBigO_sqPathError :
    Asymptotics.IsBigO (nhds (0 : ℝ))
      (fun ε : ℝ ↦ ‖maratosTrialPoint ε - maratosSolution‖)
      (fun ε : ℝ ↦ ‖maratosPath ε - maratosSolution‖ ^ (2 : ℕ)) := sorry

/-- Chapter12 Remark 12.4-extra-1 (3): the objective value at `x̄(ε)` is
`f(x̄(ε)) = ε^2`. -/
theorem maratosExample_objective_atPath (ε : ℝ) :
    maratosObjective (maratosPath ε) = ε ^ (2 : ℕ) := sorry

/-- Chapter12 Remark 12.4-extra-1 (4): the equality constraint is satisfied at `x̄(ε)`,
so `c(x̄(ε)) = 0`. -/
theorem maratosExample_constraint_atPath (ε : ℝ) :
    maratosConstraint (maratosPath ε) = 0 := sorry

/-- Chapter12 Remark 12.4-extra-1 (5): the objective value at the trial point is
`f(x̄(ε) + d̄(ε)) = 2 * ε^2`. -/
theorem maratosExample_objective_atTrialPoint (ε : ℝ) :
    maratosObjective (maratosTrialPoint ε) = 2 * ε ^ (2 : ℕ) := sorry

/-- Chapter12 Remark 12.4-extra-1 (6): the trial point violates the equality constraint by
`c(x̄(ε) + d̄(ε)) = -ε^2`. -/
theorem maratosExample_constraint_atTrialPoint (ε : ℝ) :
    maratosConstraint (maratosTrialPoint ε) = -(ε ^ (2 : ℕ)) := sorry

/-- Chapter12 Remark 12.4-extra-1 (7): for every nonzero `ε`, the Maratos trial point has a
worse objective value than `x̄(ε)`, i.e.
`maratosObjective (maratosTrialPoint ε) > maratosObjective (maratosPath ε)`. -/
theorem maratosExample_objective_increases
    (ε : ℝ) (hε : ε ≠ 0) :
    maratosObjective (maratosTrialPoint ε) > maratosObjective (maratosPath ε) := sorry

/-- Chapter12 Remark 12.4-extra-1 (8): for every nonzero `ε`, the trial point has larger
absolute constraint violation than `x̄(ε)`, i.e.
`|maratosConstraint (maratosTrialPoint ε)| > |maratosConstraint (maratosPath ε)|`. -/
theorem maratosExample_constraintViolation_increases
    (ε : ℝ) (hε : ε ≠ 0) :
    |maratosConstraint (maratosTrialPoint ε)| >
      |maratosConstraint (maratosPath ε)| := sorry

/-- Chapter12 Remark 12.4-extra-1 (9): for every positive penalty parameter `σ` and positive
`ε`, the Chapter 12 `L₁` exact penalty function also increases at the Maratos trial point, so
the full step is not acceptable for this merit function. The statement uses the chapter's
canonical exact-penalty owner `maratosProblem.toStandardPenaltyProblem.l1ExactPenalty`. -/
theorem maratosExample_l1Penalty_increases
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ (maratosTrialPoint ε) >
      maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ (maratosPath ε) := sorry

end
