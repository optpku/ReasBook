/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Exercise_3_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Algorithm_12_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_2

noncomputable section

local notation "Multiplier" => LagrangeNewtonMultiplier 1
local notation "State" => rosenbrockPoint × Multiplier

-- Domain sampling:
-- * primary domain: equality-constrained Lagrange-Newton steps for a concrete Rosenbrock
--   exercise with one scalar constraint;
-- * inspected owner declarations:
--   `EqualityConstrainedProblem` from `Chapter12.EqualityConstrainedProblem`;
--   `lagrangeNewtonTrialPoint` / `lagrangeNewtonTrialMultiplier` from
--   `Chapter12.Algorithm_12_1_1`;
--   `lagrangeNewtonDirectionEquation` from `Chapter12.Theorem_12_1_2`;
--   the shared Rosenbrock carrier/objective owner `rosenbrockPoint` / `rosenbrockFunction`
--   from `Chapter03.Exercise_3_4`.
-- Source/core/bridge triage:
-- * source-facing: the concrete Rosenbrock exercise data and its first three iterates;
-- * core/canonical: the Chapter 12 owner `EqualityConstrainedProblem 2 1` together with the
--   generic trial-update surface `lagrangeNewtonTrialPoint` / `lagrangeNewtonTrialMultiplier`;
-- * bridge/view: the source scalar multiplier `λ` viewed in the canonical one-constraint
--   multiplier space `EuclideanSpace ℝ (Fin 1)`.

/-- The equality-constrained Rosenbrock problem from Chapter12 Exercise 12.1. -/
def rosenbrockExerciseProblem : EqualityConstrainedProblem 2 1 where
  objective x := (1 - x 0) ^ (2 : ℕ)
  constraint _ x := x 1 - (x 0) ^ (2 : ℕ)

/-- The standard Rosenbrock benchmark splits into the Chapter 12 objective and constraint
terms. -/
theorem rosenbrockFunction_eq_constraintSq_add_objective (x : rosenbrockPoint) :
    rosenbrockFunction x =
      100 * (rosenbrockExerciseProblem.constraint 0 x) ^ (2 : ℕ) +
        rosenbrockExerciseProblem.objective x := rfl

/-- The source initial primal point is `(4 / 5, 3 / 5)^T`. -/
def rosenbrockExerciseInitialPoint : rosenbrockPoint :=
  !₂[(4 : ℝ) / 5, (3 : ℝ) / 5]

/-- The source scalar multiplier `λ`, viewed in the canonical one-constraint multiplier space. -/
def rosenbrockExerciseMultiplier (lam : ℝ) : Multiplier :=
  WithLp.toLp 2 ![lam]

@[simp] theorem rosenbrockExerciseMultiplier_apply_zero (lam : ℝ) :
    rosenbrockExerciseMultiplier lam 0 = lam := by
  rfl

@[simp] theorem rosenbrockExerciseMultiplier_zero :
    rosenbrockExerciseMultiplier 0 = 0 := by
  ext i
  fin_cases i
  rfl

/-- The source initial multiplier is `lambda = 1`. -/
def rosenbrockExerciseInitialMultiplier : Multiplier :=
  rosenbrockExerciseMultiplier 1

/-- The source initial state is the pair consisting of the initial point and initial multiplier
from Chapter12 Exercise 12.1. -/
def rosenbrockExerciseInitialState : State :=
  (rosenbrockExerciseInitialPoint, rosenbrockExerciseInitialMultiplier)

/-- The first unit-step iterate after the source initial state is
`((9 / 10, 4 / 5)^T, 0)`. -/
def rosenbrockExerciseFirstIterate : State :=
  (!₂[(9 : ℝ) / 10, (4 : ℝ) / 5], rosenbrockExerciseMultiplier 0)

/-- The second unit-step iterate after the source initial state is
`((1, 99 / 100)^T, 0)`. -/
def rosenbrockExerciseSecondIterate : State :=
  (!₂[(1 : ℝ), (99 : ℝ) / 100], rosenbrockExerciseMultiplier 0)

/-- The third unit-step iterate after the source initial state is `((1, 1)^T, 0)`. -/
def rosenbrockExerciseThirdIterate : State :=
  (!₂[(1 : ℝ), (1 : ℝ)], rosenbrockExerciseMultiplier 0)

/-- The source explicit Exercise 12.1 formula is defined exactly when the scalar denominator
`1 + λ` is nonzero. -/
def rosenbrockExerciseNewtonDefined (lam : Multiplier) : Prop :=
  1 + lam 0 ≠ 0

/-- The source-facing point-direction formula `(dx₁, dx₂)` used in Exercise 12.1.

This keeps the textbook coordinate update
`dx₁ = (1 - x 0) / (1 + λ)` and
`dx₂ = -rosenbrockExerciseProblem.constraint 0 x + 2 * x 0 * dx₁`
as explicit source data. It is intentionally kept source-facing rather than repackaged as a
partial specialization of the Chapter 12 owner `lagrangeNewtonDirectionEquation`. Since Lean
division is total, this declaration records the raw coordinate formula for every multiplier,
while the source side condition `rosenbrockExerciseNewtonDefined lam` is kept separately for
theorems about when the textbook Newton step is defined.
-/
def rosenbrockExercisePointDirection
    (x : rosenbrockPoint) (lam : Multiplier) : rosenbrockPoint :=
  let dx₁ : ℝ := (1 - x 0) / (1 + lam 0)
  let dx₂ : ℝ := -(rosenbrockExerciseProblem.constraint 0 x) + 2 * x 0 * dx₁
  !₂[dx₁, dx₂]

@[simp] theorem rosenbrockExercisePointDirection_apply_zero
    (x : rosenbrockPoint) (lam : Multiplier) :
    rosenbrockExercisePointDirection x lam 0 = (1 - x 0) / (1 + lam 0) := by
  rfl

@[simp] theorem rosenbrockExercisePointDirection_apply_one
    (x : rosenbrockPoint) (lam : Multiplier) :
    rosenbrockExercisePointDirection x lam 1 =
      -(rosenbrockExerciseProblem.constraint 0 x) +
        2 * x 0 * ((1 - x 0) / (1 + lam 0)) := by
  rfl

/-- The source-facing unit-step update used in Chapter 12 Exercise 12.1.

For a state `(x, λ)` with `x = (x 0, x 1)`, this specialized Newton update uses
`dx₁ = (1 - x 0) / (1 + λ)`,
`dx₂ = -rosenbrockExerciseProblem.constraint 0 x + 2 * x 0 * dx₁`, and
`dλ = -λ`, then applies the canonical unit-step Chapter 12 trial update. This declaration is
kept as the explicit source update rather than advertised as a full owner-level specialization
of the Chapter 12 Step-2 residual equation. Since Lean division is total, this declaration is
the totalized coordinate update; the source side condition `rosenbrockExerciseNewtonDefined s.2`
is recorded separately in theorem statements about textbook-defined Newton steps. -/
def rosenbrockExerciseLagrangeNewtonStep (s : State) : State :=
  ( lagrangeNewtonTrialPoint
      s.1
      (rosenbrockExercisePointDirection s.1 s.2)
      1
  , lagrangeNewtonTrialMultiplier
      s.2
      (-s.2)
      1 )

/-- The source initial multiplier satisfies the nonzero-denominator condition `1 + λ ≠ 0`. -/
theorem rosenbrockExerciseInitialState_newtonDefined :
    rosenbrockExerciseNewtonDefined rosenbrockExerciseInitialState.2 := by
  norm_num [rosenbrockExerciseNewtonDefined, rosenbrockExerciseInitialState,
    rosenbrockExerciseInitialMultiplier, rosenbrockExerciseMultiplier]

/-- The first iterate has multiplier `0`, so the next source Newton step is again defined. -/
theorem rosenbrockExerciseFirstIterate_newtonDefined :
    rosenbrockExerciseNewtonDefined rosenbrockExerciseFirstIterate.2 := by
  norm_num [rosenbrockExerciseNewtonDefined, rosenbrockExerciseFirstIterate,
    rosenbrockExerciseMultiplier]

/-- The second iterate has multiplier `0`, so the next source Newton step is again defined. -/
theorem rosenbrockExerciseSecondIterate_newtonDefined :
    rosenbrockExerciseNewtonDefined rosenbrockExerciseSecondIterate.2 := by
  norm_num [rosenbrockExerciseNewtonDefined, rosenbrockExerciseSecondIterate,
    rosenbrockExerciseMultiplier]

/-- Chapter12 Exercise 12.1 (1): the first unit-step Lagrange-Newton iterate for the constrained
Rosenbrock problem with initial state `((4 / 5, 3 / 5)^T, 1)` is
`((9 / 10, 4 / 5)^T, 0)`. -/
theorem rosenbrockExercise_firstIterate :
    rosenbrockExerciseLagrangeNewtonStep rosenbrockExerciseInitialState =
      rosenbrockExerciseFirstIterate := by
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i
    · norm_num [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExercisePointDirection,
        rosenbrockExerciseInitialState, rosenbrockExerciseInitialPoint,
        rosenbrockExerciseInitialMultiplier, rosenbrockExerciseFirstIterate,
        rosenbrockExerciseProblem, lagrangeNewtonTrialPoint]
    · norm_num [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExercisePointDirection,
        rosenbrockExerciseInitialState, rosenbrockExerciseInitialPoint,
        rosenbrockExerciseInitialMultiplier, rosenbrockExerciseFirstIterate,
        rosenbrockExerciseProblem, lagrangeNewtonTrialPoint]
  · ext i
    fin_cases i
    simp [rosenbrockExerciseLagrangeNewtonStep,
      rosenbrockExerciseInitialState, rosenbrockExerciseInitialMultiplier,
      rosenbrockExerciseFirstIterate, lagrangeNewtonTrialMultiplier]

/-- Chapter12 Exercise 12.1 (2): the second unit-step Lagrange-Newton iterate for the constrained
Rosenbrock problem is `((1, 99 / 100)^T, 0)`. -/
theorem rosenbrockExercise_secondIterate :
    rosenbrockExerciseLagrangeNewtonStep rosenbrockExerciseFirstIterate =
      rosenbrockExerciseSecondIterate := by
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i
    · norm_num [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExercisePointDirection,
        rosenbrockExerciseFirstIterate,
        rosenbrockExerciseSecondIterate,
        rosenbrockExerciseProblem, lagrangeNewtonTrialPoint]
    · norm_num [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExercisePointDirection,
        rosenbrockExerciseFirstIterate,
        rosenbrockExerciseSecondIterate,
        rosenbrockExerciseProblem, lagrangeNewtonTrialPoint]
  · ext i
    fin_cases i
    simp [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExerciseFirstIterate,
      rosenbrockExerciseSecondIterate, lagrangeNewtonTrialMultiplier]

/-- Chapter12 Exercise 12.1 (3): the third unit-step Lagrange-Newton iterate for the constrained
Rosenbrock problem is `((1, 1)^T, 0)`. -/
theorem rosenbrockExercise_thirdIterate :
    rosenbrockExerciseLagrangeNewtonStep rosenbrockExerciseSecondIterate =
      rosenbrockExerciseThirdIterate := by
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i
    · norm_num [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExercisePointDirection,
        rosenbrockExerciseSecondIterate,
        rosenbrockExerciseThirdIterate,
        rosenbrockExerciseProblem, lagrangeNewtonTrialPoint]
    · norm_num [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExercisePointDirection,
        rosenbrockExerciseSecondIterate,
        rosenbrockExerciseThirdIterate,
        rosenbrockExerciseProblem, lagrangeNewtonTrialPoint]
  · ext i
    fin_cases i
    simp [rosenbrockExerciseLagrangeNewtonStep, rosenbrockExerciseSecondIterate,
      rosenbrockExerciseThirdIterate, lagrangeNewtonTrialMultiplier]
