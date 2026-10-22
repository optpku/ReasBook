/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_3_extra_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open scoped BigOperators Gradient

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * `InteriorPointPenaltyProblem` in `Definition_10_3_extra_1` is the chapter's core owner for
--   interior-point objective/constraint/barrier data.
-- * `InteriorPointPenaltyProblem.strictFeasibleSet` and `.barrierSum` are the canonical derived
--   strict-feasibility and barrier-budget surfaces in this domain.
-- * `InteriorPointPenaltyFunctionMethod` in `Algorithm_10_3_3` and `Theorem_10_3_4` already
--   reuses those same strict-feasible and barrier-sum ideas downstream.
-- This file therefore keeps the Newton-system data source-facing, but reuses the existing
-- interior-point owner for the strict-feasible and log-barrier-sum surfaces instead of
-- duplicating them locally.

/-- A matrix field `H` represents the Hessian of `f` when it gives the Fréchet derivative of
`∇ f` at each point. -/
def IsHessianMatrixField (f : Point → ℝ) (H : Point → MatrixN) : Prop :=
  ∀ x,
    HasFDerivAt (∇ f)
      (((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (H x)))
      x

/-- The logarithmic barrier `c ↦ log (1 / c)` diverges to `+∞` as `c → 0+`. -/
theorem logBarrier_large_near_zero :
    ∀ R : ℝ, ∃ δ > 0, ∀ ⦃c : ℝ⦄, 0 < c → c < δ → R < Real.log (1 / c) := by
  intro R
  refine ⟨Real.exp (-R), Real.exp_pos _, ?_⟩
  intro c hc hδ
  have h_inv : Real.exp R < 1 / c := by
    have h' : 1 / Real.exp (-R) < 1 / c :=
      one_div_lt_one_div_of_lt hc hδ
    simpa [one_div, Real.exp_neg] using h'
  simpa using Real.log_lt_log (Real.exp_pos R) h_inv

/-- The logarithmic barrier `c ↦ log (1 / c)` is antitone on the positive half-line. -/
theorem logBarrier_antitone
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (h : c₁ < c₂) :
    Real.log (1 / c₂) ≤ Real.log (1 / c₁) := by
  have h_inv : 1 / c₂ < 1 / c₁ :=
    one_div_lt_one_div_of_lt hc₁ h
  exact le_of_lt <| Real.log_lt_log (one_div_pos.2 <| lt_trans hc₁ h) h_inv

/-- The stage multiplier in Algorithm 10.3.5 is
`λᵢ = 1 / (σ * cᵢ(x))`. -/
def logBarrierMultiplier
    (constraint : Fin m → Point → ℝ) (σ : ℝ) (x : Point) (i : Fin m) : ℝ :=
  1 / (σ * constraint i x)

/-- The Newton-system matrix in formula `(10.3.42)` for the inexact log-barrier method. -/
def logBarrierNewtonMatrix
    (constraint : Fin m → Point → ℝ)
    (objectiveHessian : Point → MatrixN)
    (constraintHessian : Fin m → Point → MatrixN)
    (σ : ℝ) (x : Point) : MatrixN :=
  objectiveHessian x -
    ∑ i : Fin m, logBarrierMultiplier constraint σ x i • constraintHessian i x +
    ∑ i : Fin m,
      ((logBarrierMultiplier constraint σ x i) / constraint i x) •
        Matrix.vecMulVec
          ((EuclideanSpace.equiv (Fin n) ℝ) (((∇ (constraint i) : Point → Point) x)))
          ((EuclideanSpace.equiv (Fin n) ℝ) (((∇ (constraint i) : Point → Point) x)))

/-- The Newton matrix in formula `(10.3.42)` is nonsingular when its determinant is a unit. -/
def logBarrierNewtonMatrixNonsingular
    (constraint : Fin m → Point → ℝ)
    (objectiveHessian : Point → MatrixN)
    (constraintHessian : Fin m → Point → MatrixN)
    (σ : ℝ) (x : Point) : Prop :=
  IsUnit (logBarrierNewtonMatrix constraint objectiveHessian constraintHessian σ x).det

/-- The right-hand side in formula `(10.3.42)` is
`∇ f(x) - ∑ i, λᵢ ∇ cᵢ(x)`. -/
def logBarrierNewtonResidual
    (objective : Point → ℝ) (constraint : Fin m → Point → ℝ)
    (σ : ℝ) (x : Point) : Point :=
  ((∇ objective : Point → Point) x) -
    ∑ i : Fin m, (logBarrierMultiplier constraint σ x i) • (((∇ (constraint i) : Point → Point) x))

/-- The search direction in Algorithm 10.3.5 is the negative inverse Newton matrix applied to
the log-barrier residual from `(10.3.42)`. -/
def logBarrierDirection
    (objective : Point → ℝ) (constraint : Fin m → Point → ℝ)
    (objectiveHessian : Point → MatrixN)
    (constraintHessian : Fin m → Point → MatrixN)
    (σ : ℝ) (x : Point) : Point :=
  -(Matrix.toEuclideanLin
      ((logBarrierNewtonMatrix constraint objectiveHessian constraintHessian σ x)⁻¹)
      (logBarrierNewtonResidual objective constraint σ x))

/-- The feasible Step-3 steplengths along the trial ray `x + β • d` are the `β ∈ [0, 1]`
for which every inequality constraint remains weakly feasible. -/
def feasibleStepSet
    (constraint : Fin m → Point → ℝ) (x d : Point) : Set ℝ :=
  {β | β ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ i : Fin m, 0 ≤ constraint i (x + β • d)}

/-- The Step-3 steplength rule in Algorithm 10.3.5 either accepts the full Newton step when
`x + d` stays strictly interior, or chooses the maximal feasible `ᾱ ∈ (0, 1]` on the trial ray,
with `x + ᾱ • d` on the feasible-region boundary, and then sets `α = (9 / 10) * ᾱ`. -/
inductive LogBarrierStepSizeCase
    (constraint : Fin m → Point → ℝ)
    (x d : Point) (α : ℝ) : Prop where
  | fullStep
      (h_eq : α = 1)
      (h_strictInterior : ∀ i : Fin m, 0 < constraint i (x + d)) :
      LogBarrierStepSizeCase constraint x d α
  | boundaryStep
      (alphaBar : ℝ)
      (h_not_strictInterior : ¬ ∀ i : Fin m, 0 < constraint i (x + d))
      (h_mem : alphaBar ∈ Set.Ioc (0 : ℝ) 1)
      (h_isGreatest : IsGreatest (feasibleStepSet constraint x d) alphaBar)
      (h_boundary : ∃ i : Fin m, constraint i (x + alphaBar • d) = 0)
      (h_eq : α = (9 / 10 : ℝ) * alphaBar) :
      LogBarrierStepSizeCase constraint x d α

/-- A Step-2 state of Algorithm 10.3.5 records the current iterate `x`, the current penalty
parameter `σ`, and the Newton direction `d` computed from formula `(10.3.42)` at `(x, σ)`. -/
structure InexactLogBarrierStageState (n m : ℕ) where
  iterate : EuclideanSpace ℝ (Fin n)
  penaltyParameter : ℝ
  direction : EuclideanSpace ℝ (Fin n)

namespace InexactLogBarrierStageState

/-- The Step-4 iterate update attached to `state` and steplength `α` is `x + α • d`. -/
def nextIterate (state : InexactLogBarrierStageState n m) (α : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  state.iterate + α • state.direction

/-- Evaluating `state.nextIterate α` expands to the Step-4 update `x + α • d`. -/
theorem nextIterate_eq
    (state : InexactLogBarrierStageState n m) (α : ℝ) :
    state.nextIterate α = state.iterate + α • state.direction :=
  rfl

end InexactLogBarrierStageState

/-- Chapter10 Algorithm 10.3.5: an inexact log-barrier function method records an objective
`f`, inequality constraints `cᵢ`, explicit Hessian matrix fields for `f` and the `cᵢ`, a
tolerance `ε ≥ 0`, an initial point `x₁` together with an explicit field
`initialState_satisfies10315` formalizing the source side condition `(10.3.15)` as strict
interiority, and an initial barrier parameter `σ₁ > 0`, packaged as an explicit initial Step-2
state carrying `x₁`, `σ₁`, and the Newton direction from `(10.3.42)`. The dynamic part of the
source algorithm is exposed through `IsStageState`, `StepSizeSpec`, and `Transition`:
`IsStageState` says that a state is strictly interior, has positive penalty parameter, has a
nonsingular Newton matrix, and records the exact direction formula `(10.3.42)`; `StepSizeSpec`
encodes Step 3; and `Transition` separates the four textbook Step-2/Step-4 branches, including
the same-stage update `σ := 10 * σ` with unchanged `x` before recomputation at the same textbook
stage. -/
structure InexactLogBarrierFunctionMethod (n m : ℕ) where
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  constraint : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  objectiveHessian : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ
  constraintHessian :
    Fin m → EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ
  objective_hessian : IsHessianMatrixField objective objectiveHessian
  constraint_hessian : ∀ i : Fin m, IsHessianMatrixField (constraint i) (constraintHessian i)
  tolerance : ℝ
  toleranceNonneg : 0 ≤ tolerance
  initialState : InexactLogBarrierStageState n m
  /-- The source initial-point side condition `(10.3.15)` is recorded here as strict
  interiority of `x₁` for the inequalities `cᵢ(x) ≥ 0`. -/
  initialState_satisfies10315 :
    ∀ i : Fin m, 0 < constraint i initialState.iterate
  initialPenaltyParameterPos : 0 < initialState.penaltyParameter
  initialNewtonMatrix_nonsingular :
    logBarrierNewtonMatrixNonsingular
      constraint
      objectiveHessian
      constraintHessian
      initialState.penaltyParameter
      initialState.iterate
  initialDirection_eq :
    initialState.direction =
      logBarrierDirection
        objective
        constraint
        objectiveHessian
        constraintHessian
        initialState.penaltyParameter
        initialState.iterate

namespace InexactLogBarrierFunctionMethod

/-- An inexact log-barrier function method can be viewed as its initial Step-2 state. -/
instance : Coe (InexactLogBarrierFunctionMethod n m) (InexactLogBarrierStageState n m) where
  coe method := method.initialState

/-- Forgetting the Newton data turns an inexact log-barrier method into the chapter's canonical
interior-point penalty owner with the fixed logarithmic barrier `c ↦ log (1 / c)`. -/
def toInteriorPointPenaltyProblem
    (method : InexactLogBarrierFunctionMethod n m) :
    InteriorPointPenaltyProblem Point (Fin m) where
  objective := method.objective
  constraint := method.constraint
  strictFeasibleSet_nonempty := ⟨method.initialState.iterate, method.initialState_satisfies10315⟩
  barrier := fun c ↦ Real.log (1 / c)
  barrier_large_near_zero := logBarrier_large_near_zero
  barrier_antitone := by
    intro c₁ c₂ hc₁ h
    exact logBarrier_antitone hc₁ h

/-- The recorded initial point satisfies the source side condition `(10.3.15)`, formalized here
as strict interiority for the inequalities `cᵢ(x) ≥ 0`. -/
theorem initialPoint_satisfies10315
    (method : InexactLogBarrierFunctionMethod n m) :
    method.initialState.iterate ∈ method.toInteriorPointPenaltyProblem.strictFeasibleSet := by
  -- Rewrite strict-feasible membership and unfold the owner projection to recover the stored
  -- pointwise positivity condition on `method.constraint`.
  simpa [toInteriorPointPenaltyProblem, InteriorPointPenaltyProblem.mem_strictFeasibleSet_iff] using
    method.initialState_satisfies10315

/-- A state is a valid Step-2 state for `method` when it is strictly interior, has positive
penalty parameter, has a nonsingular Newton matrix, and records the exact direction formula
`(10.3.42)`. -/
def IsStageState
    (method : InexactLogBarrierFunctionMethod n m)
    (state : InexactLogBarrierStageState n m) : Prop :=
  state.iterate ∈ method.toInteriorPointPenaltyProblem.strictFeasibleSet ∧
    0 < state.penaltyParameter ∧
    logBarrierNewtonMatrixNonsingular
      method.constraint
      method.objectiveHessian
      method.constraintHessian
      state.penaltyParameter
      state.iterate ∧
    state.direction =
      logBarrierDirection
        method.objective
        method.constraint
        method.objectiveHessian
        method.constraintHessian
        state.penaltyParameter
        state.iterate

/-- Unfolding `method.IsStageState state` gives the strict-interiority, positivity,
nonsingularity, and direction-formula requirements from Step 2. -/
theorem isStageState_iff
    (method : InexactLogBarrierFunctionMethod n m)
    (state : InexactLogBarrierStageState n m) :
    method.IsStageState state ↔
      state.iterate ∈ method.toInteriorPointPenaltyProblem.strictFeasibleSet ∧
        0 < state.penaltyParameter ∧
        logBarrierNewtonMatrixNonsingular
          method.constraint
          method.objectiveHessian
          method.constraintHessian
          state.penaltyParameter
          state.iterate ∧
        state.direction =
          logBarrierDirection
            method.objective
            method.constraint
            method.objectiveHessian
            method.constraintHessian
            state.penaltyParameter
            state.iterate := by
  -- This theorem is the direct definitional expansion of `IsStageState`.
  rfl

/-- The recorded initial Step-2 state satisfies the Step-2 validity conditions. -/
theorem initialState_isStageState
    (method : InexactLogBarrierFunctionMethod n m) :
    method.IsStageState method.initialState := by
  -- Assemble the four Step-2 obligations from the fields recorded in the method package.
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact method.initialPoint_satisfies10315
  · exact method.initialPenaltyParameterPos
  · exact method.initialNewtonMatrix_nonsingular
  · exact method.initialDirection_eq

/-- The initial Newton matrix from `(10.3.42)` is explicitly assumed nonsingular, so the
initial matrix inverse is well defined. -/
theorem initialNewtonMatrix_nonsingularAt
    (method : InexactLogBarrierFunctionMethod n m) :
    logBarrierNewtonMatrixNonsingular
      method.constraint
      method.objectiveHessian
      method.constraintHessian
      method.initialState.penaltyParameter
      method.initialState.iterate := by
  -- Project the stored nonsingularity assumption from the method data.
  simpa using method.initialNewtonMatrix_nonsingular

/-- The recorded initial direction is exactly the search direction from formula `(10.3.42)`. -/
theorem initialDirection_eq_formula
    (method : InexactLogBarrierFunctionMethod n m) :
    method.initialState.direction =
      logBarrierDirection
        method.objective
        method.constraint
        method.objectiveHessian
        method.constraintHessian
        method.initialState.penaltyParameter
        method.initialState.iterate := by
  -- Project the stored Step-2 direction formula from the method data.
  simpa using method.initialDirection_eq

/-- The Step-3 steplength rule for a valid state of Algorithm 10.3.5 requires `d ≠ 0` and
then applies the source full-step/boundary-step alternative. -/
def StepSizeSpec
    (method : InexactLogBarrierFunctionMethod n m)
    (state : InexactLogBarrierStageState n m) (α : ℝ) : Prop :=
  state.direction ≠ 0 ∧
    LogBarrierStepSizeCase method.constraint state.iterate state.direction α

/-- Unfolding `method.StepSizeSpec state α` gives the source Step-3 conditions. -/
theorem stepSizeSpec_iff
    (method : InexactLogBarrierFunctionMethod n m)
    (state : InexactLogBarrierStageState n m) (α : ℝ) :
    method.StepSizeSpec state α ↔
      state.direction ≠ 0 ∧
        LogBarrierStepSizeCase method.constraint state.iterate state.direction α := by
  -- This theorem is the direct definitional expansion of `StepSizeSpec`.
  rfl

/-- The Step-4 stopping test is the same scaled barrier-budget inequality as in
Algorithm 10.3.3, evaluated at the updated point `x + α • d`. -/
def terminatedAtNextIterate
    (method : InexactLogBarrierFunctionMethod n m)
    (state : InexactLogBarrierStageState n m) (α : ℝ) : Prop :=
  (1 / state.penaltyParameter) *
      method.toInteriorPointPenaltyProblem.barrierSum (state.nextIterate α) ≤
    method.tolerance

/-- Unfolding `method.terminatedAtNextIterate state α` gives the source Step-4 stopping test at
the updated iterate `x + α • d`. -/
theorem terminatedAtNextIterate_iff
    (method : InexactLogBarrierFunctionMethod n m)
    (state : InexactLogBarrierStageState n m) (α : ℝ) :
    method.terminatedAtNextIterate state α ↔
      (1 / state.penaltyParameter) *
          method.toInteriorPointPenaltyProblem.barrierSum (state.nextIterate α) ≤
        method.tolerance :=
  Iff.rfl

/-- The four outcomes of processing a textbook stage of Algorithm 10.3.5: Step-2 stop,
same-stage penalty increase and recomputation, Step-4 stop after updating `x`, or Step-4
continuation to the next textbook stage with updated `x` and `σ`. -/
inductive TransitionResult (n m : ℕ) where
  | stationaryStop
  | stationaryIncreasePenalty (nextState : InexactLogBarrierStageState n m)
  | movingStop (stepSize : ℝ) (nextIterate : EuclideanSpace ℝ (Fin n))
  | movingIncreasePenalty
      (stepSize : ℝ) (nextState : InexactLogBarrierStageState n m)

namespace TransitionResult

/-- A transition result is terminating exactly in the Step-2 stationary-stop branch or the
Step-4 budget-stop branch. -/
def terminates (result : TransitionResult n m) : Prop :=
  match result with
  | .stationaryStop => True
  | .stationaryIncreasePenalty _ => False
  | .movingStop _ _ => True
  | .movingIncreasePenalty _ _ => False

/-- Unfolding `result.terminates` separates the two stopping branches from the two continuing
branches in Algorithm 10.3.5. -/
theorem terminates_iff
    (result : TransitionResult n m) :
    result.terminates ↔
      result = .stationaryStop ∨ ∃ α x', result = .movingStop α x' := by
  -- Separate the four constructors; each branch is decided by the definition of `terminates`.
  cases result <;> simp [terminates]

end TransitionResult

/-- `Transition method k state k' result` encodes one Step-2/Step-4 branch of
Algorithm 10.3.5 from the stage-`k` Step-2 state `state`. The same-stage penalty update keeps
the stage index equal to `k`, while each Step-4 branch records the updated iterate at stage
`k + 1`. -/
inductive Transition
    (method : InexactLogBarrierFunctionMethod n m)
    (k : ℕ) (state : InexactLogBarrierStageState n m) :
    ℕ → TransitionResult n m → Prop where
  | stationaryStop
      (hk : 1 ≤ k)
      (h_state : method.IsStageState state)
      (h_direction : state.direction = 0)
      (h_gradient :
        ‖((∇ method.objective : Point → Point) state.iterate)‖ ≤ method.tolerance) :
      Transition method k state k TransitionResult.stationaryStop
  | stationaryIncreasePenalty
      (hk : 1 ≤ k)
      (h_state : method.IsStageState state)
      (h_direction : state.direction = 0)
      (h_not_gradient :
        ¬ (‖((∇ method.objective : Point → Point) state.iterate)‖ ≤ method.tolerance))
      (nextState : InexactLogBarrierStageState n m)
      (h_iterate : nextState.iterate = state.iterate)
      (h_penalty : nextState.penaltyParameter = 10 * state.penaltyParameter)
      (h_nextState : method.IsStageState nextState) :
      Transition method k state k
        (TransitionResult.stationaryIncreasePenalty nextState)
  | movingStop
      (hk : 1 ≤ k)
      (h_state : method.IsStageState state)
      (α : ℝ)
      (h_stepSize : method.StepSizeSpec state α)
      (h_budget : method.terminatedAtNextIterate state α) :
      Transition method k state (k + 1)
        (TransitionResult.movingStop α (state.nextIterate α))
  | movingIncreasePenalty
      (hk : 1 ≤ k)
      (h_state : method.IsStageState state)
      (α : ℝ)
      (h_stepSize : method.StepSizeSpec state α)
      (h_not_budget : ¬ method.terminatedAtNextIterate state α)
      (nextState : InexactLogBarrierStageState n m)
      (h_iterate : nextState.iterate = state.nextIterate α)
      (h_penalty : nextState.penaltyParameter = 10 * state.penaltyParameter)
      (h_nextState : method.IsStageState nextState) :
      Transition method k state (k + 1)
        (TransitionResult.movingIncreasePenalty α nextState)

end InexactLogBarrierFunctionMethod

#print axioms InexactLogBarrierFunctionMethod.toInteriorPointPenaltyProblem
#print axioms logBarrierNewtonMatrix
#print axioms logBarrierDirection

end
