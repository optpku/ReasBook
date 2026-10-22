/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

public section

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "EqualityPoint" => EuclideanSpace ℝ (Fin me)
local notation "InequalityPoint" => EuclideanSpace ℝ (Fin mi)
local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "EqualityMatrix" => Matrix (Fin n) (Fin me) ℝ
local notation "InequalityMatrix" => Matrix (Fin n) (Fin mi) ℝ

-- Semantic recall: `lean_leansearch` surfaced only generic radius and norm APIs, not a reusable
-- owner for this linearly constrained trust-region method. This file therefore keeps the linear
-- constraint data, the `ℓ∞` radius test, the acceptance ratio, and the Step 2-5 transition
-- clauses explicit on a source-facing algorithm owner.

/-- A linearly constrained problem on `ℝ^n`, with equality constraints
`Aeqᵀ x = beq` and inequality constraints `bineq ≤ Aineqᵀ x`. -/
structure LinearTrustRegionProblem (n me mi : ℕ) where
  objective : EuclideanSpace ℝ (Fin n) → ℝ
  equalityMatrix : Matrix (Fin n) (Fin me) ℝ
  equalityRhs : EuclideanSpace ℝ (Fin me)
  inequalityMatrix : Matrix (Fin n) (Fin mi) ℝ
  inequalityRhs : EuclideanSpace ℝ (Fin mi)

/-- The equality-constraint values `Aeqᵀ x` of a linearly constrained problem. -/
def LinearTrustRegionProblem.equalityValues
    (problem : LinearTrustRegionProblem n me mi) (x : Point) : EqualityPoint :=
  let equalityMatrix := problem.equalityMatrix
  WithLp.toLp 2 (equalityMatrix.transpose.mulVec x.ofLp)

/-- The inequality-constraint values `Aineqᵀ x` of a linearly constrained problem. -/
def LinearTrustRegionProblem.inequalityValues
    (problem : LinearTrustRegionProblem n me mi) (x : Point) : InequalityPoint :=
  let inequalityMatrix := problem.inequalityMatrix
  WithLp.toLp 2 (inequalityMatrix.transpose.mulVec x.ofLp)

/-- The feasible set of a linearly constrained problem consists of the points satisfying the
source linear equalities exactly and the source linear inequalities weakly. -/
def LinearTrustRegionProblem.feasibleSet
    (problem : LinearTrustRegionProblem n me mi) : Set Point :=
  {x |
    problem.equalityValues x = problem.equalityRhs ∧
      ∀ i : Fin mi, problem.inequalityRhs i ≤ problem.inequalityValues x i}

namespace LinearTrustRegionProblem

/-- Unfolding `problem.feasibleSet` gives the source coordinatewise equality and inequality
constraints. -/
theorem mem_feasibleSet_iff
    (problem : LinearTrustRegionProblem n me mi) (x : Point) :
    x ∈ problem.feasibleSet ↔
      problem.equalityValues x = problem.equalityRhs ∧
        ∀ i : Fin mi, problem.inequalityRhs i ≤ problem.inequalityValues x i :=
  Iff.rfl

end LinearTrustRegionProblem

/-- The source `ℓ∞` norm of a trust-region step in `ℝ^n`. -/
def linftyPointNorm (x : Point) : ℝ :=
  ‖WithLp.toLp (⊤ : ENNReal) x.ofLp‖

#print axioms LinearTrustRegionProblem.equalityValues
#print axioms LinearTrustRegionProblem.inequalityValues
#print axioms LinearTrustRegionProblem.feasibleSet
#print axioms linftyPointNorm

/-- A state of Algorithm 13.2.1 records the iterate `x_k`, the Hessian approximation `B_k`, and
the trust-region radius `Delta_k > 0`. -/
structure LinearTrustRegionState (n : ℕ) where
  iterate : EuclideanSpace ℝ (Fin n)
  hessianApproximation : Matrix (Fin n) (Fin n) ℝ
  radius : ℝ
  radius_pos : 0 < radius

/-- A trust-region step `d` is feasible at `state` when the trial point `x_k + d` remains
feasible for `problem` and the source bound `‖d‖_∞ ≤ Delta_k` holds. -/
def linearTrustRegionStageFeasible
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | state.iterate + d ∈ problem.feasibleSet ∧ linftyPointNorm d ≤ state.radius}

/-- A step belongs to `linearTrustRegionStageFeasible problem state` exactly when its trial point
is feasible and its `ℓ∞` norm stays below the current trust-region radius. -/
theorem mem_linearTrustRegionStageFeasible_iff
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n)
    (d : EuclideanSpace ℝ (Fin n)) :
    d ∈ linearTrustRegionStageFeasible problem state ↔
      state.iterate + d ∈ problem.feasibleSet ∧ linftyPointNorm d ≤ state.radius :=
  Iff.rfl

/-- The Step-2 trust-region model at `state`, with explicit first-order term `g_k` and Hessian
approximation `B_k`, is the quadratic model based at the current objective value
`f(x_k)`. -/
def linearTrustRegionStageObjective
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n)
    (gradient : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun d ↦
    problem.objective state.iterate +
      dotProduct gradient d +
      (1 / 2 : ℝ) *
        dotProduct d (WithLp.toLp 2 (state.hessianApproximation.mulVec d.ofLp))

#print axioms linearTrustRegionStageFeasible
#print axioms linearTrustRegionStageObjective

/-- A Step-2 subproblem solution records the current model gradient together with a selected
minimizer `d_k` of the trust-region subproblem determined by the current `problem` and
`state`. -/
structure LinearTrustRegionSubproblemSolution
    {n me mi : ℕ}
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n) where
  modelGradient : EuclideanSpace ℝ (Fin n)
  direction : EuclideanSpace ℝ (Fin n)
  trialPoint_feasible : state.iterate + direction ∈ problem.feasibleSet
  radius_bound : linftyPointNorm direction ≤ state.radius
  direction_minimizes :
    ∀ d : EuclideanSpace ℝ (Fin n),
      d ∈ linearTrustRegionStageFeasible problem state →
        linearTrustRegionStageObjective problem state modelGradient direction ≤
          linearTrustRegionStageObjective problem state modelGradient d

namespace LinearTrustRegionSubproblemSolution

/-- The chosen Step-2 direction in a subproblem solution is a feasible trust-region step for the
current stage. -/
theorem direction_mem_stageFeasible
    {n me mi : ℕ}
    {problem : LinearTrustRegionProblem n me mi}
    {state : LinearTrustRegionState n}
    (subproblem : LinearTrustRegionSubproblemSolution problem state) :
    subproblem.direction ∈ linearTrustRegionStageFeasible problem state :=
  ⟨subproblem.trialPoint_feasible, subproblem.radius_bound⟩

end LinearTrustRegionSubproblemSolution

/-- The actual reduction in `(13.2.8)` is the decrease in the fixed problem objective obtained
by the Step-2 trial point `x_k + d_k`. -/
def linearTrustRegionActualReduction
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n)
    (direction : EuclideanSpace ℝ (Fin n)) : ℝ :=
  problem.objective state.iterate - problem.objective (state.iterate + direction)

/-- The predicted reduction in `(13.2.8)` is the decrease of the current trust-region model from
the zero step to the chosen Step-2 direction `d_k`. -/
def linearTrustRegionPredictedReduction
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n)
    (subproblem : LinearTrustRegionSubproblemSolution problem state) : ℝ :=
  linearTrustRegionStageObjective problem state subproblem.modelGradient 0 -
    linearTrustRegionStageObjective
      problem
      state
      subproblem.modelGradient
      subproblem.direction

#print axioms linearTrustRegionActualReduction
#print axioms linearTrustRegionPredictedReduction

/-- The Step-2 acceptance ratio `r_k` from `(13.2.8)` is the quotient of the actual reduction by
the predicted reduction for the chosen trust-region step `d_k`. -/
def linearTrustRegionAcceptanceRatio
    {n me mi : ℕ}
    (problem : LinearTrustRegionProblem n me mi)
    (state : LinearTrustRegionState n)
    (subproblem : LinearTrustRegionSubproblemSolution problem state) : ℝ :=
  linearTrustRegionActualReduction problem state subproblem.direction /
    linearTrustRegionPredictedReduction problem state subproblem

/-- The accepted next iterate `x_(k+1)` follows the source rule `x_(k+1) = x_k + d_k` when
`r_k > 0` and `x_(k+1) = x_k` otherwise. -/
def linearTrustRegionNextIterate
    {n : ℕ}
    (state : LinearTrustRegionState n)
    (direction : EuclideanSpace ℝ (Fin n))
    (ratio : ℝ) : EuclideanSpace ℝ (Fin n) :=
  if 0 < ratio then state.iterate + direction else state.iterate

/-- The Step-3/Step-4 radius update gives the next trust-region radius `Delta_(k+1)` using the
source thresholds `0.25`, `0.75`, and the `ℓ∞` boundary test `‖d_k‖_∞ < Delta_k`. -/
def linearTrustRegionNextRadius
    {n : ℕ}
    (state : LinearTrustRegionState n)
    (direction : EuclideanSpace ℝ (Fin n))
    (ratio : ℝ) : ℝ :=
  if ratio < (1 / 4 : ℝ) then
    state.radius / 2
  else if ratio < (3 / 4 : ℝ) ∨ linftyPointNorm direction < state.radius then
    state.radius
  else
    2 * state.radius

/-- Chapter13 Algorithm 13.2.1: a trust-region method for linearly constrained problems. The
method records a fixed linearly constrained problem, an initial feasible point `x_1`, an
initial Hessian approximation `B_1`, an initial radius `Delta_1 > 0`, and a tolerance
`epsilon ≥ 0`. For each active stage `k ≥ 1`, Step 2 records a solution `d_k` of the current
trust-region subproblem, stops exactly when `‖d_k‖ ≤ epsilon`, and otherwise records the ratio
`r_k` from `(13.2.8)`, the point update
`x_(k+1) = x_k + d_k` if `r_k > 0` and `x_(k+1) = x_k` otherwise, the Step-3/Step-4 radius
update with thresholds `0.25` and `0.75` and the boundary test `‖d_k‖_∞ < Delta_k`, and a
next Hessian approximation `B_(k+1)` satisfying the recorded update rule. -/
structure LinearTrustRegionMethod (n me mi : ℕ) where
  problem : LinearTrustRegionProblem n me mi
  tolerance : ℝ
  tolerance_nonneg : 0 ≤ tolerance
  initialState : LinearTrustRegionState n
  initialPoint_feasible : initialState.iterate ∈ problem.feasibleSet
  active : ℕ → Prop
  stageState : ℕ → LinearTrustRegionState n
  stageSubproblem :
    ∀ k : ℕ, LinearTrustRegionSubproblemSolution problem (stageState k)
  stageStops : ℕ → Prop
  stageStops_iff :
    ∀ k : ℕ, active k →
      stageStops k ↔ ‖(stageSubproblem k).direction‖ ≤ tolerance
  stageNextState :
    ∀ (k : ℕ) (_ : active k) (_ : ¬ stageStops k), LinearTrustRegionState n
  stageNextIterate_eq :
    ∀ (k : ℕ) (hk : active k) (hcontinue : ¬ stageStops k),
      (stageNextState k hk hcontinue).iterate =
        linearTrustRegionNextIterate
          (stageState k)
          (stageSubproblem k).direction
          (linearTrustRegionAcceptanceRatio problem (stageState k) (stageSubproblem k))
  stageNextRadius_eq :
    ∀ (k : ℕ) (hk : active k) (hcontinue : ¬ stageStops k),
      (stageNextState k hk hcontinue).radius =
        linearTrustRegionNextRadius
          (stageState k)
          (stageSubproblem k).direction
          (linearTrustRegionAcceptanceRatio problem (stageState k) (stageSubproblem k))
  hessianUpdateRule :
    ℕ →
      Matrix (Fin n) (Fin n) ℝ →
        Matrix (Fin n) (Fin n) ℝ →
          Prop
  active_one : active 1
  active_pos : ∀ k : ℕ, active k → 1 ≤ k
  stageState_one : stageState 1 = initialState
  feasible_stage :
    ∀ k : ℕ, active k → (stageState k).iterate ∈ problem.feasibleSet
  active_succ_iff :
    ∀ k : ℕ, 1 ≤ k → active (k + 1) ↔ active k ∧ ¬ stageStops k
  stageState_succ :
    ∀ (k : ℕ) (hk : active k) (hcontinue : ¬ stageStops k),
      stageState (k + 1) = stageNextState k hk hcontinue
  hessian_update_spec :
    ∀ (k : ℕ) (hk : active k) (hcontinue : ¬ stageStops k),
      hessianUpdateRule
        k
        (stageState k).hessianApproximation
        (stageNextState k hk hcontinue).hessianApproximation

namespace LinearTrustRegionMethod

/-- A linearly constrained trust-region method canonically coerces to its underlying problem. -/
instance instCoeLinearTrustRegionProblem :
    Coe (LinearTrustRegionMethod n me mi) (LinearTrustRegionProblem n me mi) where
  coe := LinearTrustRegionMethod.problem

/-- At every recorded stage, the stored Step-2 subproblem solution provides a feasible
trust-region step for the current iterate and radius. -/
theorem stageSubproblem_direction_mem_stageFeasible
    (method : LinearTrustRegionMethod n me mi) (k : ℕ) :
    (method.stageSubproblem k).direction ∈
      linearTrustRegionStageFeasible method.problem (method.stageState k) :=
  (method.stageSubproblem k).direction_mem_stageFeasible

/-- On a nonterminal stage, the next iterate recorded by Algorithm 13.2.1 is the source update
determined by the acceptance ratio `r_k` and the Step-2 direction `d_k`. -/
theorem stageState_succ_iterate_eq
    (method : LinearTrustRegionMethod n me mi)
    (k : ℕ) (hk : method.active k) (hcontinue : ¬ method.stageStops k) :
    (method.stageState (k + 1)).iterate =
      linearTrustRegionNextIterate
        (method.stageState k)
        (method.stageSubproblem k).direction
        (linearTrustRegionAcceptanceRatio
          method.problem
          (method.stageState k)
          (method.stageSubproblem k)) := by
  rw [method.stageState_succ k hk hcontinue, method.stageNextIterate_eq k hk hcontinue]

/-- On a nonterminal stage, the next trust-region radius recorded by Algorithm 13.2.1 is the
source Step-3/Step-4 update determined by `r_k` and the boundary test on `d_k`. -/
theorem stageState_succ_radius_eq
    (method : LinearTrustRegionMethod n me mi)
    (k : ℕ) (hk : method.active k) (hcontinue : ¬ method.stageStops k) :
    (method.stageState (k + 1)).radius =
      linearTrustRegionNextRadius
        (method.stageState k)
        (method.stageSubproblem k).direction
        (linearTrustRegionAcceptanceRatio
          method.problem
          (method.stageState k)
          (method.stageSubproblem k)) := by
  rw [method.stageState_succ k hk hcontinue, method.stageNextRadius_eq k hk hcontinue]

end LinearTrustRegionMethod

end
