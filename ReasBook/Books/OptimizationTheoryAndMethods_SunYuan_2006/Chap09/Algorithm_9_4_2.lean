/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

open Matrix

noncomputable section

section Chapter09Algorithm942

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "EqMultiplier" => EuclideanSpace ℝ (Fin me)
local notation "IneqMultiplier" => EuclideanSpace ℝ (Fin mi)

-- This file reuses the Chapter 9 quadratic-program owner from
-- `Definition_9_1_extra_1` and adds the source-facing Algorithm 9.4.2 working-set API.

namespace QuadraticProgram

/-- The active inequality set `I(x)` of `P` consists of the inequality indices where
`Aineq x = bineq`. -/
def activeSet (P : QuadraticProgram n me mi) (x : Point) : Finset (Fin mi) :=
  Finset.univ.filter fun i ↦ (P.Aineq.mulVec x) i = P.bineq i

/-- Membership in `P.activeSet x` means that the `i`-th inequality constraint is active at `x`. -/
theorem mem_activeSet_iff (P : QuadraticProgram n me mi) (x : Point) (i : Fin mi) :
    i ∈ P.activeSet x ↔ (P.Aineq.mulVec x) i = P.bineq i := by
  simp [activeSet]

/-- The working-set feasible directions are the directions `d` satisfying the equality
constraints and the currently active inequality constraints as equalities. -/
def workingSetFeasibleDirections
    (P : QuadraticProgram n me mi) (workingSet : Finset (Fin mi)) : Set Point :=
  {d | P.Aeq.mulVec d = 0 ∧ ∀ i ∈ workingSet, (P.Aineq.mulVec d) i = 0}

/-- The working-set subproblem objective at `x` is
`d ↦ (G x + g)ᵀ d + (1 / 2) dᵀ G d`. -/
def workingSetSubproblemObjective
    (P : QuadraticProgram n me mi) (x d : Point) : ℝ :=
  dotProduct (P.G.mulVec x) d + dotProduct P.g d +
    (1 / 2 : ℝ) * dotProduct d (P.G.mulVec d)

/-- A direction `d` solves the active-set working-set subproblem at `x` when it minimizes the
quadratic subproblem objective over the feasible directions determined by the current working
set. -/
def solvesWorkingSetSubproblem
    (P : QuadraticProgram n me mi) (x : Point)
    (workingSet : Finset (Fin mi)) (d : Point) : Prop :=
  IsMinOn (P.workingSetSubproblemObjective x) (P.workingSetFeasibleDirections workingSet) d

/-- Unfolding `solvesWorkingSetSubproblem` shows that it is exactly an `IsMinOn` statement for
the working-set subproblem objective and feasible-direction set. -/
theorem solvesWorkingSetSubproblem_iff
    (P : QuadraticProgram n me mi) (x : Point)
    (workingSet : Finset (Fin mi)) (d : Point) :
    P.solvesWorkingSetSubproblem x workingSet d ↔
      IsMinOn
        (P.workingSetSubproblemObjective x)
        (P.workingSetFeasibleDirections workingSet)
        d :=
  Iff.rfl

/-- A scalar `α` is the Step-3 step size for the active-set method at `(x, d)` when
`0 < α ≤ 1`, the trial point `x + α • d` remains feasible, and no larger `β ∈ (α, 1]`
keeps the trial point feasible. This packages the source rule `(9.4.24)`. -/
def isActiveSetStepSize
    (P : QuadraticProgram n me mi) (x d : Point) (α : ℝ) : Prop :=
  α ∈ Set.Ioc (0 : ℝ) 1 ∧
    x + α • d ∈ P.feasibleSet ∧
    ∀ β : ℝ, β ∈ Set.Ioc α 1 → x + β • d ∉ P.feasibleSet

/-- Unfolding `isActiveSetStepSize` gives the Step-3 feasibility-maximality condition. -/
theorem isActiveSetStepSize_iff
    (P : QuadraticProgram n me mi) (x d : Point) (α : ℝ) :
    P.isActiveSetStepSize x d α ↔
      α ∈ Set.Ioc (0 : ℝ) 1 ∧
        x + α • d ∈ P.feasibleSet ∧
        ∀ β : ℝ, β ∈ Set.Ioc α 1 → x + β • d ∉ P.feasibleSet :=
  Iff.rfl

/-- The Step-2 leaving-index rule `(9.4.18)` chooses a working inequality whose multiplier is
negative and minimal among the current working inequalities. Since `workingSet` stores only the
inequality part of `S_k = E ∪ I(x_k)`, this is exactly the source minimization over
`S_k ∩ I`. -/
def IsStepTwoLeavingIndex
    (workingSet : Finset (Fin mi)) (ineqMultiplier : IneqMultiplier) (leaving : Fin mi) : Prop :=
  leaving ∈ workingSet ∧
    ineqMultiplier leaving < 0 ∧
    ∀ i : Fin mi, i ∈ workingSet → ineqMultiplier leaving ≤ ineqMultiplier i

/-- Unfolding `IsStepTwoLeavingIndex` gives the source `(9.4.18)` minimization rule on the
working inequality multipliers. -/
theorem isStepTwoLeavingIndex_iff
    (workingSet : Finset (Fin mi)) (ineqMultiplier : IneqMultiplier) (leaving : Fin mi) :
    IsStepTwoLeavingIndex workingSet ineqMultiplier leaving ↔
      leaving ∈ workingSet ∧
        ineqMultiplier leaving < 0 ∧
        ∀ i : Fin mi, i ∈ workingSet → ineqMultiplier leaving ≤ ineqMultiplier i :=
  Iff.rfl

/-- The zero-direction branch removes the working inequality selected by the source Step-2
leaving-index rule `(9.4.18)` without changing the iterate. -/
structure ZeroDirectionDropState
    (workingSet workingSetNext : Finset (Fin mi))
    (x xNext : Point) (ineqMultiplier : IneqMultiplier) (leaving : Fin mi) : Prop where
  leaving_rule : IsStepTwoLeavingIndex workingSet ineqMultiplier leaving
  iterate_eq : xNext = x
  workingSet_eq : workingSetNext = workingSet.erase leaving

namespace ZeroDirectionDropState

theorem leaving_mem
    {workingSet workingSetNext : Finset (Fin mi)}
    {x xNext : Point} {ineqMultiplier : IneqMultiplier} {leaving : Fin mi}
    (hdrop : ZeroDirectionDropState workingSet workingSetNext x xNext ineqMultiplier leaving) :
    leaving ∈ workingSet :=
  hdrop.leaving_rule.1

theorem multiplier_neg
    {workingSet workingSetNext : Finset (Fin mi)}
    {x xNext : Point} {ineqMultiplier : IneqMultiplier} {leaving : Fin mi}
    (hdrop : ZeroDirectionDropState workingSet workingSetNext x xNext ineqMultiplier leaving) :
    ineqMultiplier leaving < 0 :=
  hdrop.leaving_rule.2.1

end ZeroDirectionDropState

/-- The partial-step branch adds a previously inactive inequality that becomes active at the
next iterate. -/
structure PartialStepConstraintEntry
    (P : QuadraticProgram n me mi)
    (workingSet workingSetNext : Finset (Fin mi))
    (xNext : Point) (entering : Fin mi) : Prop where
  entering_not_mem : entering ∉ workingSet
  becomes_active : (P.Aineq.mulVec xNext) entering = P.bineq entering
  workingSet_eq : workingSetNext = insert entering workingSet

/-- Chapter09 Algorithm 9.4.2: an active-set method for the quadratic program `P` starts from an
initial point `x1`, stores the source working set `S₁ = E ∪ I(x₁)` as the inequality part
`workingSet 0 = P.activeSet x1`, and records the Step-2 and Step-3 update rules stage by stage.
Here `x 0` corresponds to the source iterate `x₁`, and the initial-feasibility fact
`x1 ∈ P.feasibleSet` is recovered from `feasible 0` together with `x_initial` rather than stored
as separate data. For every stage `k`, `direction k` solves the equality-based working-set
subproblem. If `direction k = 0`, then Step 2 either satisfies the stopping test that all
working-set inequality multipliers are nonnegative or removes the working inequality selected by
`(9.4.18)` without changing the iterate. If `direction k ≠ 0`, then Step 3 uses a maximal
feasible step size, updates
`x (k + 1) = x k + stepSize k • direction k`, keeps the working set unchanged for a full step,
and adds a newly active inequality for a partial step. -/
structure ActiveSetMethod (P : QuadraticProgram n me mi) (x1 : Point) where
  x : ℕ → Point
  workingSet : ℕ → Finset (Fin mi)
  direction : ℕ → Point
  stepSize : ℕ → ℝ
  eqMultiplier : ℕ → EqMultiplier
  ineqMultiplier : ℕ → IneqMultiplier
  enteringIndex : ℕ → Fin mi
  leavingIndex : ℕ → Fin mi
  x_initial : x 0 = x1
  workingSet_initial : workingSet 0 = P.activeSet x1
  feasible : ∀ k : ℕ, x k ∈ P.feasibleSet
  subproblem_solution :
    ∀ k : ℕ, P.solvesWorkingSetSubproblem (x k) (workingSet k) (direction k)
  zeroDirection_stationarity :
    ∀ k : ℕ, direction k = 0 →
      P.G.mulVec (x k) + P.g =
        P.Aeqᵀ *ᵥ eqMultiplier k + P.Aineqᵀ *ᵥ ineqMultiplier k
  zeroDirection_inactiveMultiplier :
    ∀ k : ℕ, direction k = 0 →
      ∀ i : Fin mi, i ∉ workingSet k → ineqMultiplier k i = 0
  zeroDirection_branch :
    ∀ k : ℕ, direction k = 0 →
      (∀ i : Fin mi, i ∈ workingSet k → 0 ≤ ineqMultiplier k i) ∨
        ZeroDirectionDropState
          (workingSet k)
          (workingSet (k + 1))
          (x k)
          (x (k + 1))
          (ineqMultiplier k)
          (leavingIndex k)
  nonzeroDirection_stepSize :
    ∀ k : ℕ, direction k ≠ 0 →
      P.isActiveSetStepSize (x k) (direction k) (stepSize k)
  nonzeroDirection_update :
    ∀ k : ℕ, direction k ≠ 0 →
      x (k + 1) = x k + stepSize k • direction k
  fullStep_workingSet :
    ∀ k : ℕ, direction k ≠ 0 →
      stepSize k = 1 → workingSet (k + 1) = workingSet k
  partialStep_entersConstraint :
    ∀ k : ℕ, direction k ≠ 0 → stepSize k < 1 →
      PartialStepConstraintEntry
        P
        (workingSet k)
        (workingSet (k + 1))
        (x (k + 1))
        (enteringIndex k)

/-- An active-set method can be evaluated as its iterate sequence `x`. -/
instance (P : QuadraticProgram n me mi) (x1 : Point) :
    CoeFun (ActiveSetMethod P x1) (fun _ ↦ ℕ → Point) where
  coe A := A.x

/-- Evaluating an active-set method as a function returns its iterate sequence. -/
theorem ActiveSetMethod.coe_apply
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The source initial iterate `x₁` is feasible because Algorithm 9.4.2 keeps every iterate
feasible and `x 0 = x₁`. -/
theorem ActiveSetMethod.x1_mem_feasibleSet
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) :
    x1 ∈ P.feasibleSet := by
  simpa [A.x_initial] using A.feasible 0

/-- The algorithm terminates at stage `k` exactly when the working-set subproblem returns
`direction k = 0` and the working-set inequality multipliers are all nonnegative. -/
def ActiveSetMethod.terminatedAt
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) : Prop :=
  A.direction k = 0 ∧ ∀ i : Fin mi, i ∈ A.workingSet k → 0 ≤ A.ineqMultiplier k i

/-- Unfolding `terminatedAt` gives the zero-direction and nonnegative-multiplier stopping test. -/
theorem ActiveSetMethod.terminatedAt_iff
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) :
    A.terminatedAt k ↔
      A.direction k = 0 ∧
        ∀ i : Fin mi, i ∈ A.workingSet k → 0 ≤ A.ineqMultiplier k i :=
  Iff.rfl

/-- On a zero-direction stage, Step 2 either satisfies the stopping test or performs the
`(9.4.18)` leaving-index removal update. -/
theorem ActiveSetMethod.zeroDirectionStopsOrDrops
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) {k : ℕ}
    (hzero : A.direction k = 0) :
    A.terminatedAt k ∨
      ZeroDirectionDropState
        (A.workingSet k)
        (A.workingSet (k + 1))
        (A.x k)
        (A.x (k + 1))
        (A.ineqMultiplier k)
        (A.leavingIndex k) := by
  rcases A.zeroDirection_branch k hzero with hterm | hdrop
  · exact Or.inl ⟨hzero, hterm⟩
  · exact Or.inr hdrop

/-- On a nonzero-direction stage, the active-set method uses a Step-3 maximal feasible step and
updates the iterate by `x (k + 1) = x k + stepSize k • direction k`. -/
theorem ActiveSetMethod.nonzeroDirectionSpec
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) {k : ℕ}
    (hdir : A.direction k ≠ 0) :
    P.isActiveSetStepSize (A.x k) (A.direction k) (A.stepSize k) ∧
      A.x (k + 1) = A.x k + A.stepSize k • A.direction k :=
  ⟨A.nonzeroDirection_stepSize k hdir, A.nonzeroDirection_update k hdir⟩

end QuadraticProgram

end Chapter09Algorithm942
