/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Tactic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Lemma_11_5_4

noncomputable section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

-- Primary domain: equality-constrained minimization in a finite-dimensional Euclidean space.
-- Sampled owners:
-- * `IsMinOn` is the canonical minimizer predicate.
-- * `LinearEqualityConstrainedProblem` from Chapter 11 is the owner for affine equality
--   constraints `Aᵀ x = b`, with `x ∈ problem` as the public feasible-point surface and
--   `problem.feasibleSet` as the underlying set-valued minimization domain.
-- The exercise-specific primitive data are the quartic objective and the eliminated
-- one-variable quartic; the feasible-set API is derived from the Chapter 11 owner object.

/-- The objective in Exercise 11.3 is `x ↦ 8 * x 0^4 - x 1^4`. -/
def chapter11Exercise113Objective (x : Point) : ℝ :=
  8 * (x 0) ^ (4 : ℕ) - (x 1) ^ (4 : ℕ)

/-- Exercise 11.3 as the linear equality-constrained problem with constraint `x 0 + x 1 = 1`. -/
def chapter11Exercise113Problem : LinearEqualityConstrainedProblem 2 1 where
  objective := chapter11Exercise113Objective
  constraintMatrix := fun _ _ ↦ 1
  constraintTarget := EuclideanSpace.single 0 (1 : ℝ)

/-- Eliminating `x 1` by `x 1 = 1 - x 0` gives the reduced one-variable objective
`x0 ↦ 8 * x0^4 - (1 - x0)^4`. -/
def chapter11Exercise113ReducedObjective (x0 : ℝ) : ℝ :=
  8 * x0 ^ (4 : ℕ) - (1 - x0) ^ (4 : ℕ)

/-- The optimizer of the reduced one-variable objective in Exercise 11.3 is `x0 = -1`. -/
def chapter11Exercise113ReducedSolution : ℝ :=
  -1

/-- The constrained optimizer for Exercise 11.3 is `(-1, 2)ᵀ`. -/
def chapter11Exercise113Solution : Point :=
  EuclideanSpace.single 0 (-1 : ℝ) + EuclideanSpace.single 1 (2 : ℝ)

#print axioms chapter11Exercise113Problem
#print axioms chapter11Exercise113ReducedSolution
#print axioms chapter11Exercise113Solution

/-- Feasibility for `chapter11Exercise113Problem` is exactly the equality constraint
`x 0 + x 1 = 1`. -/
theorem chapter11Exercise113_mem_iff (x : Point) :
    x ∈ chapter11Exercise113Problem ↔ x 0 + x 1 = 1 := by
  constructor
  · intro hx
    have hEq := (chapter11Exercise113Problem.mem_feasibleSet_iff x).1 hx
    have h0 := congrArg (fun v : Fin 1 → ℝ ↦ v 0) hEq
    simpa [chapter11Exercise113Problem, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
  · intro hx
    refine (chapter11Exercise113Problem.mem_feasibleSet_iff x).2 ?_
    ext i
    fin_cases i
    simpa [chapter11Exercise113Problem, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hx

/-- On the feasible line `x 0 + x 1 = 1`, the constrained objective reduces to
`chapter11Exercise113ReducedObjective (x 0)`. -/
theorem chapter11Exercise113_objective_eq_reducedObjective_of_memFeasibleSet
    {x : Point} (hx : x ∈ chapter11Exercise113Problem) :
    chapter11Exercise113Objective x = chapter11Exercise113ReducedObjective (x 0) := by
  rw [chapter11Exercise113_mem_iff] at hx
  have hx1 : x 1 = 1 - x 0 := by
    nlinarith
  simp [chapter11Exercise113Objective, chapter11Exercise113ReducedObjective, hx1]

private theorem chapter11Exercise113ReducedObjective_sub_solution (x0 : ℝ) :
    chapter11Exercise113ReducedObjective x0 -
      chapter11Exercise113ReducedObjective chapter11Exercise113ReducedSolution =
        (x0 + 1) ^ (2 : ℕ) * (7 * x0 ^ (2 : ℕ) - 10 * x0 + 7) := by
  norm_num [chapter11Exercise113ReducedObjective, chapter11Exercise113ReducedSolution]
  ring

private theorem chapter11Exercise113ReducedQuadratic_nonneg (x0 : ℝ) :
    0 ≤ 7 * x0 ^ (2 : ℕ) - 10 * x0 + 7 := by
  have hsq : 0 ≤ 7 * (x0 - 5 / 7) ^ (2 : ℕ) + 24 / 7 := by
    positivity
  nlinarith

private theorem chapter11Exercise113ReducedQuadratic_pos (x0 : ℝ) :
    0 < 7 * x0 ^ (2 : ℕ) - 10 * x0 + 7 := by
  have hsq : 0 < 7 * (x0 - 5 / 7) ^ (2 : ℕ) + 24 / 7 := by
    positivity
  nlinarith

/-- The reduced one-variable objective in Exercise 11.3 is minimized on `Set.univ` at `x0 = -1`.
-/
theorem chapter11Exercise113ReducedSolution_isMinOn :
    IsMinOn
      chapter11Exercise113ReducedObjective
      Set.univ
      chapter11Exercise113ReducedSolution := by
  refine isMinOn_iff.mpr ?_
  intro x _
  have hfactor := chapter11Exercise113ReducedObjective_sub_solution x
  have hprod :
      0 ≤ (x + 1) ^ (2 : ℕ) * (7 * x ^ (2 : ℕ) - 10 * x + 7) :=
    mul_nonneg (sq_nonneg (x + 1)) (chapter11Exercise113ReducedQuadratic_nonneg x)
  nlinarith

/-- The explicit solution point for Exercise 11.3 is feasible for `chapter11Exercise113Problem`.
-/
theorem chapter11Exercise113Solution_memFeasibleSet :
    chapter11Exercise113Solution ∈ chapter11Exercise113Problem := by
  rw [chapter11Exercise113_mem_iff]
  norm_num [chapter11Exercise113Solution]

/-- Chapter11 Exercise 11.3: the feasible point `chapter11Exercise113Solution = (-1, 2)ᵀ`
minimizes `chapter11Exercise113Objective` on the constraint set
`chapter11Exercise113Problem.feasibleSet`.
-/
theorem chapter11Exercise113Solution_isMinOnFeasibleSet :
    IsMinOn
      chapter11Exercise113Objective
      chapter11Exercise113Problem.feasibleSet
      chapter11Exercise113Solution := by
  refine isMinOn_iff.mpr ?_
  intro x hx
  have hReducedMin :=
    (isMinOn_iff.mp chapter11Exercise113ReducedSolution_isMinOn) (x 0) (by simp)
  have hsol :
      chapter11Exercise113Objective chapter11Exercise113Solution =
        chapter11Exercise113ReducedObjective chapter11Exercise113ReducedSolution := by
    rw [chapter11Exercise113_objective_eq_reducedObjective_of_memFeasibleSet
      chapter11Exercise113Solution_memFeasibleSet]
    norm_num [chapter11Exercise113Solution, chapter11Exercise113ReducedSolution]
  calc
    chapter11Exercise113Objective chapter11Exercise113Solution =
        chapter11Exercise113ReducedObjective chapter11Exercise113ReducedSolution := hsol
    _ ≤ chapter11Exercise113ReducedObjective (x 0) := hReducedMin
    _ = chapter11Exercise113Objective x :=
      (chapter11Exercise113_objective_eq_reducedObjective_of_memFeasibleSet hx).symm

/-- Any minimizer of `chapter11Exercise113Objective` on the feasible set agrees with the explicit
solution `chapter11Exercise113Solution = (-1, 2)ᵀ`. -/
theorem chapter11Exercise113_eq_solution_of_isMinOnFeasibleSet
    {x : Point} (hx : x ∈ chapter11Exercise113Problem)
    (hmin : IsMinOn chapter11Exercise113Objective chapter11Exercise113Problem.feasibleSet x) :
    x = chapter11Exercise113Solution := by
  have hxle :
      chapter11Exercise113Objective x ≤
        chapter11Exercise113Objective chapter11Exercise113Solution :=
    (isMinOn_iff.mp hmin)
      chapter11Exercise113Solution
      chapter11Exercise113Solution_memFeasibleSet
  have hsolle :
      chapter11Exercise113Objective chapter11Exercise113Solution ≤
        chapter11Exercise113Objective x :=
    (isMinOn_iff.mp chapter11Exercise113Solution_isMinOnFeasibleSet)
      x
      hx
  have hobj :
      chapter11Exercise113Objective x =
        chapter11Exercise113Objective chapter11Exercise113Solution :=
    le_antisymm hxle hsolle
  have hredx :
      chapter11Exercise113Objective x =
        chapter11Exercise113ReducedObjective (x 0) :=
    chapter11Exercise113_objective_eq_reducedObjective_of_memFeasibleSet hx
  have hredsol :
      chapter11Exercise113Objective chapter11Exercise113Solution =
        chapter11Exercise113ReducedObjective chapter11Exercise113ReducedSolution := by
    rw [chapter11Exercise113_objective_eq_reducedObjective_of_memFeasibleSet
      chapter11Exercise113Solution_memFeasibleSet]
    norm_num [chapter11Exercise113Solution, chapter11Exercise113ReducedSolution]
  have hred :
      chapter11Exercise113ReducedObjective (x 0) =
        chapter11Exercise113ReducedObjective chapter11Exercise113ReducedSolution := by
    rw [hredx, hredsol] at hobj
    exact hobj
  have hfactor := chapter11Exercise113ReducedObjective_sub_solution (x 0)
  have hx0sq : ((x 0 : ℝ) + 1) ^ (2 : ℕ) = 0 := by
    have hEqZero :
        ((x 0 : ℝ) + 1) ^ (2 : ℕ) * (7 * (x 0) ^ (2 : ℕ) - 10 * x 0 + 7) = 0 := by
      nlinarith [hred, hfactor]
    have hquad : 0 < 7 * (x 0) ^ (2 : ℕ) - 10 * x 0 + 7 :=
      chapter11Exercise113ReducedQuadratic_pos (x 0)
    nlinarith [sq_nonneg ((x 0 : ℝ) + 1), hEqZero, hquad]
  have hx0 : x 0 = -1 := by
    nlinarith
  rw [chapter11Exercise113_mem_iff] at hx
  have hx1 : x 1 = 2 := by
    nlinarith [hx, hx0]
  ext i
  fin_cases i
  · simpa [chapter11Exercise113Solution] using hx0
  · simpa [chapter11Exercise113Solution] using hx1
