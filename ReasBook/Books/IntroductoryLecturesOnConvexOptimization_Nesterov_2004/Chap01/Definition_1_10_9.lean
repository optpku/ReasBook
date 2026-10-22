/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/-
Definition 1.10.9 lies in the Chapter 1 strict-feasibility domain.

Sampled owner-style declarations in this domain:
* `FunctionalConstraintsMinimizationProblem.StrictlyFeasible` in `Chap01/Definition_1_1_2`
* `LagrangianProblem.toFunctionalConstraintsMinimizationProblem` in `Chap01/Definition_1_10_2`
* `FunctionalConstraintsMinimizationProblem.StrictlyFeasible.feasibleSet_nonempty` in
  `Chap01/Definition_1_1_2`

Best owner abstraction:
* the Chapter 1 strict-feasibility owner
  `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible`

Primitive data:
* `problem.objective`
* `problem.constraints`

Derived API:
* `problem.feasibleSet`
* the textbook expansion `∃ x : Q, ∀ j : Fin m, problem.constraints j x < 0`
* the induced feasible-set nonemptiness theorem on `problem.feasibleSet`

Source/core/bridge triage:
* source-facing: the textbook strict-inequality formulation of Slater's condition
* core/canonical: `FunctionalConstraintsMinimizationProblem.StrictlyFeasible`
* bridge/view: `problem.toFunctionalConstraintsMinimizationProblem`

This file does not introduce a second owner. Definition 1.10.9 is the specialization of the
existing strict-feasibility owner along `toFunctionalConstraintsMinimizationProblem`, and the
source-facing API here should stay at that bridge layer.
-/

/- Definition 1.10.9 reuses the Chapter 1 strict-feasibility owner specialized to a
`LagrangianProblem`. -/
variable (problem : LagrangianProblem Q m) in
#check problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible

/-- Definition 1.10.9: the Slater condition for a Lagrangian problem is strict feasibility of the
associated functional-constraint problem obtained by viewing every scalar constraint as an
inequality `fⱼ(x) ≤ 0`. -/
def SlaterCondition (problem : LagrangianProblem Q m) : Prop :=
  problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible

/-- Helper for Definition 1.10.9: expanding `problem.SlaterCondition` recovers the textbook
coordinatewise strict-inequality formulation. -/
@[simp] theorem slaterCondition_iff (problem : LagrangianProblem Q m) :
    problem.SlaterCondition ↔
      ∃ x : Q, ∀ j : Fin m, problem.constraints j x < 0 := by
  let P := problem.toFunctionalConstraintsMinimizationProblem
  -- Re-express the bridge definition in terms of the owner strict-feasibility predicate.
  change P.StrictlyFeasible ↔
      ∃ x : Q, ∀ j : Fin m, problem.constraints j x < 0
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro j
    -- Unpack membership in the owner strict feasible set and simplify the `≤`-constraint view.
    simpa [LagrangianProblem.toFunctionalConstraintsMinimizationProblem,
      ConstraintSense.StrictHolds] using
      (P.mem_strictFeasibleSet.mp hx) j
  · rintro ⟨x, hx⟩
    -- Repackage a textbook Slater point as a strict-feasible point of the owner problem.
    refine ⟨⟨x, Set.mem_univ x⟩, ?_⟩
    exact P.mem_strictFeasibleSet.mpr <| fun j ↦ by
      simpa [LagrangianProblem.toFunctionalConstraintsMinimizationProblem,
        ConstraintSense.StrictHolds] using hx j

/-- Helper for Definition 1.10.9: a Slater point is in particular feasible for the associated
inequality-constrained problem. -/
theorem feasibleSet_nonempty_of_slaterCondition {problem : LagrangianProblem Q m}
    (h : problem.SlaterCondition) :
    problem.feasibleSet.Nonempty := by
  -- The owner strict-feasibility theorem already provides a feasible point after unfolding.
  simpa [LagrangianProblem.feasibleSet] using h.feasibleSet_nonempty

end LagrangianProblem
