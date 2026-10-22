/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} {m : ℕ} (problem : FunctionalConstraintsMinimizationProblem X m)

/-
Definition 1.1.2 lies in the constrained-optimization feasibility domain.

Sampled owner-style declarations:
* `ConstraintSense.Holds`, `ConstraintSense.StrictHolds`, and the owner feasible predicate
  `problem.IsFeasible` in
  `Chap01/Definition_1_1_3`
* the owner feasible set `problem.feasibleSet` in `Chap01/Definition_1_1_3`
* `LagrangianProblem.SlaterCondition` in `Chap01/Definition_1_10_9`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `basicFeasibleSet`
* `constraints`
* `senses`

Derived API:
* the owner recall `problem.feasibleSet.Nonempty`
* the source-facing point predicate `problem.IsStrictlyFeasible`
* the owner strict feasible set `problem.strictFeasibleSet`
* the problem-level predicate `problem.StrictlyFeasible`
* the implication to ordinary feasibility and the resulting feasible-set nonemptiness theorem

Source/core/bridge triage:
* source-facing: `problem.IsStrictlyFeasible`, `problem.StrictlyFeasible`
* core/canonical: `ConstraintSense.StrictHolds`, `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `problem.strictFeasibleSet`, the implication from strict feasibility to ordinary
  feasibility, and the Euclidean specialization `GeneralMinimizationProblem n m`

The later `LagrangianProblem.SlaterCondition` should therefore reuse this owner through its
canonical bridge to `FunctionalConstraintsMinimizationProblem`, rather than restating the same
strict-feasibility data.
-/

#check problem.feasibleSet.Nonempty

end FunctionalConstraintsMinimizationProblem

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} {m : ℕ} (problem : FunctionalConstraintsMinimizationProblem X m)

/-- A point of the basic feasible set is strictly feasible if every inequality constraint is
satisfied strictly and every equality constraint exactly. -/
def IsStrictlyFeasible (x : problem.basicFeasibleSet) : Prop :=
  ∀ i, (problem.senses i).StrictHolds (problem.constraints i x)

/-- The strict feasible set, viewed inside the basic feasible set. -/
def strictFeasibleSet : Set problem.basicFeasibleSet :=
  {x | problem.IsStrictlyFeasible x}

/-- Membership in `problem.strictFeasibleSet` is exactly strict feasibility of the point. -/
@[simp] theorem mem_strictFeasibleSet {x : problem.basicFeasibleSet} :
    x ∈ problem.strictFeasibleSet ↔ problem.IsStrictlyFeasible x :=
  Iff.rfl

/-- Definition 1.1.2: A minimization problem is strictly feasible when it has a strictly
feasible point. -/
def StrictlyFeasible : Prop :=
  problem.strictFeasibleSet.Nonempty

/-- Every strictly feasible point is feasible, so the strict feasible set lies in the feasible
set. -/
theorem strictFeasibleSet_subset_feasibleSet :
    problem.strictFeasibleSet ⊆ problem.feasibleSet := by
  intro x hx
  exact fun i ↦ (problem.mem_strictFeasibleSet.mp hx i).holds

/-- A strictly feasible point is feasible. -/
theorem IsStrictlyFeasible.isFeasible {x : problem.basicFeasibleSet}
    (hx : problem.IsStrictlyFeasible x) :
    problem.IsFeasible x := by
  exact problem.strictFeasibleSet_subset_feasibleSet hx

namespace StrictlyFeasible

/-- Strict feasibility provides a feasible point. -/
theorem feasibleSet_nonempty (h : problem.StrictlyFeasible) :
    problem.feasibleSet.Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, problem.strictFeasibleSet_subset_feasibleSet hx⟩

end StrictlyFeasible

end FunctionalConstraintsMinimizationProblem
