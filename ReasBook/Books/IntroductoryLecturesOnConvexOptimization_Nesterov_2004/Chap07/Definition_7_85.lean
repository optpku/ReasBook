/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 7.85 lies in the chapter's unconstrained minimization / positive-objective domain.

Mandatory domain-style sampling before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  real-valued objective on a fixed feasible set;
- `SetConstrainedMinimizationProblem.optimalValue` and `optimalValue_eq_of_isMinOn` in
  `Chap01/Definition_1_3_7`, the canonical owner optimal-value API;
- `IsMinOn` and `isMinOn_univ_iff` in mathlib's extremum API, the canonical whole-space minimizer
  owner;
- `IsApproximateSolution` in `Chap03/Definition_3_34`, the nearby project pattern of keeping the
  source-facing unconstrained notion while using the Chapter 1 whole-space owner only as a bridge.

Best owner abstraction:
- source-facing: `StrictlyPositiveObjectiveMinimizationProblem Q`;
- core/canonical: `SetConstrainedMinimizationProblem Q` with feasible set `Set.univ`, together
  with `IsMinOn`;
- bridge/view: `toSetConstrainedMinimizationProblem`.

Primitive data:
- the objective `Q → ℝ`;
- strict positivity of that objective;
- a chosen optimal solution.

Derived API:
- the whole-space Chapter 1 minimization owner;
- the source-facing optimal value, defined by the chosen optimizer;
- the identification of that value with the infimum of attained objective values.

Source/core/bridge triage:
- source-facing: `StrictlyPositive`, `StrictlyPositiveObjectiveMinimizationProblem`, and the local
  chosen-optimum value;
- core/canonical: `SetConstrainedMinimizationProblem` and `IsMinOn`;
- bridge/view: `toSetConstrainedMinimizationProblem` and the owner-optimal-value comparison theorem.

The duplicate wheel removed here is the local raw-`sInf` optimization owner. Definition 7.85 keeps
its source-facing extra data, namely strict positivity and a chosen minimizer, but its underlying
optimization problem is now expressed canonically through the Chapter 1 whole-space owner.
-/

/-- A real-valued function on `Q` is strictly positive when all of its values are positive. -/
def StrictlyPositive {Q : Type u} (f : Q → ℝ) : Prop :=
  ∀ x, 0 < f x

namespace StrictlyPositive

variable {Q : Type u} {f : Q → ℝ}

/-- A strictly positive function has positive value at every feasible point. -/
theorem apply (hf : StrictlyPositive f) (x : Q) : 0 < f x :=
  hf x

end StrictlyPositive

/-- Definition 7.85: a general minimization problem with strictly positive objective consists of
a feasible type `Q`, a strictly positive objective function `φ : Q → ℝ`, and a chosen optimal
solution `x⋆ : Q` minimizing `φ` over all feasible points. -/
structure StrictlyPositiveObjectiveMinimizationProblem (Q : Type u) where
  /-- The objective function `φ : Q → ℝ`. -/
  objective : Q → ℝ
  /-- The objective function is strictly positive on the feasible set `Q`. -/
  objective_strictlyPositive : StrictlyPositive objective
  /-- The chosen optimal solution `x⋆ ∈ Q`. -/
  optimalSolution : Q
  /-- The chosen optimal solution minimizes `φ` over the whole feasible set `Q`. -/
  optimalSolution_isMin : IsMinOn objective Set.univ optimalSolution

/-- A strictly-positive-objective minimization problem can be used as its objective function. -/
instance {Q : Type u} :
    CoeFun (StrictlyPositiveObjectiveMinimizationProblem Q) (fun _ ↦ Q → ℝ) where
  coe problem := problem.objective

namespace StrictlyPositiveObjectiveMinimizationProblem

variable {Q : Type u}

/-- The canonical Chapter 1 whole-space minimization owner attached to the objective. -/
def toSetConstrainedMinimizationProblem
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    SetConstrainedMinimizationProblem Q where
  feasibleSet := Set.univ
  objective := problem.objective

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) (x : Q) :
    problem.toSetConstrainedMinimizationProblem x = problem x :=
  rfl

/-- The optimal value `φ⋆` is the objective value at the chosen optimal solution. -/
def optimalValue (problem : StrictlyPositiveObjectiveMinimizationProblem Q) : ℝ :=
  problem problem.optimalSolution

/-- Expanding `optimalValue` gives the infimum of the objective values attained on `Q`. -/
theorem optimalValue_eq_sInf_range
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    problem.optimalValue = sInf (Set.range problem.objective) := by
  have hglb : IsGLB (Set.range problem.objective) (problem problem.optimalSolution) := by
    simpa [Set.range] using
      problem.optimalSolution_isMin.isGLB (Set.mem_univ problem.optimalSolution)
  symm
  simpa [optimalValue] using
    hglb.csInf_eq ⟨_, ⟨problem.optimalSolution, rfl⟩⟩

/-- The optimal value is attained at the chosen optimal solution `x⋆`. -/
@[simp] theorem optimalValue_eq_objective_optimalSolution
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    problem.optimalValue = problem.objective problem.optimalSolution :=
  rfl

/-- The Chapter 1 owner optimal value agrees with the source-facing optimal value. -/
@[simp] theorem toSetConstrainedMinimizationProblem_optimalValue
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    problem.toSetConstrainedMinimizationProblem.optimalValue = (problem.optimalValue : EReal) := by
  simpa [optimalValue] using
    problem.toSetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
      (Set.mem_univ problem.optimalSolution) problem.optimalSolution_isMin

/-- The chosen optimal solution has strictly positive objective value. -/
theorem objective_optimalSolution_pos
    (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    0 < problem.objective problem.optimalSolution :=
  problem.objective_strictlyPositive problem.optimalSolution

/-- The optimal value is strictly positive. -/
theorem optimalValue_pos (problem : StrictlyPositiveObjectiveMinimizationProblem Q) :
    0 < problem.optimalValue := by
  simpa [optimalValue] using problem.objective_optimalSolution_pos

end StrictlyPositiveObjectiveMinimizationProblem
