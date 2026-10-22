/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 2.25 is a source-facing recall in the Euclidean set-constrained minimization domain.

Primary domain:
* constrained minimization on `ℝⁿ`

Relevant owner-style declarations sampled before refining:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner object
  for a feasible set together with an ambient real-valued objective;
* `SetConstrainedMinimizationProblem.coe_apply`, the coercion view of a problem as its objective
  function;
* `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`, the canonical bridge to the
  older zero-constraint owner;
* `IsMinOn`, the canonical minimizer predicate on a set.

Best owner abstraction:
* `problem : SetConstrainedMinimizationProblem E`

Primitive data:
* `feasibleSet : Set E`
* `objective : E → ℝ`

Derived API:
* the coercion `problem : E → ℝ`
* the minimizer predicate `IsMinOn problem problem.feasibleSet x`
* the bridge `problem.toGeneralMinimizationProblem`

Source/core/bridge triage:
* source-facing: the constrained problem `min_{x ∈ Q} f(x)` on `ℝⁿ`
* core/canonical: `SetConstrainedMinimizationProblem E` together with
  `IsMinOn problem problem.feasibleSet x`
* bridge/view: `problem.toGeneralMinimizationProblem`

The textbook presentation with an objective written only on `Q` is represented in the project by
an ambient objective together with the feasible set `Q`; only the restriction of that ambient
objective to `Q` affects the minimization semantics. This file therefore recalls the owner
abstraction directly and keeps no parallel public wrapper such as
`ConstrainedMinimizationProblem` or `GlobalConstrainedMinimizer`.
-/

section

variable (Q : Set E) (f : E → ℝ)

/- Definition 2.25: a constrained minimization problem over a set is the canonical owner
`SetConstrainedMinimizationProblem E`, packaging a feasible set `Q ⊆ ℝⁿ` together with a
real-valued ambient objective whose restriction to `Q` is minimized. -/
recall SetConstrainedMinimizationProblem
recall IsMinOn

variable (problem : SetConstrainedMinimizationProblem E) (x : E)

set_option linter.hashCommand false in
#check (.mk Q f : SetConstrainedMinimizationProblem E)

set_option linter.hashCommand false in
#check (problem : E → ℝ)

set_option linter.hashCommand false in
#check (IsMinOn problem problem.feasibleSet x : Prop)

end
