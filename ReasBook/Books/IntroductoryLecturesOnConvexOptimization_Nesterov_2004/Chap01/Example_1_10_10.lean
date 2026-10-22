/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_15

-- Declarations for this item will be appended below by the statement pipeline.

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]

section

variable (constraints : ι → C(X, ℝ))

/- Primary domain: penalty functions for finite families of continuous inequality constraints.

Relevant owner declarations sampled before refining:
* `IsPenaltyFunction` in `Definition_1_10_14`
* `quadraticPenalty` in `Definition_1_10_15`
* `nonsmoothPenalty` in `Definition_1_10_15`
* the owner certification theorems
  `quadraticPenalty_isPenaltyFunction` and
  `nonsmoothPenalty_isPenaltyFunction` in `Definition_1_10_15`

Best owner abstraction:
* core/canonical: `IsPenaltyFunction`

Primitive data:
* the finite family `constraints : ι → C(X, ℝ)` with `[Fintype ι]`

Derived API:
* the concrete penalties `quadratic_penalty_function constraints` and
  `nonsmoothPenalty constraints`
* their pointwise textbook formulas
  `quadraticPenalty_apply` and `nonsmoothPenalty_apply`
* their certification as penalty functions for the chapter owner
  `constraintSet constraints`

Source/core/bridge triage:
* source-facing: Example 1.10.10, asserting that these two explicit positive-part sums are
  penalty functions for the same feasible set
* core/canonical: `IsPenaltyFunction`
* bridge/view: direct recall of the two owner certification theorems from `Definition_1_10_15`

This file adds no new owner-level API: the concrete penalties, their textbook evaluation formulas,
and their certification theorems already live in the owner file, so keeping local duplicate
example theorems here would only duplicate that API. The source's Euclidean model is not used by
the owner declarations, so the example is stated at the same canonical ambient level as
`Definition_1_10_15`. -/

/- Example 1.10.10: the quadratic positive-part sum is the concrete owner
`quadraticPenalty constraints`. -/
recall quadraticPenalty

/- Example 1.10.10: pointwise, the quadratic penalty is the textbook sum
`x ↦ ∑ j, ((constraints j x)⁺)^2`. -/
recall quadraticPenalty_apply

/- Example 1.10.10: the quadratic positive-part sum is a penalty for the feasible set cut out by
the constraints. -/
recall quadraticPenalty_isPenaltyFunction

/- Example 1.10.10: the nonsmooth positive-part sum is the concrete owner
`nonsmoothPenalty constraints`. -/
recall nonsmoothPenalty

/- Example 1.10.10: pointwise, the nonsmooth penalty is the textbook sum
`x ↦ ∑ j, (constraints j x)⁺`. -/
recall nonsmoothPenalty_apply

/- Example 1.10.10: the nonsmooth positive-part sum is a penalty for the same feasible set. -/
recall nonsmoothPenalty_isPenaltyFunction

end
