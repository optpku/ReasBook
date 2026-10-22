/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace SeparableOptimizationProblem

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/- Definition 5.4.8.4 lies in the separable convex optimization / standard-form epigraph domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with its objective;
- `SeparableOptimizationProblem` in `Definition_5_4_8_1`, the source-facing owner of the
  separable coefficient data and affine-function block structure;
- `StandardFormDecisionVariable` in `Theorem_5_4_8_1`, the canonical decision-variable type for
  the variables `(x, τ, t)`;
- `standardFormOptimizationProblem` in `Theorem_5_4_8_1`, the canonical Chapter 1 constrained
  problem attached to that reformulation.

Best owner abstraction:
- source-facing: the textbook standard-form variables `(x, τ, t)` and the epigraph reformulation
  attached to `problem : SeparableOptimizationProblem E m`;
- core/canonical:
  `SetConstrainedMinimizationProblem (StandardFormDecisionVariable problem)`;
- bridge/view: the exact objective-evaluation and feasible-set-membership theorems already owned
  by `standardFormOptimizationProblem`.

Primitive data:
- the original separable problem `problem : SeparableOptimizationProblem E m`.

Derived API:
- `StandardFormDecisionVariable problem`;
- `standardFormOptimizationProblem problem`;
- `standardFormOptimizationProblem_apply`;
- `mem_standardFormOptimizationProblem_feasibleSet_iff`.

Source/core/bridge triage:
- source-facing: the textbook variables `(x, τ, t)` and the standard-form minimization problem;
- core/canonical: the Chapter 1 owner `SetConstrainedMinimizationProblem`;
- bridge/view: the companion evaluation and membership lemmas for the standard-form owner.

This file therefore reuses the chapter's canonical decision-variable owner
`StandardFormDecisionVariable problem` directly, rather than rebuilding a second wrapper for the
slack variables. The recalled constrained problem is expressed over that reused owner. -/

/- Definition 5.4.8.4 recalls the canonical standard-form decision-variable owner. -/
recall StandardFormDecisionVariable

/- Definition 5.4.8.4 recalls the canonical standard-form epigraph reformulation of a separable
optimization problem. -/
recall standardFormOptimizationProblem
recall standardFormOptimizationProblem_apply
recall mem_standardFormOptimizationProblem_feasibleSet_iff

end SeparableOptimizationProblem
