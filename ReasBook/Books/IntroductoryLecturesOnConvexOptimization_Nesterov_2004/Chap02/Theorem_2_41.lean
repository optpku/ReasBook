/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_38

-- Declarations for this item will be appended below by the statement pipeline.

/-
Primary domain: constrained smooth minimax minimization on a complete real Hilbert space with a
nonempty finite component family.

Sampled owner-style declarations:
* `SmoothMinimaxProblem` in `Definition_2_38`, the chapter owner of the feasible set and
  component family;
* `SmoothMinimaxProblem.existsUnique_isMinOn` in `Definition_2_38`, the source-facing unique
  minimizer theorem for that owner object;
* `maxTypeObjective` in `Lemma_2_18`, the canonical max-type objective attached to the component
  family;
* `StrongConvexOn.existsUnique_isMinOn_of_isClosed` in `Theorem_3_45`, the lower-level constrained
  strong-convexity minimizer theorem used internally by the owner API.

Best owner abstraction:
* source-facing/core: `SmoothMinimaxProblem E ι μ L`.

Primitive data:
* the smooth minimax problem `problem : SmoothMinimaxProblem E ι μ L`.

Derived API:
* the canonical max-type objective `problem`;
* the unique feasible minimizer conclusion
  `∃! x, x ∈ problem.feasibleSet ∧ IsMinOn problem problem.feasibleSet x`.

Source/core/bridge triage:
* source-facing: Theorem 2.41 as the unique-minimizer statement for a smooth minimax problem;
* core/canonical: `SmoothMinimaxProblem.existsUnique_isMinOn`;
* bridge/view: the internal passage to `StrongConvexOn.existsUnique_isMinOn_of_isClosed`.

This file therefore recalls the chapter owner theorem directly and introduces no parallel
max-type-only wrapper around it.
-/

namespace SmoothMinimaxProblem

/- Theorem 2.41 is the direct owner recall of the unique feasible minimizer theorem for
`SmoothMinimaxProblem`. -/
recall existsUnique_isMinOn

end SmoothMinimaxProblem
