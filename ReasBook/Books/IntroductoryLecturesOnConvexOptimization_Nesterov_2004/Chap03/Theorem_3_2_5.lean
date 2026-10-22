/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_47

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.2.5 lies in the chapter's strongly convex first-order black-box complexity domain.

Sampled owner-style declarations:
- `IsInStronglyConvexProblemClass` in `Theorem_3_47`, the source-facing owner predicate for the
  local-ball class `𝒫_s(x₀, μ, M)`
- `FirstOrderOracle` in `Theorem_3_2_1`, the canonical owner of valid subgradient replies
- `HasCoordinateSupportGrowth` in `Theorem_3_2_1`, the canonical owner of the oracle-side
  coordinate-support rule
- `SatisfiesLinearSpanCondition` in `Theorem_3_2_1`, the chapter owner for span-based iterates
- `exists_stronglyConvexLipschitzProblem_with_span_method_lower_bound` in `Theorem_3_47`, the
  earlier chapter theorem with the same oracle-level mathematical content

Best owner abstraction:
- source-facing: this numbered hard-instance lower bound for the strongly convex class
- core/canonical: `exists_stronglyConvexLipschitzProblem_with_span_method_lower_bound`
- bridge/view: approximate-minimizer and iteration-complexity corollaries built from that lower
  bound in later files

Primitive data:
- the ambient dimension through `x₀ : EuclideanSpace ℝ (Fin n)`
- the parameters `μ`, `M : NNReal`
- the iterate index `k` with `k + 1 ≤ n`

Derived API:
- the hard instance `f`, the chosen minimizer `xStar`, and class membership
  `IsInStronglyConvexProblemClass x₀ μ M f xStar`
- the lower-bound conclusion for every `FirstOrderOracle f` satisfying
  `HasCoordinateSupportGrowth` and every iterate sequence satisfying
  `SatisfiesLinearSpanCondition`

Source/core/bridge triage:
- source-facing: Theorem 3.2.5 as the textbook strongly convex first-order lower bound
- core/canonical: `exists_stronglyConvexLipschitzProblem_with_span_method_lower_bound`
- bridge/view: downstream complexity consequences expressed only in the parameter layer

The previous file kept a second public theorem whose only role was to repackage the canonical
chapter theorem. This numbered item is just a direct recall of the theorem already stated on the
chapter's canonical `FirstOrderOracle` / `HasCoordinateSupportGrowth` /
`SatisfiesLinearSpanCondition` surface. -/

/- Theorem 3.2.5 is the earlier chapter theorem
`exists_stronglyConvexLipschitzProblem_with_span_method_lower_bound`. -/
recall exists_stronglyConvexLipschitzProblem_with_span_method_lower_bound
