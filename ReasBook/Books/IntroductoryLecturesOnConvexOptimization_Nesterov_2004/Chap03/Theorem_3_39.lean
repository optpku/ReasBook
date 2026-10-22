/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped LipschitzConvexProblemClass

/- Domain note: this item lies in the chapter's nonsmooth first-order black-box complexity domain.

Sampled owner-style declarations:
- `IsInLipschitzConvexProblemClass` in `Theorem_3_2_1`, the source-facing owner predicate for the
  class `𝒫(x₀, R, M)`
- `FirstOrderOracle` in `Theorem_3_2_1`, the reusable owner of valid black-box subgradient
  replies
- `SatisfiesLinearSpanCondition` in `Theorem_3_2_1`, the source-facing span predicate for iterate
  sequences
- `exists_problem_with_nonsmooth_firstOrder_lower_bound` in `Theorem_3_2_1`, the canonical
  project theorem with the same mathematical conclusion

Best owner abstraction:
- source-facing: this numbered theorem item
- core/canonical: `exists_problem_with_nonsmooth_firstOrder_lower_bound`
- bridge/view: the Chapter 1 approximate-minimizer language on `SetConstrainedMinimizationProblem`
  used downstream when the same objective-gap estimate is phrased as an approximate solution

Primitive data:
- the dimension `n`
- the starting point `x₀`
- the parameters `R`, `M : NNReal`
- the iterate index `k` with `k + 1 ≤ n`

Derived API:
- existence of a hard instance given by `f`, `xStar`, and
  `IsInLipschitzConvexProblemClass x₀ R M f xStar`
- the lower-bound conclusion for every valid subgradient oracle whose replies satisfy the
  prefix-support-growth condition, together with every iterate sequence satisfying
  `SatisfiesLinearSpanCondition`

Source/core/bridge triage:
- source-facing: Theorem 3.39 [Chapter3_2.json:71] as the textbook hard-instance lower bound
- core/canonical: `exists_problem_with_nonsmooth_firstOrder_lower_bound`
- bridge/view: the approximate-solution language in the Chapter 1 ambient owner

This theorem is semantically identical to the earlier canonical owner theorem
`exists_problem_with_nonsmooth_firstOrder_lower_bound`. The textbook bounds `R > 0`, `M > 0`, and
`0 ≤ k ≤ n - 1` are encoded in the project-facing interface as `R M : NNReal` together with
`k + 1 ≤ n`, so the clean statement for this item is a direct recall of that canonical theorem
rather than a parallel local shell.
-/

/-- Theorem 3.39 [Chapter3_2.json:71]: for `k + 1 ≤ n`, the canonical Chapter 3 hard-instance
theorem `exists_problem_with_nonsmooth_firstOrder_lower_bound` gives a convex Lipschitz objective
in `𝒫(x₀, R, M)` such that every valid first-order oracle satisfying the prefix-support-growth
condition, and every iterate sequence satisfying the linear-span condition for that oracle, has
objective gap at least `MR / (2 (2 + √(k + 1)))` at step `k`. The source inequalities `R > 0`,
`M > 0`, and `0 ≤ k ≤ n - 1` are absorbed by the project-facing parameters `R M : NNReal` and
`k + 1 ≤ n`. -/
-- The proof route is pure theorem reuse: this source-facing item is recalled with its full local
-- theorem surface, so the file stays aligned with the textbook wording without duplicating the
-- Nemirovski hard-instance construction.
recall exists_problem_with_nonsmooth_firstOrder_lower_bound
