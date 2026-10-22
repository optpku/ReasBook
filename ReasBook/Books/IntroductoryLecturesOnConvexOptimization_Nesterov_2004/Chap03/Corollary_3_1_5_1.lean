/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 3.1.5.1 lies in the chapter's extended-valued convex-analysis / subgradient domain.

Primary domain:
- subgradients and subdifferentials for `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `IsSubgradientAt`
- `subdifferential`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- `subgradient_inner_sub_nonneg_of_isMinOn`

Best owner abstraction:
- the subdifferential owner API together with the minimizer-pairing theorem
  `subgradient_inner_sub_nonneg_of_isMinOn`

Primitive data:
- a feasible set `Q`, an extended-real objective `f`, points `x0`, `xStar`, `g`
- the feasibility hypothesis `x0 ∈ Q`
- the minimizing hypothesis `IsMinOn f Q xStar`

Derived API:
- the subgradient-membership view `g ∈ subdifferential f x0`
- the pairing inequality `0 ≤ inner ℝ g (x0 - xStar)`

Source/core/bridge triage:
- source-facing: the corollary that a subgradient at a feasible point has nonnegative pairing with
  the displacement to a minimizer
- core/canonical: `subdifferential` and the owner theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- bridge/view: the chapter theorem `subgradient_inner_sub_nonneg_of_isMinOn`

The previous file introduced a second public theorem whose only extra step was rewriting the
primitive predicate `IsSubgradientAt` as membership in the owner set `subdifferential` via
`mem_subdifferential_iff`, and it had no downstream users. This file therefore recalls the
canonical chapter theorem directly instead of keeping a parallel wrapper around the owner
abstraction. -/

recall subgradient_inner_sub_nonneg_of_isMinOn
