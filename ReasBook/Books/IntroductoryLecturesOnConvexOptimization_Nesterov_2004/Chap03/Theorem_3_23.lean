/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.23 lies in the chapter's extended-valued convex-analysis / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`
- `subdifferential`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- `subgradient_inner_sub_nonneg_of_isMinOn`

Best owner abstraction:
- the intrinsic subdifferential owner `subdifferential` together with the minimizer theorem
  `subgradient_inner_sub_nonneg_of_isMinOn`

Primitive data:
- a feasible set `Q`, an extended-real objective `f`, points `x0`, `xStar`, `g`
- the feasibility hypothesis `hx0 : x0 ∈ Q`
- the minimizing hypothesis `hxStar : IsMinOn f Q xStar`
- the owner-membership hypothesis `hg : g ∈ subdifferential f x0`

Derived API:
- the nonnegative pairing inequality `0 ≤ inner ℝ g (x0 - xStar)`

Source/core/bridge triage:
- source-facing: this textbook minimizer-pairing theorem
- core/canonical: `subdifferential`, `IsSubgradientAt`, `IsMinOn`, and the theorem
  `subgradient_inner_sub_nonneg_of_isMinOn`
- bridge/view: the former Euclidean/closed/convex wrapper, now deleted because its extra
  hypotheses were redundant and created a duplicate theorem surface

The earlier version of this file reintroduced a second public theorem with the same name and
mathematical content, but on an over-concrete Euclidean wrapper API carrying unused convexity,
closedness, nonemptiness, and domain hypotheses. The intrinsic owner theorem already exists in
`Theorem_3_1_5_6` with the exact source-facing conclusion, so this item is now a direct recall
instead of a parallel duplicate. -/

recall subgradient_inner_sub_nonneg_of_isMinOn
