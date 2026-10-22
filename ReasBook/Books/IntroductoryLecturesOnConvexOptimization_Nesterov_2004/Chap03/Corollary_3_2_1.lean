/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

/-
Corollary 3.2.1 lies in the constrained strong-convexity / relative-subdifferential domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- `subdifferentialWithin` in `Theorem_3_44`
- `mem_subdifferentialWithin_iff` in `Theorem_3_44`
- `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin` in `Theorem_3_44`

Best owner abstraction:
- core/canonical: the generic lower-bound theorem
  `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`
- supporting owner notions: `StrongConvexOn Q μ f` and `g ∈ ∂[Q] f(x)`

Source/core/bridge triage:
- source-facing: Corollary 3.2.1, the quadratic affine lower bound produced by a feasible
  subgradient of a strongly convex function
- core/canonical: `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`
- bridge/view: none; this file is a direct recall of the owner theorem

Primitive data:
- an inner-product space, feasible set `Q`, objective `f`, modulus `μ`, base point `x`,
  comparison point `y`, and vector `g`
- the owner hypotheses `StrongConvexOn Q μ f`, `g ∈ ∂[Q] f(x)`, and `y ∈ Q`

Derived API:
- the quadratic affine lower bound at `y`

The earlier chapter duplicates of `subdifferentialWithin` are Euclidean-specialized, while
`Theorem_3_44` is the generic inner-product-space owner needed here. This corollary therefore
keeps the owner theorem itself as the public center and adds no parallel local wrapper.
-/
recall StrongConvexOn.lower_bound_of_mem_subdifferentialWithin
