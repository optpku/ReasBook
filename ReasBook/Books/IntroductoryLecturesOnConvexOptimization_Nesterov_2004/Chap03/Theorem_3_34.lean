/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_27

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.34 lies in the chapter's equality-constrained convex optimality domain.

Sampled owner declarations in this domain:
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the chapter owner of the feasible
  set cut out by `x ∈ Q` and `A x = b`
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative of an `ℝ ∪ {+∞}`-valued objective
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients
- `isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound` in
  `Theorem_3_1_27`, the intrinsic linear-map optimality criterion already carrying the exact
  mathematical content needed here
- the real-valued constrained-subdifferential surface `g ∈ ∂[Q] f(x)` in `Theorem_3_44`, the later
  chapter notation for relative subgradients

Best owner abstraction:
- core/canonical:
  `isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound`

Primitive data:
- a feasible set `Q`
- an extended-real-valued convex objective `f`
- a linear map `A`
- a right-hand side `b`
- a Slater point `xBar` with a feasible ball `Metric.ball xBar ε ⊆ Q`

Derived API:
- the feasibility conclusion `A xStar = b`
- a multiplier/subgradient witness with `gStar ∈ ∂ f(xStar)`
- the adjoint-norm bound coming from the Slater-ball value gap

Source/core/bridge triage:
- source-facing: the textbook matrix presentation with `Aᵀ` and a relative subgradient on `Q`
- core/canonical: the intrinsic linear-map theorem from `Theorem_3_1_27`
- bridge/view: the matrix specialization `A := A.toEuclideanLin` together with the transpose /
  adjoint identification and the real-valued relative-subgradient notation

The previous version duplicated the owner theorem at the coordinate `Matrix` / `EuclideanSpace`
level. This file now keeps Theorem 3.34 as a direct recall of the intrinsic chapter owner; the
textbook `Aᵀ` specialization is a downstream bridge/view, not a second public owner theorem.
-/

/- Theorem 3.34 is the intrinsic linear-map theorem
`isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound`; the textbook
matrix form is the downstream specialization via `A.toEuclideanLin` and the standard
transpose/adjoint identification. -/
recall isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound
