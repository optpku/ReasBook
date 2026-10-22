/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_22

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.5.5 is a recall-only item in the chapter's extended-valued convex-analysis /
subgradient / supporting-nesterovHyperplane domain.

Primary domain:
- subgradients of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces and their
  supporting-nesterovHyperplane consequences for sublevel sets.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`
- `IsSupportingHyperplane` in `Definition_3_1_4_1`
- `subgradient_nonpos_on_sublevelSet_of_mem_subdifferential`
- `subgradient_isSupportingHyperplane_sublevelSet_of_mem_subdifferential`

Best owner abstraction:
- the subdifferential owner API `g ∈ subdifferential f x0`, with supporting-nesterovHyperplane data derived
  through `IsSupportingHyperplane`.

Primitive data:
- an extended-valued function `f`, a base point `x0`, and a subgradient vector `g`
- the owner membership hypothesis `g ∈ subdifferential f x0`
- the nonvanishing hypothesis `g ≠ 0` for the supporting-nesterovHyperplane conclusion

Derived API:
- the sublevel-set inequality `⟪g, x - x0⟫ ≤ 0`
- the supporting-nesterovHyperplane conclusion for `{x | f x ≤ f x0}`

Source/core/bridge triage:
- source-facing: the sublevel-set support consequence of a subgradient at `x0`
- core/canonical: the owner subdifferential API and the nesterovHyperplane-support owner
  `IsSupportingHyperplane`
- bridge/view: none needed here beyond direct recall of the existing owner-based theorems

This file previously duplicated the subgradient inequality and supporting-nesterovHyperplane conclusion by
storing the owner predicate data in unpacked form (`hx0` together with the affine lower-support
family `hg`). The chapter already has the canonical owner-based statements in `Theorem_3_22`, and
the duplicate local theorem names had no downstream users. With `Theorem_3_22` now lifted from the
Euclidean model layer to the intrinsic real-inner-product-space owner layer, this file recalls the
canonical theorems directly instead of keeping a parallel wrapper API around `subdifferential`. -/

/- Theorem 3.1.5.5: every subgradient `g ∈ ∂f(x₀)` is a supporting vector to the sublevel set
`{x | f x ≤ f x₀}`, equivalently `⟪g, x - x₀⟫ ≤ 0` for every point of that set. -/
recall subgradient_nonpos_on_sublevelSet_of_mem_subdifferential

/- A nonzero subgradient at `x₀` yields a supporting nesterovHyperplane to the sublevel set
`{x | f x ≤ f x₀}`. -/
recall subgradient_isSupportingHyperplane_sublevelSet_of_mem_subdifferential
