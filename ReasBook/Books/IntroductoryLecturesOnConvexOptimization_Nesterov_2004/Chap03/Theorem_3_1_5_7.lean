/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_19

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.5.7 is a recall-only surface in the chapter's extended-valued convex-analysis /
common-subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`
- `eq_add_inner_of_mem_commonRegularSubdifferential` in `Theorem_3_1_19`
- `map_segment_eq_of_commonRegularSubdifferential_nonempty` in `Theorem_3_1_19`

Best owner abstraction:
- the intrinsic common-regular-subdifferential owner theorems in `Theorem_3_1_19`,
  now stated on arbitrary real inner-product spaces rather than only on the Euclidean model

Primitive data:
- none in this file; the common-subgradient owner objects and both source-facing consequences
  already live upstream

Derived API:
- this numbered recall surface for the affine-increment identity and the affine-on-segments
  consequence

Source/core/bridge triage:
- source-facing: the textbook consequences of a nonempty common regular subdifferential
- core/canonical: `commonRegularSubdifferential` together with the owner theorems
  `eq_add_inner_of_mem_commonRegularSubdifferential` and
  `map_segment_eq_of_commonRegularSubdifferential_nonempty`
- bridge/view: this numbered recall surface

The previous version duplicated the affine-increment theorem with the same public name as the
upstream owner theorem and added a second renamed segment-affinity theorem carrying extra unused
hypotheses. The owner theorems also used to be fixed to `EuclideanSpace ℝ (Fin n)`, even though
their owner notion `commonRegularSubdifferential` is already intrinsic. Since there are no
downstream users of the duplicate local names, this file now reuses the generalized canonical
owner theorems directly instead of maintaining either a parallel wrapper API or a Euclidean-only
recall surface. -/

/- Theorem 3.1.5.7: every common subgradient `g ∈ ∂̂ f(X)` gives the affine increment formula
`f x₁ = f x₀ + ⟪g, x₁ - x₀⟫` on `X`. -/
recall eq_add_inner_of_mem_commonRegularSubdifferential

/- If the common regular subdifferential of a convex function on `X` is nonempty, then the
function is affine on every segment contained in `X`. -/
recall map_segment_eq_of_commonRegularSubdifferential_nonempty
