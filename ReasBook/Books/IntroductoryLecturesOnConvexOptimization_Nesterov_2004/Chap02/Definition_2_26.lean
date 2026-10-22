/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.ReciprocalEpigraphOnPositiveRay

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 2.26 is a source-facing recall in the convex-geometry domain of epigraphs in `ℝ²`.

Primary domain:
- the epigraph of the reciprocal map `x ↦ 1 / x` on the positive ray.

Sampled owner-style declarations:
- `reciprocalEpigraphOnPositiveRay`, the Chapter 2 owner set for the textbook region `Q`;
- `mem_reciprocalEpigraphOnPositiveRay_iff`, the owner membership criterion;
- `ConvexOn.convex_epigraph`, the mathlib owner theorem expressing the general epigraph style;
- `convexOn_iff_convex_epigraph`, the canonical bridge between convexity and epigraph convexity.

Best owner abstraction:
- `reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)`

Primitive data:
- the positivity condition `0 < x.1`;
- the epigraph inequality `x.2 ≥ 1 / x.1`.

Derived API:
- the additional displayed condition `0 ≤ x.2`, since `0 < x.1` implies `0 < 1 / x.1`.

Source/core/bridge triage:
- source-facing: the textbook set `Q = {(x₁, x₂) | 0 < x₁, x₂ ≥ 1 / x₁}`;
- core/canonical: `reciprocalEpigraphOnPositiveRay`;
- bridge/view: `mem_reciprocalEpigraphOnPositiveRay_iff`.

This recall file therefore introduces no parallel local definition such as
`positiveReciprocalEpigraph`; downstream use should refer directly to the owner set and its
companion membership theorem. -/

recall reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)

recall mem_reciprocalEpigraphOnPositiveRay_iff
    (x : ℝ × ℝ) :
    x ∈ reciprocalEpigraphOnPositiveRay ↔ 0 < x.1 ∧ x.2 ≥ 1 / x.1
