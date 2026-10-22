/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.2 is a recall-only item in the metric / norm-ball domain.

Sampled owner-style declarations:
- `Metric.closedBall`
- `Metric.mem_closedBall`
- `mem_closedBall_zero_iff`
- `mem_closedBall_iff_norm`

Best owner abstraction:
- source-facing: `Metric.closedBall (0 : E) r`
- core/canonical: `Metric.closedBall`
- bridge/view: `mem_closedBall_zero_iff`

Primitive data:
- a seminormed additive group `E`
- a radius `r : ℝ`

Derived API:
- the zero-center membership view `mem_closedBall_zero_iff`

The previous `normBall` and `mem_normBall_iff` declarations were exact-interface duplicates of the
canonical metric closed ball at the origin and its standard norm-bound membership theorem. This
file therefore recalls the canonical owner expression directly instead of keeping a parallel local
wrapper. -/

universe u

section

variable {E : Type u} [SeminormedAddGroup E]
variable (r : ℝ) (a : E)

/- Definition 7.2: the textbook norm ball `B_{‖·‖}(r)` centered at the origin is exactly the
canonical metric closed ball `Metric.closedBall (0 : E) r`. -/
#check (Metric.closedBall (0 : E) r : Set E)

/- Membership in the origin-centered norm ball is exactly the standard norm-bound characterization.
-/
#check (show a ∈ Metric.closedBall (0 : E) r ↔ ‖a‖ ≤ r from mem_closedBall_zero_iff)

end
