/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

universe u

section

variable {E : Type u} [PseudoMetricSpace E]

/- Definition 2.34 lies in the distance-to-set / projection domain.

Sampled owner-style declarations:
* `Metric.infDist`, the canonical distance-to-set owner;
* `Metric.lipschitz_infDist_pt`, showing that pointwise distance-to-set constructions are owned by
  `Metric.infDist`;
* `Metric.continuous_infDist_pt`, the intrinsic continuity bridge attached to the same owner;
* `IsProjectionPointOn Q x p` in `Chap07/Definition_7_3`, the project owner predicate for nearest
  points, used only in the normed bridge below.

Source/core/bridge triage:
* source-facing: the half squared distance to a set;
* core/canonical: `Metric.infDist`;
* bridge/view: the projection-point evaluation formula below.

Primitive data:
* the set `Q` and the ambient point `x`.

Derived API:
* continuity/Lipschitz consequences inherited from `Metric.infDist`;
* the projection-point evaluation formula.

Accordingly, this file exposes the source-facing owner directly as a set-based function derived
from `Metric.infDist`, without hard-coding convexity or the Euclidean `ℝⁿ` display model into the
public owner. -/

/-- Definition 2.34: the half squared distance to a set sends `x` to one half of the square of
its minimal distance to `Q`. The textbook Euclidean statement is the specialization to `ℝⁿ`. -/
def Set.halfSquaredDistance (Q : Set E) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * infDist x Q ^ 2

end

section

variable {E : Type u} [SeminormedAddCommGroup E]

/-- For any projection point `p` of `x` onto `Q`, the half squared distance equals one half of
the squared norm of the displacement `x - p`. -/
-- Proof sketch: if `p` is a projection point of `x` onto `Q`, then by definition
-- `‖x - p‖ = infDist x Q`. Substitute this equality into the definition based on `Metric.infDist`.
theorem IsProjectionPointOn.halfSquaredDistance_eq
    {Q : Set E} {x p : E} (hp : IsProjectionPointOn Q x p) :
    Q.halfSquaredDistance x = (1 / 2 : ℝ) * ‖x - p‖ ^ 2 := by
  simp [Set.halfSquaredDistance, hp.2.symm, dist_eq_norm]

end

end
