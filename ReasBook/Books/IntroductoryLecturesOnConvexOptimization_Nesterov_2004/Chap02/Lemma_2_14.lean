/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 2.14 lies in the real-inner-product projection domain.

Sampled owner-style declarations:
* `IsProjectionPointOn Q y p` in `Chap07/Definition_7_3`, the owner predicate for projection data;
* `IsProjectionPointOn.isMinOn` in `Definition_2_33`, the minimizing-property bridge;
* `IsProjectionPointOn.inner_sub_nonneg` in `Lemma_2_13`, the projection variational inequality;
* `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the chosen-point bridge already
  available upstream.

Source/core/bridge triage:
* source-facing: the Pythagorean inequality for a projection point onto a convex set;
* core/canonical: `IsProjectionPointOn Q y p`;
* bridge/view: specializing from the chosen `euclideanProjection` to the owner predicate via
  `euclideanProjection_isProjectionPointOn`.

Primitive data:
* the convex set `Q`, ambient point `y`, projection point `p`, and feasible point `x`.

Derived API:
* the variational inequality `IsProjectionPointOn.inner_sub_nonneg`.

Accordingly, this file keeps only the owner-level theorem. The chosen Euclidean-projection
specialization is already recovered canonically by combining this theorem with
`euclideanProjection_isProjectionPointOn`, and the Euclidean-space statement is just its
specialization to `ℝⁿ`, so no parallel local corollary is kept. -/

namespace IsProjectionPointOn

/-- Lemma 2.14: every feasible point of a convex set in a real inner product space lies no closer
to an ambient point `y` than a projection point `p` does, with the usual Pythagorean
squared-distance decomposition. -/
-- Proof sketch: write `x - y = (x - p) + (p - y)`. The projection variational inequality gives
-- `0 ≤ ⟪x - p, p - y⟫`, and `norm_add_sq_real` then expands `‖x - y‖²` as the left-hand side plus
-- the nonnegative mixed term `2 ⟪x - p, p - y⟫`.
theorem pythagorean_ineq
    {Q : Set E} (hQ_convex : Convex ℝ Q) {y p x : E}
    (hp : IsProjectionPointOn Q y p) (hx : x ∈ Q) :
    ‖x - p‖ ^ 2 + ‖p - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hinner : 0 ≤ inner ℝ (x - p) (p - y) := by
    simpa [real_inner_comm] using hp.inner_sub_nonneg hQ_convex hx
  calc
    ‖x - p‖ ^ 2 + ‖p - y‖ ^ 2
        ≤ ‖x - p‖ ^ 2 + 2 * inner ℝ (x - p) (p - y) + ‖p - y‖ ^ 2 := by
          nlinarith
    _ = ‖(x - p) + (p - y)‖ ^ 2 := by rw [norm_add_sq_real]
    _ = ‖x - y‖ ^ 2 := by abel_nf

end IsProjectionPointOn

end
