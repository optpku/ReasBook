/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33

noncomputable section

open Metric

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 2.13 lies in the real-inner-product projection domain.

Sampled owner-style declarations:
* `IsProjectionPointOn Q x₀ p` in `Chap07/Definition_7_3`, the project owner predicate for
  nearest-point data;
* `IsProjectionPointOn.isMinOn` in `Definition_2_33`, the project bridge from projection data to
  the minimizing property of `y ↦ ‖y - x₀‖`;
* `norm_eq_iInf_iff_real_inner_le_zero` from mathlib's projection-minimal API, the owner theorem
  converting the minimizing equality on a convex set into the standard variational inequality.

Source/core/bridge triage:
* source-facing: the textbook variational inequality for a projection point onto a convex set;
* core/canonical: `IsProjectionPointOn Q x₀ p`;
* bridge/view: the inner-product inequality derived from the minimizing characterization.

Primitive data:
* the set `Q`, ambient point `x₀`, projection point `p`, feasible point `x`, and convexity of
  `Q`.

Derived API:
* feasibility `hp.1`;
* the minimizing equality `hp.2`;
* the minimizing predicate `hp.isMinOn`.

Accordingly, this file keeps only the source-facing inequality and derives it directly from the
owner predicate rather than introducing a parallel nearest-point wrapper. -/

namespace IsProjectionPointOn

/-- Lemma 2.13: if `p` is a projection point of `x₀` onto a convex set `Q` in a real inner
product space, then the displacement `p - x₀` has nonnegative inner product with every feasible
direction `x - p` based at `p`. -/
theorem inner_sub_nonneg
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₀ p x : E}
    (hp : IsProjectionPointOn Q x₀ p) (hx : x ∈ Q) :
    0 ≤ inner ℝ (p - x₀) (x - p) := by
  have hinner : inner ℝ (x₀ - p) (x - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hp.1).1 hp.norm_eq_iInf x hx
  simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonneg.mpr hinner

end IsProjectionPointOn

end
