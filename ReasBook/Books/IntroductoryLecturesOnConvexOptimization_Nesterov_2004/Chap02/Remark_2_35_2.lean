/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient

universe u

/- Remark 2.35.2 is a recall-only item in the projected-gradient / Euclidean-projection domain on
nonempty closed convex sets in a complete real inner-product space. The textbook `ℝⁿ` statement is
the specialization `E = EuclideanSpace ℝ (Fin n)`.

Primary domain:
* the ambient projected-gradient point `x_Q(xBar; γ)`, defined by projecting the explicit
  gradient step from an arbitrary ambient base point `xBar : E`.

Owner declarations sampled for this refinement:
* `gradientMapping` in `Definition_2_35_1`, the source-facing projected-gradient point;
* `gradientMapping_isProjectionPointOn` in `Definition_2_35_1`, the chapter's source-facing
  projection-point bridge for that projected-gradient point;
* `euclideanProjection` in `Theorem_2_33`, the lower owner used internally by
  `gradientMapping`;
* `gradientMapping_eq_point_sub_inv_smul_reducedGradient` in `Remark_2_35_1`, the later
  source-facing step identity derived from the same owner.

Best owner abstraction:
* `gradientMapping`.

Primitive data:
* the feasible set `Q` with nonempty / closed / convex structure;
* the objective `f`, the ambient base point `xBar`, and the parameter `γ`;
* the complete real inner-product-space structure on `E`, which is exactly the ambient owner layer
  used by `gradientMapping` and `euclideanProjection`.

Derived API:
* `gradientMapping_isProjectionPointOn`, the direct source-facing projection-point bridge;
* the later step identity `gradientMapping_eq_point_sub_inv_smul_reducedGradient`.

Source/core/bridge triage:
* source-facing: the remark that `x_Q(xBar; γ)` is well-defined for every ambient `xBar : E`,
  with no hypothesis `xBar ∈ Q`;
* core/canonical: `gradientMapping`;
* bridge/view: `gradientMapping_isProjectionPointOn`.

Accordingly, this file stays at the owner level: it recalls `gradientMapping` directly in the
general ambient space where it is defined, and recalls its chapter-local projection-point bridge
instead of dropping back to the lower `euclideanProjection` interface or re-specializing either
declaration to `ℝⁿ`. -/

recall gradientMapping
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E

recall gradientMapping_isProjectionPointOn
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (γ : NNRealˣ) (xBar : E) :
    IsProjectionPointOn Q (gradientStep f xBar γ)
      x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)
