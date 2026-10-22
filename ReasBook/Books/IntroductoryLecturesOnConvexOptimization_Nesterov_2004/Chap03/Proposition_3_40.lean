/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 3.40 lies in the real inner-product-space strong-convexity / quadratic-correction
bridge domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `strongConvexOn_iff_convex`
- chapter `StrongConvexOnWith` in `Definition_2_14`
- chapter `strongConvexOn_iff_quadratic_jensen_bound` in `Theorem_2_10`

Best owner abstraction:
- source-facing: Proposition 3.40's quadratic-corrected convexity statement
- core/canonical: `strongConvexOn_iff_convex`
- bridge/view: this recall-only source-facing entry

Primitive data:
- the ambient real inner product space `E`
- the feasible set `Q`, modulus `μ`, and objective `f`

Derived API:
- convexity of `fun x ↦ f x - μ / (2 : ℝ) * ‖x‖ ^ 2`, directly from the owner theorem

The previous file duplicated the forward direction of the canonical mathlib equivalence
`strongConvexOn_iff_convex` under the local name `StrongConvexOn.convexOn_sub_sq_norm`. This
refinement removes that parallel wrapper and recalls the owner theorem directly. The textbook
positivity hypothesis `μ > 0` is redundant for this bridge and is therefore omitted from the
public API.
-/

/- Proposition 3.40: in a real inner product space, `μ`-strong convexity on `Q` is exactly
convexity of the quadratic-corrected objective. -/
recall strongConvexOn_iff_convex
    {Q : Set E} {μ : ℝ} {f : E → ℝ} :
    StrongConvexOn Q μ f ↔ ConvexOn ℝ Q (fun x ↦ f x - μ / (2 : ℝ) * ‖x‖ ^ 2)
