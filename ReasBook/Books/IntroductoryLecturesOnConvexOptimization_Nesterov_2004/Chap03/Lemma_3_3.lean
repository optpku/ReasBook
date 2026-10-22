/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- Lemma 3.3 lies in the chapter's support-function / convex-hull domain.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_eq`
- mathlib `sSup_union`

Best owner abstraction:
- the chapter owner `supportFunction` together with its canonical convex-hull invariance theorem
  `supportFunction_convexHull_eq`

Primitive data:
- two sets `Q₁ Q₂ : Set E`

Derived API:
- the textbook pointwise specialization
  `ξ[convexHull ℝ (Q₁ ∪ Q₂)] x = max (ξ[Q₁] x) (ξ[Q₂] x)`

Source/core/bridge triage:
- source-facing: `supportFunction_convexHull_union_eq_max`
- core/canonical: `supportFunction` and `supportFunction_convexHull_eq`
- bridge/view: `supportFunction_apply` and `sSup_union`
-/

recall supportFunction

recall supportFunction_apply

recall supportFunction_convexHull_eq

/-- Lemma 3.3: in a real inner-product space, the support function of the convex hull of
`Q₁ ∪ Q₂` is the pointwise maximum of the support functions of `Q₁` and `Q₂`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: rewrite away the convex hull by `supportFunction_convexHull_eq`, then expand the
-- support function of the union with `supportFunction_apply` and `sSup_union`.
theorem supportFunction_convexHull_union_eq_max
    (Q₁ Q₂ : Set E) (x : E) :
    ξ[convexHull ℝ (Q₁ ∪ Q₂)] x = max (ξ[Q₁] x) (ξ[Q₂] x) := by
  rw [supportFunction_convexHull_eq]
  simp [supportFunction_apply, Set.image_union, sSup_union]

end
