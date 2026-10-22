/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.14 is a recall-only file in the chapter's affine-nesterovHyperplane support domain.

Relevant sampled declarations:
- `AffineHyperplane`
- `AffineHyperplane.IsSupporting`
- `IsSupportingHyperplane`
- `exists_supporting_hyperplane_at_boundary_point_of_closed_convex`

Best owner abstraction:
- the earlier source-facing theorem
  `exists_supporting_hyperplane_at_boundary_point_of_closed_convex`, built on the chapter's
  `AffineHyperplane` owner API.

Source/core/bridge triage:
- source-facing: this numbered theorem item;
- core/canonical: the earlier chapter theorem with the same mathematical content;
- bridge/view: this later theorem name, which is only a textual restatement of the same result.

Primitive data:
- the closed convex set `Q` and the boundary point `x₀`.

Derived API:
- the coordinate witness `(g, γ)` together with membership in `nesterovHyperplane g γ` and the predicate
  `IsSupportingHyperplane Q g γ`.

This file previously duplicated the exact theorem surface already provided by
`Theorem_3_1_4_2.lean`. It now reuses that earlier declaration directly instead of keeping a
second parallel theorem with the same statement under a different name.
-/
recall exists_supporting_hyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E}
    (hx₀ : x₀ ∈ frontier Q) :
    ∃ g : E, ∃ γ : ℝ, x₀ ∈ nesterovHyperplane g γ ∧ IsSupportingHyperplane Q g γ

end
