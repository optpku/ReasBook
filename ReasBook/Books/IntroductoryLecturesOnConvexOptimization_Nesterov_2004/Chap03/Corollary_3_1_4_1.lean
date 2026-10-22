/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Corollary 3.1.4.1 lies in the chapter's affine-nesterovHyperplane strong-separation domain.

Primary domain:
- strong separation of a closed convex set from an exterior point in a real inner-product space.

Relevant sampled declarations:
- `AreStronglySeparable` in `Definition_3_12`, the owner predicate for strong separation;
- `areStronglySeparable_empty_singleton` in `Definition_3_12`, the intrinsic empty-set companion;
- `areStronglySeparable_singleton_of_nonmem_closed_convex` in `Theorem_3_16`, the canonical
  owner-level theorem for the nonempty case;
- `exists_strictlySeparating_hyperplane_of_nonmem_closed_convex` in `Corollary_3_1_4`, the
  downstream coordinate bridge from the owner predicate to `(g, γ)`.

Best owner abstraction:
- `AreStronglySeparable`.

Primitive data:
- the closed convex set `Q`, the exterior point `x`, and, for the canonical owner theorem, the
  genuinely used nonemptiness witness `Q.Nonempty`.

Derived API:
- the owner-level theorem `areStronglySeparable_singleton_of_nonmem_closed_convex`;
- the coordinate `(g, γ)` consequence in `Corollary_3_1_4`.

Source/core/bridge triage:
- source-facing: the chapter corollary asserting strong separation of a closed convex set and an
  exterior point;
- core/canonical: `AreStronglySeparable Q ({x} : Set E)`;
- bridge/view: this file, which now reuses the existing owner theorem directly instead of keeping a
  second Euclidean-space-specialized wrapper.

The previous version introduced a new theorem over `EuclideanSpace ℝ (Fin n)` with a positivity
assumption on `n`, even though the mathematics here is already captured intrinsically by the
earlier owner theorem and the coordinate bridge is already handled in `Corollary_3_1_4`. This file
therefore becomes recall-only: `ℝⁿ` remains available purely as a downstream specialization of the
intrinsic owner statement.
-/

/- Corollary 3.1.4.1 is the direct chapter reuse of the canonical owner theorem for separating a
closed convex set from an exterior point. The coordinate `(g, γ)` form is recovered separately by
`exists_strictlySeparating_hyperplane_of_nonmem_closed_convex`. -/
recall areStronglySeparable_singleton_of_nonmem_closed_convex

end
