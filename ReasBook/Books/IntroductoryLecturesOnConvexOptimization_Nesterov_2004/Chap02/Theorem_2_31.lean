/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_39

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 2.31 corresponds to the textbook Theorem 2.3.1, the constrained optimality criterion
for the max-type problem `min_{x ∈ Q} max_i fᵢ(x)` on `ℝⁿ`.

Primary domain:
* constrained finite max-type convex minimization in the Euclidean textbook presentation

Sampled owner-style declarations:
* `maxTypeObjective` in `Lemma_2_18`, the owner max objective of a nonempty finite family;
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max model at a base point;
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`, the chapter's
  constrained first-order optimality owner behind the max-type criterion;
* `isMinOn_maxTypeObjective_iff_affineApproximation_ge` in `Theorem_2_39`, the canonical
  project-level theorem with the exact mathematical content of Theorem 2.3.1.

Best owner abstraction:
* `isMinOn_maxTypeObjective_iff_affineApproximation_ge`

Primitive data:
* the feasible set `Q`;
* the component family `fs`;
* componentwise convexity on `Q`;
* feasibility of the base point `xStar`;
* differentiability of each component at `xStar`.

Derived API:
* the constrained minimizing predicate `IsMinOn (maxTypeObjective fs) Q xStar`;
* the affine lower-model condition
  `∀ x ∈ Q, maxTypeAffineApproximation fs xStar x ≥ maxTypeObjective fs xStar`.

Source/core/bridge triage:
* source-facing: Theorem 2.3.1 in the textbook `ℝⁿ` / `Fin m` presentation;
* core/canonical: `isMinOn_maxTypeObjective_iff_affineApproximation_ge`;
* bridge/view: the specialization `E = EuclideanSpace ℝ (Fin n)` and `ι = Fin m`.

This file therefore keeps no parallel local theorem shell. The numbered textbook item is recalled
directly from the existing chapter owner theorem at the correct abstraction level. -/

/- Theorem 2.31 / Theorem 2.3.1 is the direct owner recall of the constrained max-type
optimality criterion. The textbook `ℝⁿ` / `Fin m` formulation is the Euclidean specialization of
this owner theorem. -/
recall isMinOn_maxTypeObjective_iff_affineApproximation_ge
