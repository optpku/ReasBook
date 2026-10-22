/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 3.54 is a recall-only item in the measure-theoretic convex-geometry domain of
centroids of subsets of `ℝⁿ`.

Sampled owner-style declarations:
- `setAverage`, the core normalized-average construction on measurable sets;
- `setAverage_eq`, the canonical normalized-integral formula for that owner;
- `Convex.set_average_mem`, the downstream convex-geometry owner lemma showing centroid membership
  is derived from set averages.

Best owner abstraction:
- source-facing: the textbook centroid of a set
- core/canonical: `setAverage`
- bridge/view: `setAverage_eq` specialized to the identity map on `S`

Primitive data:
- a set `S : Set E`

Derived API:
- the centroid expression `⨍ x in S, x`, given directly by the owner `setAverage`;
- the normalized-integral formula obtained directly from `setAverage_eq`

This file is now recall-only: the previous public alias `centerOfGravity` duplicated the canonical
mathlib owner `setAverage` with no extra mathematics. The centroid surface is therefore expressed
directly by the set-average notation, and the normalized-integral formula remains owned by
`setAverage_eq`.
-/

section

variable (S : Set E)

/- Definition 3.54: the center of gravity of a set `S ⊆ ℝⁿ` is the canonical Lebesgue
set-average construction specialized to the identity map on `S`. -/
#check (⨍ x in S, x ∂volume : E)

/- The normalized-integral formula for the centroid is the identity-function specialization of the
owner theorem `setAverage_eq`. -/
#check (setAverage_eq volume (fun x : E ↦ x) S)

end

end
