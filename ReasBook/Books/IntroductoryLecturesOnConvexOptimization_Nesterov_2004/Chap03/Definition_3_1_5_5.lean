/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

/- Definition 3.1.5.5 lies in the source-facing domain of bounded intersections for set-valued
maps.

Primary domain:
- bounded intersections of set-valued maps.

Sampled owner-style declarations:
- `Set.iInter`;
- `Set.mem_iInter₂`.

Best owner abstraction:
- the common-value set attached to a set-valued map on a set.

Primitive data:
- a domain type `α`;
- a codomain type `β`;
- a set-valued map `S : α → Set β`;
- an index set `X : Set α`.

Derived API:
- the bounded-intersection owner `⋂ x ∈ X, S x`;
- the membership bridge `Set.mem_iInter₂`.

Source/core/bridge triage:
- source-facing: `commonValueSet`;
- core/canonical: `Set.iInter`;
- bridge/view: `Set.mem_iInter₂`.

This file keeps the source-facing object aligned with the textbook notation `\hat{\mathcal S}(X)`
while realizing it directly by the canonical bounded intersection over `X`. -/

section

variable {α : Type u} {β : Type v}

/-- Definition 3.1.5.5: for a set-valued map `S` and a set `X`, the common-value set
`\hat{\mathcal S}(X)` is the bounded intersection `⋂ x ∈ X, S x`. -/
def commonValueSet (S : α → Set β) (X : Set α) : Set β :=
  ⋂ x ∈ X, S x

/-- Helper for Definition 3.1.5.5: membership in the common-value set is equivalent to belonging
to every value `S x` with `x ∈ X`. -/
theorem mem_commonValueSet_iff {S : α → Set β} {X : Set α} {y : β} :
    y ∈ commonValueSet S X ↔ ∀ x ∈ X, y ∈ S x := by
  -- Unfold the source-facing owner to the canonical bounded intersection.
  change y ∈ (⋂ x ∈ X, S x : Set β) ↔ ∀ x ∈ X, y ∈ S x
  -- The generic owner theorem for bounded intersections closes the membership bridge.
  exact Set.mem_iInter₂

end
