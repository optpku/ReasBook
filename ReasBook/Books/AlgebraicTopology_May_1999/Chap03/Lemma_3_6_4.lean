/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import AlgebraicTopology_May_1999.Chap03.Construction_3_6_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]

/- Lemma 3.6.4 (1): the canonical projection
`CategoryOfElements.π (associatedAction b (End b ⧸ H)) : E(G/H) ⥤ B`
is a covering functor. -/
recall orbitCategoryAssociatedAction_elements_isCovering
    (b : B) [CategoryTheory.IsConnected B] (H : O(End b)) :
    Functor.IsCovering (CategoryOfElements.π (associatedAction b (End b ⧸ H)))

/-- Lemma 3.6.4 (2): at the canonical object `e = H`, a loop at `b` lies in the image subgroup
of the vertex group under the covering projection exactly when it lies in `H`. -/
theorem orbitCategoryAssociatedAction_basepoint_mem_mapVertexGroup_range_iff_mem (b : B)
    (H : O(End b)) (γ : End b) :
    γ ∈ ((CategoryOfElements.π (associatedAction b (End b ⧸ H))).mapVertexGroup
      (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) (𝟙 b))).range ↔ γ ∈ H := by
  simpa [MonoidHom.mem_range] using
    (exists_orbitSubgroupCoveringHom_iff b (H : Subgroup (End b)) (𝟙 b) (𝟙 b) γ)
