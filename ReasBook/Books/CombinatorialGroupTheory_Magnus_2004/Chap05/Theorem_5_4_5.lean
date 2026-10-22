/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Corollary_5_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_4

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for simply connected planar `(q, p)` maps with the
source-facing starred sum over boundary regions whose boundary intersection with the whole map is a
consecutive part of the ambient boundary.

Layer triage:
- `source-facing`: the starred curvature sum of Theorem `5-4-5`, indexed by those regions `D`
  for which `∂D ∩ ∂M` is a consecutive part of `∂M`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner of the planar map,
  `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner of the `(q, p)` condition,
  `TwoComplex.TwoManifoldEmbedding.adjustedInteriorEdgeDefectSum` is the owner construction for the
  curvature sum attached to a selected family of regions,
  `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` is the owner of the source quantity
  `i(D)`, and `TwoComplex.TwoManifoldEmbedding.BoundaryIntersectionIsConsecutivePart` from Definition
  `5-4-4` is the owner predicate selecting the starred summation domain.
- `bridge/view`: the textbook starred sum is the specialization of
  `adjustedInteriorEdgeDefectSum` to the consecutive-boundary-intersection predicate, while
  the source hypothesis that a region boundary contains no boundary edge of the ambient map is the
  inclusion `C.boundaryGeometricEdges D ⊆ {e | embedding.IsInteriorEdge e}`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum` from
   `Corollary_5_3_5.lean` is the existing owner for the bullet-sum version over all boundary
   regions.
2. `TwoComplex.TwoManifoldEmbedding.BoundaryIntersectionIsConsecutivePart` from
   `Definition_5_4_4.lean` is the source-facing owner for the extra starred-sum restriction.
3. `OneComplex.vertexDegree` and `TwoComplex.regionCount` are the chapter owners
   for the no-degree-one and more-than-one-region hypotheses.
4. `TwoComplex.boundaryGeometricEdges` and
   `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` are the owner APIs for the source condition
   that a region boundary contains no boundary edge of the ambient map.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: first handle the case where the map boundary is a simple closed path by
-- induction on the number of regions. If every boundary region has consecutive boundary
-- intersection, apply Corollary `5-3-5`; otherwise choose a region whose boundary intersection is
-- not consecutive, split the map along that region into two smaller maps, apply the induction
-- hypothesis to both pieces, and combine the resulting starred sums. When the boundary is not a
-- simple closed path, use Lemma `5-4-3` to obtain two extremal disks and add their contributions
-- to recover the same lower bound for the ambient starred sum.
/-- Theorem 5-4-5: in a connected simply connected `(q, p)` map with no vertices of degree `1`
and more than one region, if every region whose boundary contains no boundary edge of the ambient
map has degree at least `p`, then the starred curvature sum
`∑_M^* [p / q + 2 - i(D)]` is at least `p`. -/
theorem consecutiveBoundaryRegion_curvature_formula_lower_bound_of_simplyConnected_roundBracketQPMap
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [TwoComplex.IsSimplyConnected C]
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hQP : embedding Is(q, p))
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hnoDegreeOne :
      let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
      ∀ v : C.skeleton, C.skeleton.vertexDegree v ≠ 1)
    (hmoreThanOneRegion : (1 : ℚ) < embedding.regionCount)
    (hRegionDegree :
      ∀ D : GeometricFace C,
        C.boundaryGeometricEdges D ⊆
          { e : OneComplex.GeometricEdge C.skeleton | embedding.IsInteriorEdge e } →
          p ≤ C.regionDegree D) :
    (p : ℚ) ≤
      embedding.adjustedInteriorEdgeDefectSum embedding.BoundaryIntersectionIsConsecutivePart p q :=
  sorry

end

end TwoManifoldEmbedding
end TwoComplex
