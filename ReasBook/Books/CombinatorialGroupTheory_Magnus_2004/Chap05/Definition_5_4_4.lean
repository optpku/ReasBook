/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_2

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

open Set Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary regions in planar map theory.

Layer triage:
- `source-facing`: for a chosen region `D` of a planar map `M`, the intersection `∂D ∩ ∂M`
  should be realized by a consecutive string of closed edges that appears along both the boundary
  of `D` and some boundary cycle of `M`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map,
  `TwoComplex.GeometricFace` is the owner of an unoriented region, `boundary`, `region`, and
  `geometricEdgeSet` are the source-facing planar subsets, and `IsBoundaryCycle` from
  Definition `5-4-2` is the existing owner predicate for boundary cycles of the whole map.
- `bridge/view`: `Quiver.Path.CyclicPath.HasPart` is the owner predicate for a consecutive segment
  of a cyclic boundary path, and `TwoComplex.boundaryArrowGeometricEdge` maps that total-arrow
  segment to the corresponding geometric-edge string used in the source statement.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the existing owner
   for ambient boundary cycles of a surface embedding.
2. `TwoComplex.boundaryArrowGeometricEdge` from Definition `5-1-1` is the canonical bridge from
   an oriented boundary arrow to the underlying closed geometric edge.
3. `Quiver.Path.CyclicPath.HasPart` is the owner-side consecutive-segment predicate on cyclic
   boundary data; it packages the representative-loop plus `List.IsInfix` formulation once.
4. `frontier (embedding.region D)` and `embedding.boundary` are the source-facing subsets for
   `∂D` and `∂M`, while `embedding.geometricEdgeSet e` is the closed edge corresponding to `e`.
-/

namespace Quiver.Path

/-- A cyclic path contains the consecutive part `part` when some representative loop has `part`
as a contiguous block in its total-edge list. -/
def CyclicPath.HasPart {V : Type*} [Quiver V] (c : CyclicPath V) (part : List (Quiver.Total V)) :
    Prop :=
  ∃ p : Loop V, cyclicPath p = c ∧ List.IsInfix part p.2.edgeList

end Quiver.Path

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- The planar support obtained by taking the union of the closed edges listed in `edges`. -/
private def edgeSequenceSupport (embedding : TwoManifoldEmbedding C 𝔼²)
    (edges : List (OneComplex.GeometricEdge C.skeleton)) : Set 𝔼² :=
  sUnion (embedding.geometricEdgeSet '' { e | e ∈ edges })

/-- A list of geometric edges occurs consecutively in the boundary of a geometric face when some
oriented representative of that face has a boundary cycle containing the list as a contiguous
block. -/
private def GeometricFaceHasConsecutiveEdgeSequence (C : TwoComplex) (D : GeometricFace C)
    (edges : List (OneComplex.GeometricEdge C.skeleton)) : Prop :=
  ∃ F : C.Face,
    (⟦F⟧ : GeometricFace C) = D ∧
      ∃ part : List (Quiver.Total C.skeleton),
        (C.boundary F).HasPart part ∧ part.map C.boundaryArrowGeometricEdge = edges

/-- A list of geometric edges occurs consecutively in the boundary of the planar map when some
boundary cycle of the map contains that list as a contiguous block. -/
private def BoundaryCycleHasConsecutiveEdgeSequence (embedding : TwoManifoldEmbedding C 𝔼²)
    (edges : List (OneComplex.GeometricEdge C.skeleton)) : Prop :=
  ∃ c : CyclicPath C.skeleton,
    IsBoundaryCycle embedding c ∧
      ∃ part : List (Quiver.Total C.skeleton),
        c.HasPart part ∧ part.map C.boundaryArrowGeometricEdge = edges

/-- Definition 5-4-4: the intersection `∂D ∩ ∂M` is a consecutive part of the planar map when it
is the union of a nonempty consecutive sequence of closed edges that occurs along a boundary cycle
of the region `D` and along some boundary cycle of the whole map. -/
def BoundaryIntersectionIsConsecutivePart (embedding : TwoManifoldEmbedding C 𝔼²)
    (D : GeometricFace C) : Prop :=
  ∃ edges : List (OneComplex.GeometricEdge C.skeleton),
    edges ≠ [] ∧
      frontier (embedding.region D) ∩ embedding.boundary = edgeSequenceSupport embedding edges ∧
      GeometricFaceHasConsecutiveEdgeSequence C D edges ∧
        BoundaryCycleHasConsecutiveEdgeSequence embedding edges

end

end TwoManifoldEmbedding
end TwoComplex
