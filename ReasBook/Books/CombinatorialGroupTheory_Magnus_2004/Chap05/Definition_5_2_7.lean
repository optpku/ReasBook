/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

open Set

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary and interior cells of a planar map.

Layer triage:
- `source-facing`: the textbook boundary/interior terminology for vertices, edges, and regions of
  a map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map, while
  `vertexSet`, `edge`, `region`, and `boundary` are the source-facing planar subsets attached to
  that owner.
- `bridge/view`: a vertex is viewed in the plane through `vertexMap`, and unoriented edges and
  regions are viewed through `edge` and `region`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding` from Definition `5-1-1` is the chapter owner for a planar map.
2. `TwoManifoldEmbedding.vertexSet`, `TwoManifoldEmbedding.edge`, `TwoManifoldEmbedding.region`, and
   `TwoManifoldEmbedding.boundary` are the canonical source-facing planar pieces used to express the
   textbook boundary conditions.
3. `OneComplex.GeometricEdge` and `TwoComplex.GeometricFace` are the canonical owners for
   unoriented edges and regions, so boundary/interior should be predicates on those existing
   cells rather than a new wrapper structure.

Primitive vs. derived:
- primitive public data: a chosen planar embedding `embedding : TwoManifoldEmbedding C 𝔼²`;
- derived API: the boundary/interior predicates on vertices, geometric edges, and regions of `C`,
  together with the canonical face-boundary support test for boundary regions.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

open OneComplex

variable {C : TwoComplex}

/-- Definition 5-2-7 (1): a boundary vertex of a planar map is a vertex whose image lies on the
boundary of the map. -/
def IsBoundaryVertex (embedding : TwoManifoldEmbedding C 𝔼²) (v : C.skeleton) : Prop :=
  embedding.vertexMap v ∈ embedding.boundary

/-- Definition 5-2-7 (2): a boundary edge of a planar map is a geometric edge whose source-style
edge is contained in the boundary of the map. -/
def IsBoundaryEdge (embedding : TwoManifoldEmbedding C 𝔼²)
    (e : GeometricEdge C.skeleton) : Prop :=
  embedding.edge e ⊆ embedding.boundary

/-- Definition 5-2-7 (3): a boundary region of a planar map is a region whose boundary meets the
boundary of the map. -/
def IsBoundaryRegion (embedding : TwoManifoldEmbedding C 𝔼²) (D : GeometricFace C) : Prop :=
  ((frontier (embedding.region D)) ∩ embedding.boundary).Nonempty

/-- For a planar map, a boundary region is exactly a region whose canonical face-boundary support
meets the boundary of the map. -/
theorem isBoundaryRegion_iff_faceBoundarySupport_inter_boundary_nonempty
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] (D : GeometricFace C) :
    embedding.IsBoundaryRegion D ↔
      (embedding.faceBoundarySupport D ∩ embedding.boundary).Nonempty := by
  change ((frontier (embedding.region D)) ∩ embedding.boundary).Nonempty ↔
    (embedding.faceBoundarySupport D ∩ embedding.boundary).Nonempty
  rw [(inferInstance : embedding.IsPlanarMap).region_boundary_eq_faceBoundarySupport D]

/-- Definition 5-2-7 (4): an interior vertex of a planar map is a vertex that is not a boundary
vertex. -/
abbrev IsInteriorVertex (embedding : TwoManifoldEmbedding C 𝔼²) (v : C.skeleton) : Prop :=
  ¬ embedding.IsBoundaryVertex v

/-- Definition 5-2-7 (5): an interior edge of a planar map is a geometric edge that is not a
boundary edge. -/
abbrev IsInteriorEdge (embedding : TwoManifoldEmbedding C 𝔼²)
    (e : GeometricEdge C.skeleton) : Prop :=
  ¬ embedding.IsBoundaryEdge e

/-- Definition 5-2-7 (6): an interior region of a planar map is a region that is not a boundary
region. -/
abbrev IsInteriorRegion (embedding : TwoManifoldEmbedding C 𝔼²) (D : GeometricFace C) : Prop :=
  ¬ embedding.IsBoundaryRegion D

end

end TwoManifoldEmbedding
end TwoComplex
