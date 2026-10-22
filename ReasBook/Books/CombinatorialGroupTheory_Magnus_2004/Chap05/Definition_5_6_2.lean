/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_7

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary layers in planar map theory.

Layer triage:
- `source-facing`: the boundary layer of a map is given by its boundary vertices, the geometric
  edges incident with boundary vertices, and its boundary regions.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map, and
  the existing predicates
  `TwoManifoldEmbedding.IsBoundaryVertex` / `TwoManifoldEmbedding.IsBoundaryRegion` from Definition
  `5-2-7` are the canonical boundary-cell predicates.
- `bridge/view`: an unoriented geometric edge is represented by an oriented edge of the
  `1`-skeleton, so incidence with a boundary vertex is expressed by checking whether one of the
  two endpoints of any representative is a boundary vertex.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryVertex` from Definition `5-2-7` is the existing owner
   for boundary vertices of a planar map.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` from Definition `5-2-7` is the existing owner
   for boundary regions of a planar map.
3. `OneComplex.GeometricEdge C.skeleton` is the canonical owner for source-level unoriented
   edges, so “incident with a boundary vertex” should be a predicate on geometric edges rather
   than on oriented representatives.
4. `OneComplex.geometricEdgeSetoid` is the quotient relation identifying an oriented edge with
   its inverse, so it is the correct bridge for making endpoint incidence well defined on
   geometric edges.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

open OneComplex

local notation "GeometricEdge" => OneComplex.GeometricEdge C.skeleton

/-- An oriented edge belongs to the boundary layer when one of its endpoints is a boundary
vertex. -/
private def orientedEdgeIsBoundaryLayer
    (embedding : TwoManifoldEmbedding C 𝔼²) (e : C.skeleton.Edge) : Prop :=
  embedding.IsBoundaryVertex (C.skeleton.initial e) ∨
    embedding.IsBoundaryVertex (C.skeleton.terminal e)

/-- Endpoint incidence with a boundary vertex is unchanged when an oriented edge is replaced by
its inverse, so it descends to the corresponding geometric edge. -/
-- Proof sketch: split the geometric-edge relation into equality or inversion. Equality is
-- immediate, while inversion swaps initial and terminal vertices, leaving the disjunction
-- unchanged.
private theorem orientedEdgeIsBoundaryLayer_eq_of_geometricEdgeSetoid
    (embedding : TwoManifoldEmbedding C 𝔼²) (e f : C.skeleton.Edge)
    (h : (geometricEdgeSetoid C.skeleton).r e f) :
    embedding.orientedEdgeIsBoundaryLayer e = embedding.orientedEdgeIsBoundaryLayer f := by
  rcases h with rfl | rfl
  · rfl
  · apply propext
    have hinit : C.skeleton.initial f⁻¹ = C.skeleton.terminal f := C.skeleton.initial_edgeInv f
    have hterm : C.skeleton.terminal f⁻¹ = C.skeleton.initial f := C.skeleton.terminal_edgeInv f
    constructor
    · intro h'
      simpa [orientedEdgeIsBoundaryLayer, hinit, hterm, or_comm] using h'
    · intro h'
      simpa [orientedEdgeIsBoundaryLayer, hinit, hterm, or_comm] using h'

/-- A geometric edge is incident with the boundary of the planar map when one of its endpoints is
a boundary vertex. -/
def IsBoundaryLayerEdge (embedding : TwoManifoldEmbedding C 𝔼²) :
    GeometricEdge → Prop :=
  Quotient.lift
    (embedding.orientedEdgeIsBoundaryLayer)
    (embedding.orientedEdgeIsBoundaryLayer_eq_of_geometricEdgeSetoid)

/-- A geometric edge represented by `e` is incident with a boundary vertex exactly when one of the
endpoints of `e` is a boundary vertex. -/
-- Proof sketch: evaluate the quotient lift on the representative `e`.
@[simp] theorem isBoundaryLayerEdge_mk_iff
    (embedding : TwoManifoldEmbedding C 𝔼²) (e : C.skeleton.Edge) :
    embedding.IsBoundaryLayerEdge ⟦e⟧ ↔
      embedding.IsBoundaryVertex (C.skeleton.initial e) ∨
        embedding.IsBoundaryVertex (C.skeleton.terminal e) :=
  Iff.rfl

/- Definition 5-6-2 reuses the existing owner predicates `IsBoundaryVertex` and
`IsBoundaryRegion` for the vertex and region parts of the boundary layer; only the edge clause
requires the new owner `IsBoundaryLayerEdge` above. -/

end

end TwoManifoldEmbedding
end TwoComplex
