/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

open Set

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: planar realizations of maps in the Euclidean plane.

Layer triage:
- `source-facing`: the source treats a map as vertices, edges, and regions drawn in `𝔼²`, with
  closure and boundary operations on those planar pieces.
- `core/canonical`: `TwoComplex` is the project owner for the underlying oriented map,
  `TwoComplex.TwoManifoldEmbedding` is the owner for a realization of that map in a surface, and
  `OneComplex.GeometricEdge` / `TwoComplex.GeometricFace` are the canonical unoriented edge and
  region carriers.
- `bridge/view`: from a chosen planar embedding we recover the source-style vertex set, open
  edges, regions, support, and boundary as derived subsets of `𝔼²`.

Domain sampling:
1. `TwoComplex` from Definition `3-2-4` is the established owner abstraction for the map itself.
2. `TwoComplex.TwoManifoldEmbedding C 𝔼²` from Proposition `3-5-6` is the owner for a planar
   realization of that map.
3. `OneComplex.GeometricEdge` and `TwoComplex.GeometricFace` are the canonical unoriented cell
   carriers, so the source's plain "edges" and "regions" should be derived from them rather than
   rebuilt as a second root structure.
4. `closure`, `frontier`, and `sUnion` are the canonical topological owners for closed edge and
   face images, region boundaries, and finite unions of planar pieces.

Primitive vs. derived:
- primitive owner data: a `TwoComplex` and a chosen planar `TwoManifoldEmbedding`;
- derived API: source-style planar edges, regions, support, boundary, and the textbook planar-map
  axioms phrased as a property of that embedding.
-/

/- Definition 5-1-1: the chapter owner for the underlying oriented map is `TwoComplex`. -/
#check TwoComplex

/- A planar realization of that map is a `TwoManifoldEmbedding` into the Euclidean plane. -/
#check TwoComplex.TwoManifoldEmbedding

/- Existence of such a realization is the owner predicate `TwoComplex.EmbedsInPlane`. -/
#check TwoComplex.EmbedsInPlane

namespace Set

/-- A planar edge is a bounded subset of the Euclidean plane homeomorphic to the open unit
interval. -/
def IsPlanarEdge (e : Set 𝔼²) : Prop :=
  Bornology.IsBounded e ∧ Nonempty (Homeomorph (Set.Ioo (0 : ℝ) 1) e)

/-- A planar region is a bounded subset of the Euclidean plane homeomorphic to the open unit
disk. -/
def IsPlanarRegion (D : Set 𝔼²) : Prop :=
  Bornology.IsBounded D ∧ Nonempty (Homeomorph (Metric.ball (0 : 𝔼²) 1) D)

/-- Two vertices are endpoints of an edge when adjoining them to the edge gives its closure. -/
def HasEndpoints (e : Set 𝔼²) (a b : 𝔼²) : Prop :=
  closure e = e ∪ ({a, b} : Set 𝔼²)

end Set

namespace TwoComplex

/-- The unoriented geometric edge traversed by a total boundary arrow in the `1`-skeleton. -/
def boundaryArrowGeometricEdge {C : TwoComplex} (e : Quiver.Total C.skeleton) :
    OneComplex.GeometricEdge C.skeleton :=
  ⟦e.hom.1⟧

@[simp] theorem boundaryArrowGeometricEdge_reverse {C : TwoComplex}
    (e : Quiver.Total C.skeleton) :
    C.boundaryArrowGeometricEdge (Quiver.Total.reverse e) = C.boundaryArrowGeometricEdge e := by
  change (⟦e.hom.1⁻¹⟧ : OneComplex.GeometricEdge C.skeleton) = ⟦e.hom.1⟧
  exact Quot.sound (Or.inr rfl)

/-- The geometric edges occurring in the boundary cycle of an oriented face. -/
private def orientedBoundaryGeometricEdges (C : TwoComplex) (D : C.Face) :
    Set (OneComplex.GeometricEdge C.skeleton) :=
  { e | ∃ a ∈ (C.boundary D).1, C.boundaryArrowGeometricEdge a = e }

private theorem orientedBoundaryGeometricEdges_faceInv (C : TwoComplex) (D : C.Face) :
    C.orientedBoundaryGeometricEdges (C.faceInv D) = C.orientedBoundaryGeometricEdges D := by
  ext e
  constructor
  · rintro ⟨a, ha, hae⟩
    rw [C.boundary_faceInv D] at ha
    change a ∈ ((Quiver.Path.inverseCycle (C.boundary D)).1) at ha
    change a ∈ ((C.boundary D).1.reverse.map Quiver.Total.reverse) at ha
    rcases Cycle.mem_map.1 ha with ⟨b, hb, rfl⟩
    exact ⟨b, Cycle.mem_reverse_iff.1 hb, by simpa using hae⟩
  · rintro ⟨a, ha, hae⟩
    refine ⟨Quiver.Total.reverse a, ?_, by simpa using hae⟩
    rw [C.boundary_faceInv D]
    change Quiver.Total.reverse a ∈ ((C.boundary D).1.reverse.map Quiver.Total.reverse)
    exact Cycle.mem_map.2 ⟨a, Cycle.mem_reverse_iff.2 ha, rfl⟩

/-- The geometric edges occurring in the boundary cycle of a geometric face. -/
def boundaryGeometricEdges (C : TwoComplex) :
    GeometricFace C → Set (OneComplex.GeometricEdge C.skeleton) :=
  Quotient.lift (C.orientedBoundaryGeometricEdges) fun D E h ↦ by
    rcases h with rfl | h
    · rfl
    · simpa [h] using C.orientedBoundaryGeometricEdges_faceInv E

@[simp] theorem boundaryGeometricEdges_mk (C : TwoComplex) (D : C.Face) :
    C.boundaryGeometricEdges ⟦D⟧ = C.orientedBoundaryGeometricEdges D :=
  rfl

@[simp] theorem mem_boundaryGeometricEdges_mk_iff (C : TwoComplex) (D : C.Face)
    (e : OneComplex.GeometricEdge C.skeleton) :
    e ∈ C.boundaryGeometricEdges ⟦D⟧ ↔
      ∃ a ∈ (C.boundary D).1, C.boundaryArrowGeometricEdge a = e :=
  Iff.rfl

namespace TwoManifoldEmbedding

variable {C : TwoComplex}

/-- The set of vertices of a planar realization. -/
def vertexSet (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  Set.range embedding.vertexMap

/-- The closed image of an unoriented edge of the map. -/
def geometricEdgeSet
    (embedding : TwoManifoldEmbedding C 𝔼²) :
    OneComplex.GeometricEdge C.skeleton → Set 𝔼² :=
  Quotient.lift embedding.edgeSet fun e f h ↦ by
    rcases h with rfl | h
    · rfl
    · simpa [h] using embedding.edgeInv_set f

/-- The union of all closed edge-images of the planar realization. -/
def closedEdgeSupport (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  ⋃ e : OneComplex.GeometricEdge C.skeleton, embedding.geometricEdgeSet e

/-- The source-style edge corresponding to an unoriented edge is the closed edge-image with the
vertex set removed. -/
def edge
    (embedding : TwoManifoldEmbedding C 𝔼²)
    (e : OneComplex.GeometricEdge C.skeleton) : Set 𝔼² :=
  embedding.geometricEdgeSet e \ embedding.vertexSet

/-- The source-style region corresponding to a geometric face is the closed face-image with the
vertex set and all closed edge-images removed. -/
def region (embedding : TwoManifoldEmbedding C 𝔼²) (D : GeometricFace C) : Set 𝔼² :=
  embedding.geometricFaceSet D \ (embedding.vertexSet ∪ embedding.closedEdgeSupport)

/-- The underlying subset of the plane occupied by the planar realization. -/
def support (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  embedding.vertexSet ∪
    (⋃ e : OneComplex.GeometricEdge C.skeleton, embedding.edge e) ∪
      ⋃ D : GeometricFace C, embedding.region D

/-- The boundary of a planar realization is the frontier of its support. -/
def boundary (embedding : TwoManifoldEmbedding C 𝔼²) : Set 𝔼² :=
  frontier embedding.support

/-- The closed-edge support prescribed by the combinatorial boundary of an oriented face. -/
def faceBoundarySupport (embedding : TwoManifoldEmbedding C 𝔼²) (D : GeometricFace C) : Set 𝔼² :=
  sUnion (embedding.geometricEdgeSet '' C.boundaryGeometricEdges D)

@[simp] theorem geometricEdgeSet_mk (embedding : TwoManifoldEmbedding C 𝔼²) (e : C.skeleton.Edge) :
    embedding.geometricEdgeSet ⟦e⟧ = embedding.edgeSet e :=
  rfl

@[simp] theorem faceBoundarySupport_mk (embedding : TwoManifoldEmbedding C 𝔼²) (D : C.Face) :
    embedding.faceBoundarySupport ⟦D⟧ =
      sUnion (embedding.geometricEdgeSet '' C.orientedBoundaryGeometricEdges D) :=
  rfl

/-- Definition 5-1-1, expressed on the canonical owner: a planar realization of a `TwoComplex`
is a finite planar map when its source-style edges and regions satisfy the textbook interval,
disk, endpoint, disjointness, and boundary-incidence conditions. -/
class IsPlanarMap (embedding : TwoManifoldEmbedding C 𝔼²) : Prop where
  finite_vertex : Finite C.skeleton
  finite_edge : Finite (OneComplex.GeometricEdge C.skeleton)
  finite_face : Finite (GeometricFace C)
  edge_isPlanar (e : OneComplex.GeometricEdge C.skeleton) :
    (embedding.edge e).IsPlanarEdge
  region_isPlanar (D : GeometricFace C) :
    (embedding.region D).IsPlanarRegion
  region_closure (D : GeometricFace C) :
    closure (embedding.region D) = embedding.geometricFaceSet D
  edge_closedEdge (e : OneComplex.GeometricEdge C.skeleton) :
    closure (embedding.edge e) = embedding.geometricEdgeSet e
  edge_hasEndpoints (e : C.skeleton.Edge) :
    (embedding.edge ⟦e⟧).HasEndpoints
      (embedding.vertexMap (C.skeleton.initial e))
      (embedding.vertexMap (C.skeleton.terminal e))
  edge_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (OneComplex.GeometricEdge C.skeleton))
      embedding.edge
  region_pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (GeometricFace C))
      embedding.region
  edge_region_disjoint (e : OneComplex.GeometricEdge C.skeleton) (D : GeometricFace C) :
    Disjoint (embedding.edge e) (embedding.region D)
  region_boundary_connected (D : GeometricFace C) :
    IsConnected (frontier (embedding.region D))
  region_boundary_eq_faceBoundarySupport (D : GeometricFace C) :
    frontier (embedding.region D) = embedding.faceBoundarySupport D

/-- A face-boundary incidence in a carried subcomplex is also a face-boundary incidence for the
corresponding ambient face. -/
private theorem vertexOnFace_of_subcomplex
    {S : Subcomplex C} {v : S.complex.skeleton} {D : S.complex.Face} :
    S.complex.VertexOnFace v D → C.VertexOnFace v.1 D.1 := by
  sorry

/-- Restricting a surface embedding to a carried subcomplex keeps the same geometric images of
the surviving vertices, edges, and faces. -/
def restrictToSubcomplex (embedding : TwoManifoldEmbedding C 𝔼²) (S : Subcomplex C) :
    TwoManifoldEmbedding S.complex 𝔼² where
  vertexMap v := embedding.vertexMap v.1
  edgeMap e := embedding.edgeMap e.1
  faceMap D := embedding.faceMap D.1
  vertex_injective := fun _ _ h ↦ Subtype.ext (embedding.vertex_injective h)
  edge_isClosedEmbedding := fun e ↦ embedding.edge_isClosedEmbedding e.1
  face_isClosedEmbedding := fun D ↦ embedding.face_isClosedEmbedding D.1
  source_eq_edgeMap_zero := fun e ↦ embedding.source_eq_edgeMap_zero e.1
  target_eq_edgeMap_one := fun e ↦ embedding.target_eq_edgeMap_one e.1
  edgeInv_range := fun e ↦ embedding.edgeInv_range e.1
  faceInv_range := fun D ↦ embedding.faceInv_range D.1
  boundary_edge_subset_face := by
    sorry
  boundary_vertex_mem_face := fun hv ↦
    embedding.boundary_vertex_mem_face (vertexOnFace_of_subcomplex hv)

/-- Restricting a planar map to a carried subcomplex again yields a planar map. -/
instance isPlanarMap_restrictToSubcomplex
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] (S : Subcomplex C) :
    (embedding.restrictToSubcomplex S).IsPlanarMap := by
  sorry

/-- Restricting a planar map to a nested subcomplex again yields a planar map. -/
instance isPlanarMap_restrict {C : TwoComplex} {S T : TwoComplex.Subcomplex C}
    (embedding : TwoManifoldEmbedding S.complex 𝔼²) [embedding.IsPlanarMap]
    (hvertex : T.skeleton.vertexSet ⊆ S.skeleton.vertexSet)
    (hedge : T.skeleton.edgeSet ⊆ S.skeleton.edgeSet)
    (hface : T.faceSet ⊆ S.faceSet) :
    (embedding.restrict hvertex hedge hface).IsPlanarMap := by
  sorry

/-- A finite planar map has only finitely many oriented edges, since each geometric edge has the
two possible orientations. -/
theorem finite_orientedEdge {C : TwoComplex} (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] :
    Finite C.skeleton.Edge := by
  classical
  let hplanar : embedding.IsPlanarMap := inferInstance
  let _ : Finite (OneComplex.GeometricEdge C.skeleton) := hplanar.finite_edge
  let f : OneComplex.GeometricEdge C.skeleton × Bool → C.skeleton.Edge := fun x ↦
    if x.2 then (Quotient.out x.1)⁻¹ else Quotient.out x.1
  have hf : Function.Surjective f := by
    intro e
    let q : OneComplex.GeometricEdge C.skeleton := ⟦e⟧
    rcases Quotient.eq.mp (Quotient.out_eq q) with h | h
    · refine ⟨(q, false), ?_⟩
      simp [f, q, h]
    · refine ⟨(q, true), ?_⟩
      have h' : q.out⁻¹ = e := by
        exact (congrArg C.skeleton.edgeInv h).trans (C.skeleton.edgeInv_involutive e)
      simp [f, q, h']
  exact Finite.of_surjective f hf

end TwoManifoldEmbedding
end TwoComplex
