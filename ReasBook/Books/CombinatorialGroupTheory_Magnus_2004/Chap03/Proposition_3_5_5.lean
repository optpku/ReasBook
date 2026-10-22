/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝔻²" => Metric.closedBall (0 : 𝔼²) 1

/-!
Primary domain: planar Cayley complexes, topological surfaces, and free products of cyclic groups.

Layer triage:
- `source-facing`: a concrete Cayley-complex realization of a presentation of `G` whose Cayley
  complex embeds in a `2`-manifold.
- `core/canonical`: `CayleyComplex.Coordinates` is the owner for a Cayley-complex realization,
  `ChartedSpace 𝔼² S` is the standard local-Euclidean owner for a
  topological `2`-manifold model, and `Monoid.CoprodI` is mathlib's owner for indexed free
  products.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding` is the cellwise topological-realization owner
  for a `2`-complex in a surface, and `TwoComplex.EmbedsInTwoManifold` /
  `IsFreeProductOfCyclicGroups` expose the source-facing existence hypotheses and conclusions
  directly.

Domain sampling:
1. `CayleyComplex.Coordinates` is the canonical chapter owner for the actual Cayley complex
   attached to a presentation.
2. `ChartedSpace 𝔼² S` is mathlib's standard local-Euclidean owner for a topological
   `2`-manifold model.
3. `Monoid.CoprodI A` is mathlib's owner for free products indexed by a family of groups, while
   `IsCyclic (A i)` is the owner predicate for cyclic factors.

Primitive vs. derived:
- primitive data: the actual vertex placement together with closed-interval edge maps and
  closed-disk face maps that are topological embeddings into the ambient surface;
- derived API: the closed edge-images and face-images, their opposite-orientation invariance, and
  the source-style manifold-embeddability predicate.
-/

namespace TwoComplex

/-- A `2`-complex embedding into a topological surface consists of an injective placement of
vertices together with compatible closed-interval edge maps and closed-disk face maps. -/
structure TwoManifoldEmbedding (C : TwoComplex) (S : Type v) [TopologicalSpace S] where
  /-- The placement of vertices in the ambient surface. -/
  vertexMap : C.skeleton → S
  /-- A cellwise realization of each oriented edge by a closed interval. -/
  edgeMap : C.skeleton.Edge → Set.Icc (0 : ℝ) 1 → S
  /-- A cellwise realization of each oriented face by a closed disk. -/
  faceMap : C.Face → 𝔻² → S
  /-- Distinct vertices have distinct images. -/
  vertex_injective : Function.Injective vertexMap
  /-- Each oriented edge is realized by a closed topological embedding of the closed interval. -/
  edge_isClosedEmbedding (e : C.skeleton.Edge) : Topology.IsClosedEmbedding (edgeMap e)
  /-- Each oriented face is realized by a closed topological embedding of the closed disk. -/
  face_isClosedEmbedding (D : C.Face) : Topology.IsClosedEmbedding (faceMap D)
  /-- The initial vertex of an oriented edge is the left endpoint of its realized interval. -/
  source_eq_edgeMap_zero (e : C.skeleton.Edge) :
    edgeMap e ⟨0, by norm_num, by norm_num⟩ = vertexMap (C.skeleton.initial e)
  /-- The terminal vertex of an oriented edge is the right endpoint of its realized interval. -/
  target_eq_edgeMap_one (e : C.skeleton.Edge) :
    edgeMap e ⟨1, by norm_num, by norm_num⟩ = vertexMap (C.skeleton.terminal e)
  /-- Opposite orientations of an edge have the same closed image. -/
  edgeInv_range (e : C.skeleton.Edge) :
    Set.range (edgeMap (C.skeleton.edgeInv e)) = Set.range (edgeMap e)
  /-- Opposite orientations of a face have the same closed image. -/
  faceInv_range (D : C.Face) :
    Set.range (faceMap (C.faceInv D)) = Set.range (faceMap D)
  /-- Every boundary edge of a face is contained in the realized image of that face. -/
  boundary_edge_subset_face {D : C.Face} {a : Quiver.Total C.skeleton} (ha : a ∈ (C.boundary D).1) :
    Set.range (edgeMap a.hom.1) ⊆ Set.range (faceMap D)
  /-- Every vertex on the boundary of a face lies in the realized image of that face. -/
  boundary_vertex_mem_face {D : C.Face} {x : C.skeleton} :
    C.VertexOnFace x D → vertexMap x ∈ Set.range (faceMap D)

namespace TwoManifoldEmbedding

variable {C : TwoComplex} {S : Type v} [TopologicalSpace S]

/-- The closed image of an oriented edge in a surface embedding. -/
def edgeSet (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) : Set S :=
  Set.range (embedding.edgeMap e)

/-- The closed image of an oriented face in a surface embedding. -/
def faceSet (embedding : TwoManifoldEmbedding C S) (D : C.Face) : Set S :=
  Set.range (embedding.faceMap D)

/-- The initial vertex of an oriented edge lies in its closed image. -/
theorem source_mem_edge (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    embedding.vertexMap (C.skeleton.initial e) ∈ embedding.edgeSet e := by
  exact ⟨⟨0, by norm_num, by norm_num⟩, embedding.source_eq_edgeMap_zero e⟩

/-- The terminal vertex of an oriented edge lies in its closed image. -/
theorem target_mem_edge (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    embedding.vertexMap (C.skeleton.terminal e) ∈ embedding.edgeSet e := by
  exact ⟨⟨1, by norm_num, by norm_num⟩, embedding.target_eq_edgeMap_one e⟩

/-- Each oriented edge has a closed geometric image. -/
theorem edge_isClosed (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    IsClosed (embedding.edgeSet e) :=
  (embedding.edge_isClosedEmbedding e).isClosed_range

/-- Each oriented face has a closed geometric image. -/
theorem face_isClosed (embedding : TwoManifoldEmbedding C S) (D : C.Face) :
    IsClosed (embedding.faceSet D) :=
  (embedding.face_isClosedEmbedding D).isClosed_range

/-- Opposite orientations of an edge have the same geometric image. -/
theorem edgeInv_set (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    embedding.edgeSet (C.skeleton.edgeInv e) = embedding.edgeSet e :=
  embedding.edgeInv_range e

/-- Opposite orientations of a face have the same geometric image. -/
theorem faceInv_set (embedding : TwoManifoldEmbedding C S) (D : C.Face) :
    embedding.faceSet (C.faceInv D) = embedding.faceSet D :=
  embedding.faceInv_range D

/-- The geometric image of an unoriented face, obtained by quotienting the oriented-face image
along reversal. -/
def geometricFaceSet (embedding : TwoManifoldEmbedding C S) :
    TwoComplex.GeometricFace C → Set S :=
  Quotient.lift embedding.faceSet fun D E h ↦ by
    rcases h with rfl | h
    · rfl
    · simpa [h] using embedding.faceInv_set E

@[simp] theorem geometricFaceSet_mk
    (embedding : TwoManifoldEmbedding C S) (D : C.Face) :
    embedding.geometricFaceSet ⟦D⟧ = embedding.faceSet D :=
  rfl

/-- The union of the geometric images of a family of unoriented faces. -/
def geometricFaceUnion (embedding : TwoManifoldEmbedding C S)
    (faces : Set (TwoComplex.GeometricFace C)) : Set S :=
  ⋃ D ∈ faces, embedding.geometricFaceSet D

/-- An ambient homeomorphism realizes a `2`-complex automorphism when it carries each geometric
face image to the image of its image face. -/
def RealizesAutomorphism
    (embedding : TwoManifoldEmbedding C S)
    (α : TwoComplex.Aut C) (φ : Homeomorph S S) : Prop :=
  ∀ D : TwoComplex.GeometricFace C,
    φ '' embedding.geometricFaceSet D = embedding.geometricFaceSet (α.geometricFacePerm D)

end TwoManifoldEmbedding

/-- A `2`-complex embeds in a `2`-manifold when it admits a geometric embedding into a Hausdorff
charted space locally modelled on `ℝ²`. -/
def EmbedsInTwoManifold (C : TwoComplex) : Prop :=
  ∃ (S : Type z) (_ : TopologicalSpace S) (_ : T2Space S) (_ : ChartedSpace 𝔼² S),
      Nonempty (TwoManifoldEmbedding C S)

end TwoComplex

/-- A group is a free product of cyclic groups when it is isomorphic to an indexed free product
`Monoid.CoprodI A` with cyclic factor groups. -/
def IsFreeProductOfCyclicGroups (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type v) (A : ι → Type w) (_ : ∀ i, Group (A i)) (_ : ∀ i, IsCyclic (A i)),
    Nonempty (Monoid.CoprodI A ≃* G)

section Proposition355

variable {G : Type u} [Group G]
variable {X : Type v} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Proposition 3-5-5: every group admitting a presentation whose Cayley complex embeds in a
`2`-manifold is either an `F`-group or a free product of cyclic groups. -/
-- Proof sketch: analyze the relator-root system of the given planar Cayley presentation as in the
-- text. A finite strictly quadratic connected component gives an `F`-group by Proposition
-- `3-5-4`; otherwise each component normalizes to cyclic relators, and the presentation splits as
-- a free product of cyclic groups.
theorem isFGroup_or_isFreeProductOfCyclicGroups_of_cayleyComplex_embedsInTwoManifold
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (e : PresentedGroup R ≃* G) (hC : C.EmbedsInTwoManifold) :
    IsFGroup G ∨ IsFreeProductOfCyclicGroups G := sorry

end Proposition355
