/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊²" =>
  { x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 }

/-!
Primary domain: Cayley complexes, planar/spherical embeddings, and free products of cyclic groups.

Layer triage:
- `source-facing`: groups `G` that are either `F`-groups or free products of at most countably
  many cyclic groups, together with presentations whose Cayley complexes admit embeddings in the
  sphere or in the plane.
- `core/canonical`: `PresentedGroup R` is the owner for the presented group,
  `CayleyComplex.Coordinates.PresentationCoordinates C R` is the chapter owner for an actual
  Cayley complex with its standard coordinates, `TwoComplex.EmbedsInTwoManifold` from Proposition
  `3-5-5` is the intrinsic owner for embeddability in a `2`-manifold, and
  `IsFreeProductOfCyclicGroups` from Proposition `3-5-5` is the chapter owner for cyclic free
  products.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding` from Proposition `3-5-5` is the cellwise
  topological witness layer, the planar and spherical notions in this file are source-facing
  specializations to `ℝ²` and `𝕊²` that bridge back to `EmbedsInTwoManifold`, and
  `IsCountableFreeProductOfCyclicGroups` below is the source-facing countable refinement of the
  owner predicate `IsFreeProductOfCyclicGroups`, built from mathlib's indexed free-product owner
  `Monoid.CoprodI A`, the canonical cyclicity predicate `IsCyclic (A i)`, and a `Countable`
  indexing type.

Domain sampling:
1. `CayleyComplex.Coordinates.PresentationCoordinates C R` from Proposition `3-4-1` is the owner
   for an actual Cayley complex `C(X; R)` with coordinates over `PresentedGroup R`.
2. `TwoComplex.EmbedsInTwoManifold` from Proposition `3-5-5` is the intrinsic owner for the
   embeddability conclusion used across the chapter.
3. `TwoComplex.TwoManifoldEmbedding` from Proposition `3-5-5` is the chapter owner for the
   primitive geometric embedding data behind that intrinsic owner.
4. `IsFreeProductOfCyclicGroups` from Proposition `3-5-5` is the owner predicate for cyclic
   free-product decompositions, and the countable variant in this file should refine that owner
   instead of inlining a fresh existential package in each theorem statement.
-/

namespace TwoComplex

/-- A `2`-complex embeds in the plane when it admits a surface embedding into `ℝ²`. -/
def EmbedsInPlane (C : TwoComplex) : Prop :=
  Nonempty (TwoManifoldEmbedding C 𝔼²)

/-- A `2`-complex embeds in the `2`-sphere when it admits a surface embedding into `𝕊²`. -/
def EmbedsInSphere (C : TwoComplex) : Prop :=
  Nonempty (TwoManifoldEmbedding C 𝕊²)

/-- A planar embedding is, in particular, an embedding into a `2`-manifold. -/
-- Proof sketch: `ℝ²` is itself a Hausdorff charted `2`-manifold, so the planar witness is a
-- special case of the owner predicate `EmbedsInTwoManifold`.
theorem embedsInTwoManifold_of_embedsInPlane {C : TwoComplex} (hC : C.EmbedsInPlane) :
    TwoComplex.EmbedsInTwoManifold.{0} C := by
  exact ⟨𝔼², inferInstance, inferInstance, inferInstance, hC⟩

/-- A spherical embedding is, in particular, an embedding into a `2`-manifold. -/
-- Proof sketch: the standard unit sphere `𝕊²` carries its canonical Hausdorff charted
-- `2`-manifold structure, so a spherical embedding is a specialization of
-- `EmbedsInTwoManifold`.
theorem embedsInTwoManifold_of_embedsInSphere {C : TwoComplex} (hC : C.EmbedsInSphere) :
    TwoComplex.EmbedsInTwoManifold.{0} C := by
  exact ⟨𝕊², inferInstance, inferInstance, inferInstance, hC⟩

namespace TwoManifoldEmbedding

/-- Restricting a surface embedding along a nested subcomplex keeps the same geometric cell images
on the smaller carried complex. -/
def restrict {C : TwoComplex} {X : Type v} [TopologicalSpace X] {S T : Subcomplex C}
    (embedding : TwoComplex.TwoManifoldEmbedding S.complex X)
    (hvertex : T.skeleton.vertexSet ⊆ S.skeleton.vertexSet)
    (hedge : T.skeleton.edgeSet ⊆ S.skeleton.edgeSet)
    (hface : T.faceSet ⊆ S.faceSet) :
    TwoComplex.TwoManifoldEmbedding T.complex X := by
  refine
    { vertexMap := fun v ↦ embedding.vertexMap ⟨v.1, hvertex v.2⟩
      edgeMap := fun e ↦ embedding.edgeMap ⟨e.1, hedge e.2⟩
      faceMap := fun D ↦ embedding.faceMap ⟨D.1, hface D.2⟩
      vertex_injective := ?_
      edge_isClosedEmbedding := ?_
      face_isClosedEmbedding := ?_
      source_eq_edgeMap_zero := ?_
      target_eq_edgeMap_one := ?_
      edgeInv_range := ?_
      faceInv_range := ?_
      boundary_edge_subset_face := ?_
      boundary_vertex_mem_face := ?_ }
  · intro v w h
    apply Subtype.ext
    exact congrArg (fun x : S.skeleton.vertexSet ↦ x.1) (embedding.vertex_injective h)
  · intro e
    simpa using embedding.edge_isClosedEmbedding ⟨e.1, hedge e.2⟩
  · intro D
    simpa using embedding.face_isClosedEmbedding ⟨D.1, hface D.2⟩
  · intro e
    simpa using embedding.source_eq_edgeMap_zero ⟨e.1, hedge e.2⟩
  · intro e
    simpa using embedding.target_eq_edgeMap_one ⟨e.1, hedge e.2⟩
  · intro e
    simpa using embedding.edgeInv_range ⟨e.1, hedge e.2⟩
  · intro D
    simpa using embedding.faceInv_range ⟨D.1, hface D.2⟩
  · sorry
  · intro D v hv
    exact embedding.boundary_vertex_mem_face
      (Subcomplex.vertexOnFace_of_subset S T hvertex hedge hface hv)

/-- A planar surface embedding fills the plane when the union of all oriented face images is all
of `ℝ²`. -/
def FillsPlane
    {C : TwoComplex}
    (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  (⋃ D : C.Face, embedding.faceSet D) = Set.univ

/-- Filling the plane means exactly that every point of `ℝ²` lies in the image of some oriented
face. -/
-- Proof sketch: unfold `FillsPlane` and rewrite membership in the union of the face images.
theorem fillsPlane_iff
    {C : TwoComplex}
    (embedding : TwoManifoldEmbedding C 𝔼²) :
    embedding.FillsPlane ↔
      ∀ x : 𝔼², ∃ D : C.Face, x ∈ embedding.faceSet D := by
  constructor
  · intro h x
    have hx : x ∈ ⋃ D : C.Face, embedding.faceSet D := by
      rw [h]
      simp
    simpa [Set.mem_iUnion] using hx
  · intro h
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases h x with ⟨D, hD⟩
      simpa [Set.mem_iUnion] using Exists.intro D hD

end TwoManifoldEmbedding

end TwoComplex

/-- A group is a countable free product of cyclic groups when it is isomorphic to an indexed free
product `Monoid.CoprodI A` of cyclic groups over a countable index type. -/
def IsCountableFreeProductOfCyclicGroups (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type v) (_ : Countable ι) (A : ι → Type w) (_ : ∀ i, Group (A i))
    (_ : ∀ i, IsCyclic (A i)), Nonempty (Monoid.CoprodI A ≃* G)

/-- A countable free product of cyclic groups is, in particular, a free product of cyclic
groups. -/
theorem IsCountableFreeProductOfCyclicGroups.isFreeProductOfCyclicGroups
    {G : Type u} [Group G] (hG : IsCountableFreeProductOfCyclicGroups G) :
    IsFreeProductOfCyclicGroups G := sorry

section Proposition356

variable {G : Type u} [Group G]

/-- Proposition 3-5-6 (1): if `G` is either an `F`-group or a free product of at most countably
many cyclic groups, and `G` is finite, then `G` has a presentation whose Cayley complex embeds in
the `2`-sphere. -/
-- Proof sketch: choose the Section `5` presentation of `G` with strictly quadratic root system
-- and cyclic star graph. The local cyclicity makes the Cayley complex into a connected
-- simply-connected `2`-manifold without boundary. Finite `G` gives finitely many face orbits, so
-- the resulting surface is compact; classification of simply-connected surfaces then identifies it
-- with the sphere.
theorem exists_spherical_cayley_presentation
    (hG : IsFGroup G ∨ IsCountableFreeProductOfCyclicGroups G)
    (hfin : Finite G) :
    ∃ (X : Type v) (R : Set (FreeGroup X)) (C : TwoComplex)
      (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
      (e : PresentedGroup R ≃* G), C.EmbedsInSphere := sorry

/-- Proposition 3-5-6 (2): if `G` is either an `F`-group or a free product of at most countably
many cyclic groups, and `G` is infinite, then `G` has a presentation whose Cayley complex embeds
in the plane. -/
-- Proof sketch: use the same Section `5` presentation to obtain a connected simply-connected
-- surface without boundary. Infinite `G` forces the Cayley complex to be noncompact, and the
-- increasing-disc exhaustion from the textbook rules out the sphere. The remaining simply
-- connected surface is the plane.
theorem exists_planar_cayley_presentation
    (hG : IsFGroup G ∨ IsCountableFreeProductOfCyclicGroups G)
    (hinf : Infinite G) :
    ∃ (X : Type v) (R : Set (FreeGroup X)) (C : TwoComplex)
      (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
      (e : PresentedGroup R ≃* G), C.EmbedsInPlane := sorry

end Proposition356
