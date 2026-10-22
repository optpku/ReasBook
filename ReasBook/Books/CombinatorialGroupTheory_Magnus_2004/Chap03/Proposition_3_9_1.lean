/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_5

-- Declarations for this item will be appended below by the statement pipeline.

universe w

set_option autoImplicit false

noncomputable section

open Quiver.Path

/-
Primary domain: finite singular subcomplex decompositions inside an ambient `TwoComplex`.

Layer triage:
- `source-facing`: a finite singular subcomplex with no loose `1`-skeleton data, together with
  the conclusion that its connected components are singular discs equipped with explicit reduced
  boundary cycles or singular spheres whose edges are all closed up by carried faces.
- `core/canonical`: `OneComplex.GeometricEdge`,
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`,
  `TwoComplex.IsSimplyConnected`, `TwoComplex.EmbedsInPlane`, `TwoComplex.EmbedsInSphere`, and
  `TwoComplex.GeometricFace` are the owner predicates and carriers for the geometric ingredients.
- `bridge/view`: `Quiver.Path.CyclicPath`, `IsSimpleCycle`, and
  `IsCyclicallyReducedCycle` are the owner API for the chosen boundary cycle carried by a
  singular disc, while oriented-edge representatives of a geometric edge remain only a companion
  view for boundary traversal.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner abstraction for carried
   subcomplexes and their induced `2`-complexes.
2. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for simple
   connectedness of the carried `2`-complex.
3. `TwoComplex.EmbedsInPlane` and `TwoComplex.EmbedsInSphere` from Proposition `3-5-6` are the
   owner predicates for planar and spherical embeddability.
4. `OneComplex.GeometricEdge` from Definition `3-2-1` is the owner carrier for carried edges, so
   boundary-vs-interior edge data should be phrased on geometric edges rather than on oriented
   representatives.
5. `TwoComplex.GeometricFace` from Definition `3-2-4` is the owner carrier for orientation-free
   face incidence, so the incident-face API should pair naturally with geometric edges.
6. `Quiver.Path.CyclicPath`, `IsSimpleCycle`, and `IsCyclicallyReducedCycle` are the owner API
   for the explicit disc boundary cycle.

Primitive vs. derived:
- primitive data: the ambient subcomplex `S` with finite carried vertices, geometric edges, and
  faces, no loose carried vertices or edges, and for a disc component its chosen boundary cycle;
- derived API: connected-component decompositions of `S`, connectedness, simple connectedness,
  simplicity and cyclic reduction of the chosen boundary cycle, and the geometric-face incidence
  conditions distinguishing disc boundary geometric edges from interior or spherical ones.
-/

namespace Quiver.Path

private def CyclicPath.SupportsEdge {K : OneComplex} (c : CyclicPath K) (e : K.Edge) : Prop :=
  ∃ t ∈ c.1, t.hom.1 = e ∨ t.hom.1 = e⁻¹

private theorem CyclicPath.supportsEdge_inv_iff {K : OneComplex} (c : CyclicPath K) (e : K.Edge) :
    c.SupportsEdge e⁻¹ ↔ c.SupportsEdge e := by
  constructor
  · rintro ⟨t, ht, hte | hte⟩
    · exact ⟨t, ht, Or.inr hte⟩
    · exact ⟨t, ht, Or.inl (hte.trans (K.edgeInv_involutive e))⟩
  · rintro ⟨t, ht, hte | hte⟩
    · exact ⟨t, ht, Or.inr (hte.trans (K.edgeInv_involutive e).symm)⟩
    · exact ⟨t, ht, Or.inl hte⟩

/-- A geometric edge lies on a cyclic path when some, equivalently every, oriented representative
of that geometric edge is traversed by the path. -/
def CyclicPath.SupportsGeometricEdge {K : OneComplex} (c : CyclicPath K)
    (e : OneComplex.GeometricEdge K) : Prop :=
  Quotient.liftOn e (fun f ↦ c.SupportsEdge f) fun e f h ↦
    propext <| by
      rcases h with rfl | h
      · rfl
      · simpa [h] using c.supportsEdge_inv_iff f

/-- The owner-level geometric-edge condition is equivalent to traversing any chosen oriented
representative or its reverse. -/
theorem supportsGeometricEdge_iff {K : OneComplex} (c : CyclicPath K) (e : K.Edge) :
    c.SupportsGeometricEdge ⟦e⟧ ↔ ∃ t ∈ c.1, t.hom.1 = e ∨ t.hom.1 = e⁻¹ := by
  rfl

end Quiver.Path

namespace TwoComplex.Subcomplex

variable {C : TwoComplex.{w}}

/-- A family of subcomplexes is a connected-component decomposition of `S` when it partitions the
carried vertices, edges, and faces of `S`, and each piece is connected. -/
structure IsComponentDecomposition (S : Subcomplex C) {ι : Type*}
    (components : ι → Subcomplex C) : Prop where
  /-- A carried vertex of `S` lies in exactly one listed component. -/
  vertex_mem_iff (v : C.skeleton) :
    v ∈ S.skeleton.vertexSet ↔ ∃ i, v ∈ (components i).skeleton.vertexSet
  /-- A carried edge of `S` lies in exactly one listed component. -/
  edge_mem_iff (e : C.skeleton.Edge) :
    e ∈ S.skeleton.edgeSet ↔ ∃ i, e ∈ (components i).skeleton.edgeSet
  /-- A carried face of `S` lies in exactly one listed component. -/
  face_mem_iff (D : C.Face) :
    D ∈ S.faceSet ↔ ∃ i, D ∈ (components i).faceSet
  /-- Distinct listed components have disjoint vertex carriers, so they are genuinely different
  connected components of the carried `1`-skeleton. -/
  vertex_pairwiseDisjoint :
    Pairwise
      (fun i j ↦
        Disjoint (components i).skeleton.vertexSet (components j).skeleton.vertexSet)
  /-- Each listed piece is connected in its own carried `1`-skeleton. -/
  connected (i : ι) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify (components i).skeleton.toOneComplex)

namespace IsComponentDecomposition

section

variable {S : Subcomplex C} {ι : Type*} {components : ι → Subcomplex C}

/-- Each listed component of a component decomposition is carried by the parent subcomplex at the
vertex level. -/
theorem vertexSet_subset (hcomponents : IsComponentDecomposition S components) (i : ι) :
    (components i).skeleton.vertexSet ⊆ S.skeleton.vertexSet := fun _ hv ↦
  (hcomponents.vertex_mem_iff _).2 ⟨i, hv⟩

/-- Each listed component of a component decomposition is carried by the parent subcomplex at the
edge level. -/
theorem edgeSet_subset (hcomponents : IsComponentDecomposition S components) (i : ι) :
    (components i).skeleton.edgeSet ⊆ S.skeleton.edgeSet := fun _ he ↦
  (hcomponents.edge_mem_iff _).2 ⟨i, he⟩

/-- Each listed component of a component decomposition is carried by the parent subcomplex at the
face level. -/
theorem faceSet_subset (hcomponents : IsComponentDecomposition S components) (i : ι) :
    (components i).faceSet ⊆ S.faceSet := fun _ hD ↦
  (hcomponents.face_mem_iff _).2 ⟨i, hD⟩

end

end IsComponentDecomposition

section SingularSurfacePieces

variable (S : Subcomplex C)

local notation "K1" => S.skeleton.toOneComplex
local notation "GeometricEdge" => OneComplex.GeometricEdge K1
local notation "verts" => S.skeleton.vertexSet
local notation "edges" => S.skeleton.edgeSet

/-- The geometric faces of `S.complex` incident to a geometric edge of the carried
`1`-skeleton. -/
def incidentGeometricFaces (e : GeometricEdge) : Set (TwoComplex.GeometricFace S.complex) :=
  { F | ∃ D : S.complex.Face,
      (⟦D⟧ : TwoComplex.GeometricFace S.complex) = F ∧
        (S.complex.boundary D).SupportsGeometricEdge e }

/-- A carried geometric edge is on the outer boundary exactly when it is incident to a unique
carried geometric face. -/
def EdgeHasUniqueIncidentGeometricFace (e : GeometricEdge) : Prop :=
  ∃ F : TwoComplex.GeometricFace S.complex,
    F ∈ S.incidentGeometricFaces e ∧
      ∀ F' : TwoComplex.GeometricFace S.complex,
        F' ∈ S.incidentGeometricFaces e → F' = F

/-- A carried geometric edge is an interior surface edge exactly when it is incident to two
distinct carried geometric faces and to no others. -/
def EdgeHasExactlyTwoIncidentGeometricFaces (e : GeometricEdge) : Prop :=
  ∃ F₁ F₂ : TwoComplex.GeometricFace S.complex,
    F₁ ≠ F₂ ∧
      F₁ ∈ S.incidentGeometricFaces e ∧
      F₂ ∈ S.incidentGeometricFaces e ∧
      ∀ F : TwoComplex.GeometricFace S.complex,
        F ∈ S.incidentGeometricFaces e → F = F₁ ∨ F = F₂

/-- A singular subcomplex is finite and has no loose carried `1`-skeleton data: every carried
vertex lies on a carried oriented edge, and every carried geometric edge occurs on the boundary of
some carried geometric face. -/
structure IsSingularSubcomplex : Prop where
  finite_vertexSet : Set.Finite verts
  finite_edgeSet : Set.Finite edges
  finite_faceSet : Set.Finite S.faceSet
  edge_exists_at_vertex (v : K1) :
    ∃ e : (K1).Edge, (K1).initial e = v ∨ (K1).terminal e = v
  incidentGeometricFace_nonempty (e : GeometricEdge) :
    ∃ F : TwoComplex.GeometricFace S.complex, F ∈ S.incidentGeometricFaces e

/-- A singular disc is a finite connected simply connected planar subcomplex whose chosen cyclic
boundary is simple, cyclically reduced, and carries exactly the geometric edges incident to one
carried geometric face; the remaining carried geometric edges are interior and incident to exactly
two carried geometric faces. -/
structure IsSingularDisc (boundary : CyclicPath K1) : Prop extends IsSingularSubcomplex S where
  faceSet_nonempty : S.faceSet.Nonempty
  connected : Quiver.IsStronglyConnected (Quiver.Symmetrify K1)
  simplyConnected : S.complex.IsSimplyConnected
  embedsInPlane : S.complex.EmbedsInPlane
  simpleCycle : IsSimpleCycle boundary
  cyclicallyReducedCycle : IsCyclicallyReducedCycle boundary
  boundary_geometricEdge_iff (e : GeometricEdge) :
    boundary.SupportsGeometricEdge e ↔ S.EdgeHasUniqueIncidentGeometricFace e
  interior_geometricEdge (e : GeometricEdge) :
    ¬ boundary.SupportsGeometricEdge e → S.EdgeHasExactlyTwoIncidentGeometricFaces e

/-- A singular disc in particular carries a simple cyclic boundary witness. -/
theorem IsSingularDisc.hasSimpleBoundary {S : Subcomplex C}
    {boundary : CyclicPath S.skeleton.toOneComplex} (hS : IsSingularDisc S boundary) :
    S.HasSimpleBoundary := by
  exact ⟨boundary, hS.simpleCycle⟩

/-- A singular sphere is a finite connected simply connected spherical subcomplex all of whose
carried geometric edges are interior edges incident to exactly two carried geometric faces. -/
structure IsSingularSphere : Prop extends IsSingularSubcomplex S where
  faceSet_nonempty : S.faceSet.Nonempty
  connected : Quiver.IsStronglyConnected (Quiver.Symmetrify K1)
  simplyConnected : S.complex.IsSimplyConnected
  embedsInSphere : S.complex.EmbedsInSphere
  interior_geometricEdge (e : GeometricEdge) :
    S.EdgeHasExactlyTwoIncidentGeometricFaces e

end SingularSurfacePieces

/-- Proposition 3-9-1: every singular subcomplex admits a finite component normal form in which
each component is either a singular disc with an explicit reduced boundary cycle or a singular
sphere. -/
-- Proof sketch: argue by induction on the total boundary length of the singular subcomplex.
-- Detachment decreases this complexity by splitting off repeated boundary segments, while sewing
-- up removes immediately cancellable boundary pairs. Repeating these moves until no further
-- reduction is possible yields components that are exactly reduced singular discs or singular
-- spheres.
theorem exists_disc_or_sphere_component_normalForm_of_singularSubcomplex
    (S : Subcomplex C) (hS : IsSingularSubcomplex S) :
    ∃ (ι : Type*) (_ : Fintype ι) (components : ι → Subcomplex C),
      IsComponentDecomposition S components ∧
        ∀ i : ι,
          (∃ boundary : CyclicPath (components i).skeleton.toOneComplex,
            IsSingularDisc (components i) boundary) ∨
            IsSingularSphere (components i) := sorry

end TwoComplex.Subcomplex
