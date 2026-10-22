/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_2

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Primary domain: coverings, automorphisms, and quotient maps of `1`- and `2`-complexes.

Layer triage:
- `source-facing`: an actual Cayley complex `C(X; R)` realized by
  `PresentationCoordinates C R`,
  an actual presentation complex `K(X; R)` realized by `PresentationComplex.Coordinates K X R`,
  and the canonical map `C(X; R) → K(X; R)`.
- `core/canonical`: `CayleyComplex.Coordinates` is the owner for the Cayley-complex realization
  data, `PresentationComplex.Coordinates` is the owner for the presentation-complex realization
  data, `TwoComplex.Hom` and `TwoComplex.Hom.IsCoveringMap` are the owners for `2`-complex maps
  and coverings, `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner for simple
  connectedness of the total space, and `TwoComplex.Hom.IsDeckTransformation` is the map-relative
  owner for automorphisms of the universal cover that descend to the base.
- `bridge/view`: `CayleyComplex.Coordinates.PresentationMap` is the thin bridge carrying the
  actual presentation complex `K(X; R)` and the canonical map `C(X; R) → K(X; R)` attached to a
  fixed Cayley-complex realization.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the owner for the actual Cayley
   complex data on `C(X; R)`.
2. `TwoComplex.Hom` and `TwoComplex.Hom.IsCoveringMap` from Proposition `3-3-4` are the owners
   for maps and coverings of `2`-complexes.
3. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner for simple connectedness
   of the universal cover.
4. `ModifiedCayleyComplex.faceBoundary_word` from Proposition `3-7-1` shows the project style for
   realizing a `2`-complex by cell coordinates together with explicit face-boundary word data.
5. `CayleyComplex.automorphism_cellAction_eq_leftTranslation` from Proposition `3-4-1`
   classifies the induced cell action of label-preserving Cayley-complex automorphisms, so the
   quotient statement here must be phrased via automorphisms over the canonical map rather than
   via all automorphisms of the source.

Primitive vs. derived:
- primitive data: an actual Cayley-complex realization `coords`, an actual presentation-complex
  realization on some `K`, and the canonical comparison map `C(X; R) → K(X; R)` recording how the
  Cayley coordinates forget the group coordinate while preserving signed edge labels and relator
  labels;
- derived API: connectedness of the Cayley complex, the covering-map property of the canonical
  comparison, the resulting universal-covering property, and the quotient-by-deck-transformations
  statement.
-/

universe u v

set_option autoImplicit false

namespace TwoComplex.Hom

variable {C' C : TwoComplex}

/-- A deck transformation of `φ : C' → C` is an automorphism of `C'` that commutes with `φ` on
vertices, oriented edges, and oriented faces. -/
structure IsDeckTransformation (φ : Hom C' C) (α : Aut C') : Prop where
  /-- The automorphism preserves the fibers of `φ` on vertices. -/
  comm_vertex (v : C'.skeleton) :
      φ.toVertex (α.vertexPerm v) = φ.toVertex v
  /-- The automorphism preserves the fibers of `φ` on oriented edges. -/
  comm_edge (e : C'.skeleton.Edge) :
      φ.toEdge (α.edgePerm e) = φ.toEdge e
  /-- The automorphism preserves the fibers of `φ` on oriented faces. -/
  comm_face (D : C'.Face) :
      φ.mapFace (α.facePerm D) = φ.mapFace D

/-- A morphism of `2`-complexes presents the target as the quotient of the source by its deck
transformations when it is surjective on cells and its fibers are exactly the
deck-transformation orbits. -/
structure IsQuotientByDeckTransformations (φ : Hom C' C) : Prop where
  /-- Every target vertex is the image of some source vertex. -/
  vertex_surjective : Function.Surjective φ.toVertex
  /-- Every target oriented edge is the image of some source oriented edge. -/
  edge_surjective : Function.Surjective φ.toEdge
  /-- Every target face is the image of some source face. -/
  face_surjective : Function.Surjective φ.mapFace
  /-- Two vertices have the same image exactly when they lie in the same deck-transformation
  orbit. -/
  vertex_orbit_iff (v₁ v₂ : C'.skeleton) :
      φ.toVertex v₁ = φ.toVertex v₂ ↔
        ∃ α : Aut C', IsDeckTransformation φ α ∧ α.vertexPerm v₁ = v₂
  /-- Two oriented edges have the same image exactly when they lie in the same
  deck-transformation orbit. -/
  edge_orbit_iff (e₁ e₂ : C'.skeleton.Edge) :
      φ.toEdge e₁ = φ.toEdge e₂ ↔
        ∃ α : Aut C', IsDeckTransformation φ α ∧ α.edgePerm e₁ = e₂
  /-- Two faces have the same image exactly when they lie in the same deck-transformation orbit.
  -/
  face_orbit_iff (D₁ D₂ : C'.Face) :
      φ.mapFace D₁ = φ.mapFace D₂ ↔
        ∃ α : Aut C', IsDeckTransformation φ α ∧ α.facePerm D₁ = D₂

end TwoComplex.Hom

namespace PresentationComplex

open Quiver.Path

variable {X : Type u} {R : Set (FreeGroup X)}

/-- Coordinates on an actual `2`-complex realizing it as the presentation complex `K(X; R)` with
one vertex, oriented edges indexed by signed generators, geometric faces indexed by relators in
`R`, and a chosen oriented representative of each relator face attached along the corresponding
relator word. -/
structure Coordinates (K : TwoComplex) (X : Type u) (R : Set (FreeGroup X)) where
  /-- The chosen identification of vertices with the unique vertex of the presentation complex. -/
  vertexEquiv : K.skeleton ≃ Unit
  /-- The chosen identification of oriented edges with signed generators. -/
  edgeEquiv : K.skeleton.Edge ≃ SignedLetter X
  /-- Reversing an oriented edge toggles the sign of the corresponding generator. -/
  edgeInv_apply (e : K.skeleton.Edge) :
      edgeEquiv e⁻¹ = (edgeEquiv e)⁻¹
  /-- The chosen identification of geometric faces with the relators. -/
  geometricFaceEquiv : TwoComplex.GeometricFace K ≃ ↥R
  /-- The chosen oriented representative of the relator face `r`. -/
  orientedFace (r : ↥R) : K.Face
  /-- The chosen representative of `r` lies in the corresponding geometric-face class. -/
  orientedFace_geometricFace (r : ↥R) :
      geometricFaceEquiv (⟦orientedFace r⟧ : TwoComplex.GeometricFace K) = r
  /-- The chosen boundary path of the oriented relator face `r` is based at the unique vertex of
  the presentation complex. -/
  faceBoundary (r : ↥R) :
      K.BoundaryPath (orientedFace r) (vertexEquiv.symm ())
  /-- The chosen boundary path of `r` reads exactly the relator `r`. -/
  faceBoundary_word (r : ↥R) :
      FreeGroup.mk ((edgeList (faceBoundary r).1).map fun e ↦ edgeEquiv e.hom.1) = (r : FreeGroup X)

end PresentationComplex

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- The actual Cayley complex `C(X; R)` is connected. -/
theorem cayleyComplex_connected
    (coords : PresentationCoordinates C R) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton) := sorry

/-- A chosen realization of the canonical comparison map from the Cayley complex `C(X; R)` to the
presentation complex `K(X; R)` attached to the same relator set. -/
structure PresentationMap
    (coords : PresentationCoordinates C R) where
  /-- The actual presentation complex `K(X; R)`. -/
  presentationComplex : TwoComplex.{v}
  /-- Chosen presentation-complex coordinates on `K(X; R)`. -/
  presentationCoordinates : PresentationComplex.Coordinates presentationComplex X R
  /-- The canonical quotient map `C(X; R) → K(X; R)`. -/
  toPresentation : TwoComplex.Hom C presentationComplex
  /-- On vertices, the canonical map forgets the group coordinate. -/
  map_vertex (v : C.skeleton) :
      presentationCoordinates.vertexEquiv (toPresentation.toVertex v) = ()
  /-- On oriented edges, the canonical map forgets the group coordinate and keeps the signed
  generator label. -/
  map_edge (e : C.skeleton.Edge) :
      presentationCoordinates.edgeEquiv (toPresentation.toEdge e) = (coords.edgeEquiv e).2
  /-- On geometric faces, the canonical map forgets the group coordinate and keeps the relator
  label. -/
  map_geometricFace (D : TwoComplex.GeometricFace C) :
      presentationCoordinates.geometricFaceEquiv (toPresentation.mapGeometricFace D) =
        (coords.geometricFaceEquiv D).2

namespace PresentationMap

variable {coords : PresentationCoordinates C R}

/-- The canonical map `C(X; R) → K(X; R)` is a covering map. -/
theorem toPresentation_isCoveringMap (P : PresentationMap coords) :
    P.toPresentation.IsCoveringMap := sorry

/-- Proposition 3-4-3 (1): the Cayley complex `C(X; R)` is the universal covering of the
presentation complex `K(X; R)`. -/
-- Proof sketch: the canonical map is a covering map, Proposition `3-4-2` gives simple
-- connectedness of `C(X; R)`, and the Cayley complex is connected.
theorem toPresentation_isUniversalCovering
    (P : PresentationMap coords) :
    P.toPresentation.IsCoveringMap ∧
      TwoComplex.IsSimplyConnected C ∧
      Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton) :=
  ⟨P.toPresentation_isCoveringMap, isSimplyConnected coords, cayleyComplex_connected coords⟩

/-- Proposition 3-4-3 (2): the presentation complex `K(X; R)` is the quotient complex of
`C(X; R)` by the deck transformations of the canonical covering map. -/
-- Proof sketch: a deck transformation of `P.toPresentation` preserves the signed edge labels and
-- relator labels remembered by the presentation-complex coordinates, so Proposition `3-4-1`
-- identifies it with a unique left translation. Since `P.toPresentation` forgets only the group
-- coordinate on vertices, oriented edges, and geometric faces,
-- two cells have the same image exactly when they differ by such a translation.
theorem toPresentation_isQuotientByDeckTransformations
    (P : PresentationMap coords) :
    P.toPresentation.IsQuotientByDeckTransformations := sorry

end PresentationMap

end CayleyComplex.Coordinates
