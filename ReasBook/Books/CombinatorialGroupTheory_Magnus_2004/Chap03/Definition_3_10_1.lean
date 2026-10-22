/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_7
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Quiver.Path
open CayleyComplex.Coordinates

set_option autoImplicit false

noncomputable section

/-!
Primary domain: spherical diagrams over Cayley complexes and the asphericity of a presentation.

Layer triage:
- `source-facing`: a spherical diagram over the actual Cayley complex `C(X; R)`, its reducedness,
  reduction, triviality, and the resulting asphericity notion for the presentation.
- `core/canonical`: `CayleyComplex.Coordinates` is the owner for the actual Cayley complex of
  `(X; R)`, `TwoComplex.IsSphericalDiagram` is the owner predicate for a combinatorial sphere,
  `TwoComplex.Subcomplex.IsSingularDisc` is the owner predicate for singular subdiscs,
  `TwoComplex.Hom` and `OneComplex.Hom.mapLoop` are the owner maps for sending a carried loop in
  a subdisc into the ambient Cayley complex, and
  `CayleyComplex.Coordinates.boundaryLabel` is the owner for boundary labels in the actual
  Cayley complex.
- `bridge/view`: the source phrase “a spherical diagram is a pair `(S, f)`” is packaged by the
  structure `CayleyComplex.Coordinates.SphericalDiagram`, while the reduction operation is
  expressed by a direct one-step relation carrying the chosen reducible subdisc, its deleted-face
  complement, and explicit sewing comparison data into the target spherical diagram; then
  `Relation.ReflTransGen` is the canonical owner for finite reduction sequences.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the chapter owner for a chosen actual
   Cayley complex attached to `(X; R)`, so the source-facing API should land directly in `C`.
2. `TwoComplex.IsSphericalDiagram` from Proposition `3-9-7` already packages the connected,
   simply connected, sphere-embedding part of “combinatorial sphere”.
3. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the owner for a singular
   subdisc with explicit boundary loop data.
4. `OneComplex.Hom.mapLoop` applied to the inclusion `S.skeleton.inclusion`,
   `TwoComplex.Hom.mapLoop`, and
   `CayleyComplex.Coordinates.boundaryLabel` are the chapter owners for comparing a carried
   subdisc boundary loop with its image in the actual Cayley complex and reading the resulting
   signed boundary word there.
5. `Relation.ReflTransGen` is the canonical closure operator for “obtainable by finitely many
   reductions”, so triviality should be expressed with that owner rather than a bespoke
   transitive closure.

Primitive vs. derived:
- primitive data: the source `2`-complex, the map into the actual Cayley complex, finiteness of
  the source cells, and for a reduction step the chosen two-face singular subdisc, the complement
  of the deleted faces, and the explicit sewing comparison into the target;
- derived API: reducedness, triviality via repeated reductions, and asphericity of the
  presentation.
-/

namespace TwoComplex.Subcomplex

/-- A singular subdisc has exactly two geometric faces when its carried face set has exactly two
elements modulo orientation reversal. -/
def HasExactlyTwoGeometricFaces {C : TwoComplex} (S : Subcomplex C) : Prop :=
  ∃ F₁ F₂ : TwoComplex.GeometricFace S.complex,
    F₁ ≠ F₂ ∧
      ∀ F : TwoComplex.GeometricFace S.complex, F = F₁ ∨ F = F₂

end TwoComplex.Subcomplex

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Definition 3-10-1 (1): a spherical diagram over `(X; R)` is a finite combinatorial sphere
together with a dimension-preserving map into the actual Cayley complex `C(X; R)`. -/
structure SphericalDiagram
    (coords : PresentationCoordinates C R) where
  /-- The finite combinatorial sphere underlying the spherical diagram. -/
  source : TwoComplex
  /-- The dimension-preserving map into the Cayley complex `C(X; R)`. -/
  map : TwoComplex.Hom source C
  /-- The source has finitely many vertices. -/
  finite_vertex : Finite source.skeleton
  /-- The source has finitely many oriented edges. -/
  finite_edge : Finite source.skeleton.Edge
  /-- The source has finitely many oriented faces. -/
  finite_face : Finite source.Face
  /-- The source is a combinatorial sphere. -/
  spherical : source.IsSphericalDiagram

namespace SphericalDiagram

variable {coords : PresentationCoordinates C R}

/-- A spherical diagram is used via its underlying source `2`-complex. -/
instance : CoeOut (SphericalDiagram coords) TwoComplex where
  coe := SphericalDiagram.source

/-- The source `1`-skeleton of a spherical diagram is finite. -/
instance (Δ : SphericalDiagram coords) : Finite Δ.source.skeleton := Δ.finite_vertex

/-- The oriented edge set of the source of a spherical diagram is finite. -/
instance (Δ : SphericalDiagram coords) : Finite Δ.source.skeleton.Edge := Δ.finite_edge

/-- The oriented face set of the source of a spherical diagram is finite. -/
instance (Δ : SphericalDiagram coords) : Finite Δ.source.Face := Δ.finite_face

/-- A carried singular subdisc has trivial boundary label when one of its boundary loops reads a
word equal to `1` in the free group on the generators. -/
def HasTrivialBoundaryLabel (Δ : SphericalDiagram coords)
    (S : TwoComplex.Subcomplex Δ.source) : Prop :=
  ∃ (p : Loop S.skeleton.toOneComplex)
    (_ : TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p))
    (w : List (SignedLetter X)),
      boundaryLabel coords (Δ.map.mapLoop (S.skeleton.inclusion.mapLoop p)) = w ∧
        FreeGroup.mk w = 1

/-- A spherical diagram has a reducible subdisc when it contains a singular two-face subdisc whose
boundary label is trivial in the free group. -/
def HasReducibleSubdisc (Δ : SphericalDiagram coords) : Prop :=
  ∃ S : TwoComplex.Subcomplex Δ.source,
    S.HasExactlyTwoGeometricFaces ∧
      Δ.HasTrivialBoundaryLabel S

/-- Definition 3-10-1 (2): a spherical diagram is reduced when it contains no singular subdisc
with exactly two geometric faces and trivial boundary label. -/
def IsReduced (Δ : SphericalDiagram coords) : Prop :=
  ¬ Δ.HasReducibleSubdisc

/-- The deleted-face complement of a chosen reducible subdisc is the carried subcomplex whose
oriented faces are exactly the ambient faces not belonging to that subdisc. -/
def IsDeletedFaceComplement (Δ : SphericalDiagram coords)
    (S T : TwoComplex.Subcomplex Δ.source) : Prop :=
  ∀ D : Δ.source.Face, D ∈ T.faceSet ↔ D ∉ S.faceSet

/-- A sewing comparison from the deleted-face complement into a target spherical diagram is a
surjective map on the carried `1`-skeleton, bijective on the remaining oriented faces, and
compatible with the ambient map to the actual Cayley complex. -/
def IsSewingComparison (Δ : SphericalDiagram coords) (T : TwoComplex.Subcomplex Δ.source)
    (Δ' : SphericalDiagram coords) (sew : TwoComplex.Hom T.complex Δ'.source) : Prop :=
  let C' := T.complex
  let K := C'.skeleton
  Function.Surjective sew.toVertex ∧
    Function.Surjective sew.toEdge ∧
    Function.Bijective sew.mapFace ∧
    (∀ v : K, Δ'.map.toVertex (sew.toVertex v) = Δ.map.toVertex v.1) ∧
    (∀ e : K.Edge,
      Δ'.map.toEdge (sew.toEdge e) = Δ.map.toEdge e.1) ∧
    ∀ D : C'.Face, Δ'.map.mapFace (sew.mapFace D) = Δ.map.mapFace D.1

/-- Definition 3-10-1 (3): a one-step reduction deletes a reducible singular two-face subdisc and
sews up the complementary faces. If the chosen subdisc already contains every oriented face of the
source, the result is the empty diagram. -/
inductive ReductionStep : Option (SphericalDiagram coords) → Option (SphericalDiagram coords) → Prop
  | toEmpty
      (Δ : SphericalDiagram coords)
      (reducibleSubdisc : TwoComplex.Subcomplex Δ.source)
      (reducible_twoFace : reducibleSubdisc.HasExactlyTwoGeometricFaces)
      (reducible_trivialBoundary : Δ.HasTrivialBoundaryLabel reducibleSubdisc)
      (covers_faces : ∀ D : Δ.source.Face, D ∈ reducibleSubdisc.faceSet) :
      ReductionStep (some Δ) none
  | toDiagram
      (Δ Δ' : SphericalDiagram coords)
      (reducibleSubdisc : TwoComplex.Subcomplex Δ.source)
      (reducible_twoFace : reducibleSubdisc.HasExactlyTwoGeometricFaces)
      (reducible_trivialBoundary : Δ.HasTrivialBoundaryLabel reducibleSubdisc)
      (deletedFaceComplement : TwoComplex.Subcomplex Δ.source)
      (deletedFaceComplement_spec :
        IsDeletedFaceComplement Δ reducibleSubdisc deletedFaceComplement)
      (sew : TwoComplex.Hom deletedFaceComplement.complex Δ'.source)
      (sew_spec :
        IsSewingComparison Δ deletedFaceComplement Δ' sew) :
      ReductionStep (some Δ) (some Δ')

/-- Definition 3-10-1 (4): a spherical diagram is trivial when a finite sequence of reductions
carries it to the empty diagram. -/
def IsTrivial (Δ : SphericalDiagram coords) : Prop :=
  Relation.ReflTransGen ReductionStep (some Δ) none

end SphericalDiagram

/-- Definition 3-10-1 (5): the presentation `(X; R)` and its associated Cayley complex are
aspherical when every spherical diagram over `C(X; R)` is trivial. -/
def IsAspherical
    (coords : PresentationCoordinates C R) : Prop :=
  ∀ Δ : SphericalDiagram coords, Δ.IsTrivial

end CayleyComplex.Coordinates
