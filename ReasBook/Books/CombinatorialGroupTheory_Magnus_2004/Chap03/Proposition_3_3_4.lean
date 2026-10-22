/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_8
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Quiver.Path

namespace TwoComplex

/-
Layer triage:
- `source-facing`: a connected `2`-complex `C`, a base vertex `v : C.skeleton`, a subgroup
`H ≤ π(C, v)`, and a connected covering `2`-complex whose induced map on fundamental groups
identifies the covering group with `H`.
- `core/canonical`: `TwoComplex.Hom`, extending the chapter owner `OneComplex.Hom` on the
  `1`-skeleton, is the source-faithful owner for maps of `2`-complexes,
  `TwoComplex.Hom.IsCoveringMap` is the owner abstraction for coverings of `2`-complexes,
  `Quiver.Prefunctor.IsCovering` for `φ.toPrefunctor` is the canonical owner for the
  `1`-skeleton covering data reused by that class, and `CategoryTheory.Functor.mapEnd` is the
  owner API for the induced map on based fundamental groups.
- `bridge/view`: `TwoComplex.Hom.piFunctor` and
  `TwoComplex.Hom.inducedFundamentalGroupHomOver` are the induced functor on fundamental
  groupoids and its based vertex-group specialization, while `TwoComplex.BoundaryStar` and
  `TwoComplex.Hom.mapBoundaryStar` express the `2`-cell lifting condition using the existing
  path-based `BoundaryPath` owner API.

Domain sampling:
1. `OneComplex.Hom` from Proposition `3-3-1` is the chapter owner for morphisms of `1`-complexes.
2. `TwoComplex.BoundaryPath` is the project owner for a face corner based at a chosen vertex.
3. `Quiver.Prefunctor.IsCovering` is the canonical owner predicate for the `1`-skeleton part of a
   covering, accessed here through `OneComplex.Hom.toPrefunctor`.
4. `OneComplex.Hom.pi1Functor` and `CategoryTheory.Functor.mapEnd` give the chapter/mathlib owner
   pattern for passing from a map of path groupoids to the induced homomorphism on based
   fundamental groups.

Primitive vs. derived:
- primitive data: the skeleton morphism, the face map, and compatibility saying that mapped face
  boundary loops are boundary loops of the image face; for coverings, the primitive extra data is
  the existing `1`-skeleton covering owner together with the bijective lifting condition on based
  boundary paths over each vertex;
- derived API: the induced functor on `2`-dimensional path classes, the induced homomorphism on
  fundamental groups, and injectivity for covering maps.
-/

/-- The boundary star of a vertex records an oriented face together with a chosen boundary path of
that face beginning at the vertex. This is the `2`-cell analogue of the outgoing edge star used
for coverings of `1`-complexes. -/
abbrev BoundaryStar (C : TwoComplex) (v : C.skeleton) :=
  Σ D : C.Face, C.BoundaryPath D v

/-- A morphism of `2`-complexes is a morphism of the underlying `1`-skeletons together with a map
of oriented faces that respects face reversal and sends each boundary loop to the boundary loop of
the image face. -/
structure Hom (C' C : TwoComplex) extends OneComplex.Hom C'.skeleton C.skeleton where
  /-- The induced map on oriented faces. -/
  mapFace : C'.Face → C.Face
  /-- The face map preserves orientation reversal. -/
  map_faceInv (D : C'.Face) :
      mapFace (C'.faceInv D) = C.faceInv (mapFace D)
  /-- The image of a based boundary path of `D` is a based boundary path of `∂(mapFace D)`. -/
  mapBoundary {D : C'.Face} {v : C'.skeleton} (q : C'.BoundaryPath D v) :
      C.BoundaryPath (mapFace D) (toVertex v)

namespace Hom

variable {C' C : TwoComplex} (φ : Hom C' C)

/-- The map induced by a `2`-complex morphism on boundary stars over a chosen vertex. -/
def mapBoundaryStar (v : C'.skeleton) :
    C'.BoundaryStar v → C.BoundaryStar (φ.toVertex v)
  | ⟨D, q⟩ => ⟨φ.mapFace D, φ.mapBoundary q⟩

/-- A morphism of `2`-complexes induces the canonical map on geometric faces. -/
def mapGeometricFace : C'.GeometricFace → C.GeometricFace :=
  Quotient.map' φ.mapFace fun D E h ↦ by
    rcases h with h | h
    · exact Or.inl (congrArg φ.mapFace h)
    · exact Or.inr (by simpa [h] using φ.map_faceInv E)

@[simp] theorem mapGeometricFace_mk (D : C'.Face) :
    φ.mapGeometricFace (⟦D⟧ : C'.GeometricFace) = (⟦φ.mapFace D⟧ : C.GeometricFace) :=
  rfl

/-- A morphism of `2`-complexes is a covering map when it is a covering on the `1`-skeleton and
it bijectively lifts based face-boundary paths at every vertex. -/
class IsCoveringMap : Prop extends φ.toPrefunctor.IsCovering where
  /-- The induced map on incident oriented face corners at any chosen vertex is bijective. -/
  boundaryStar_bijective (v : C'.skeleton) : Function.Bijective (φ.mapBoundaryStar v)

/-- A `2`-complex morphism preserves the boundary-path reduction relation. -/
theorem mapPath_boundary_path_reduction_step {a b : C'.skeleton} {p q : Quiver.Path a b}
    (h : C'.boundary_path_reduction_step p q) :
    C.boundary_path_reduction_step (φ.mapPath p) (φ.mapPath q) := sorry

/-- A `2`-complex morphism preserves elementary `2`-reduction steps. -/
theorem mapPath_path_two_reduction_step {a b : C'.skeleton} {p q : Quiver.Path a b}
    (h : C'.path_two_reduction_step p q) :
    C.path_two_reduction_step (φ.mapPath p) (φ.mapPath q) := by
  rcases h with h | h
  · exact Or.inl (φ.mapPath_reduction_step h)
  · exact Or.inr (φ.mapPath_boundary_path_reduction_step h)

/-- A `2`-complex morphism preserves `2`-equivalence of paths. -/
theorem mapPath_path_two_equiv {a b : C'.skeleton} {p q : Quiver.Path a b}
    (h : C'.path_two_equiv p q) :
    C.path_two_equiv (φ.mapPath p) (φ.mapPath q) := sorry

/-- A morphism of `2`-complexes induces the canonical functor on fundamental groupoids. -/
def piFunctor : C'.pi ⥤ C.pi where
  obj a := ⟨φ.toVertex a.vertex⟩
  map := fun p ↦
    Quotient.map' φ.mapPath (fun _ _ h ↦ φ.mapPath_path_two_equiv h) p
  map_id a := by
    rfl
  map_comp p q := by
    sorry

/-- A `2`-complex morphism induces a homomorphism on based fundamental groups. -/
noncomputable def inducedFundamentalGroupHom (v : C'.skeleton) :
    π(C', v) →* π(C, φ.toVertex v) :=
  φ.piFunctor.mapEnd ⟨v⟩

/-- If a `2`-complex morphism sends `v'` to `v`, then it induces the usual homomorphism
`π(C', v') → π(C, v)`. -/
noncomputable def inducedFundamentalGroupHomOver (v' : C'.skeleton) (v : C.skeleton)
    (hv : φ.toVertex v' = v) :
    π(C', v') →* π(C, v) :=
  hv ▸ φ.inducedFundamentalGroupHom v'

/-- A covering map of `2`-complexes induces an injective homomorphism on based fundamental
groups. -/
theorem inducedFundamentalGroupHomOver_injective_of_isCoveringMap
    (hφ : IsCoveringMap φ) (v' : C'.skeleton) (v : C.skeleton) (hv : φ.toVertex v' = v) :
    Function.Injective (φ.inducedFundamentalGroupHomOver v' v hv) := sorry

end Hom

/-- Proposition 3-3-4: for any subgroup `H ≤ π(C, v)` of the fundamental group of a connected
`2`-complex `C`, there exists a connected covering `2`-complex `C' → C` with a chosen vertex `v'`
over `v` whose induced homomorphism `π(C', v') → π(C, v)` has image exactly `H`; injectivity is
the canonical consequence of the covering-map owner. -/
-- Proof sketch: first build the covering of the `1`-skeleton corresponding to the subgroup of
-- `π(C.skeleton, v)` from Proposition `3-3-2`. Then attach a `2`-cell over each lifted boundary
-- loop of a face of `C`, obtaining a connected `2`-complex covering whose induced map on
-- fundamental groups has image `H`; injectivity follows from covering-space lifting.
theorem exists_connected_covering_inducing_subgroup
    (C : TwoComplex) (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    (v : C.skeleton)
    (H : Subgroup (π(C, v))) :
    ∃ (C' : TwoComplex)
      (_ : Quiver.IsStronglyConnected (Quiver.Symmetrify C'.skeleton)) (φ : Hom C' C)
      (_ : Hom.IsCoveringMap φ) (v' : C'.skeleton) (hv' : φ.toVertex v' = v),
      (φ.inducedFundamentalGroupHomOver v' v hv').range = H := sorry

end TwoComplex
