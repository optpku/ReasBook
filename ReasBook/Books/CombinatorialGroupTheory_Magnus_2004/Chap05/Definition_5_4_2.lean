/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_7

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: extremal disc submaps in planar map theory.

Layer triage:
- `source-facing`: a submap `K` of a map `M` that is topologically a disk and whose boundary
  edges occur in order along some boundary cycle of `M`.
- `core/canonical`: `TwoComplex.Subcomplex` is the project owner for submaps,
  `TwoComplex.Subcomplex.IsSingularDisc` is the existing owner predicate for disc-like submaps
  together with a chosen boundary cycle, and `TwoComplex.TwoManifoldEmbedding.IsBoundaryEdge` is the
  owner predicate for ambient boundary edges of a planar map.
- `bridge/view`: `Loop`, `cyclicPath`, `edgeList`, and `OneComplex.Hom.mapLoop` applied to the
  inclusion `K.skeleton.inclusion` compare a boundary cycle in the submap with a boundary cycle
  in the ambient map through ordered total-edge lists.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the chapter owner for submaps.
2. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the owner predicate for a
   submap that is topologically a disk together with an explicit boundary cycle.
3. `TwoComplex.TwoManifoldEmbedding.IsBoundaryEdge` from Definition `5-2-7` is the owner predicate
   for edges lying on the boundary of the ambient planar map.
4. `Loop`, `cyclicPath`, and `edgeList` from Definition `3-2-3` are the canonical ordered
   boundary-cycle API, and `OneComplex.Hom.mapLoop` applied to `K.skeleton.inclusion` is the
   bridge from a submap boundary loop to the corresponding ambient boundary loop.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

variable {C : TwoComplex}

/-- The edges of a chosen submap boundary cycle occur in order in a chosen ambient boundary cycle
when some representatives of those cyclic paths give a sublist relation after mapping the submap
edges into the ambient map. This is a file-local bridge used only to state `IsExtremalDisk`. -/
private def boundaryCycleOccursInOrder (K : Subcomplex C)
    (boundaryK : CyclicPath K.skeleton.toOneComplex) (boundaryM : CyclicPath C.skeleton) : Prop :=
  let inclusion := K.skeleton.inclusion
  ∃ pK : Loop K.skeleton.toOneComplex, cyclicPath pK = boundaryK ∧
    ∃ pM : Loop C.skeleton, cyclicPath pM = boundaryM ∧
      List.Sublist (inclusion.mapLoop pK).2.edgeList pM.2.edgeList

/-- A boundary cycle of a surface embedding is a simple cycle all of whose geometric edges lie on
the boundary of the ambient map. -/
def IsBoundaryCycle (embedding : TwoManifoldEmbedding C 𝔼²)
    (c : CyclicPath C.skeleton) : Prop :=
  IsSimpleCycle c ∧
    ∀ ⦃e : OneComplex.GeometricEdge C.skeleton⦄,
      c.SupportsGeometricEdge e → embedding.IsBoundaryEdge e

/-- A planar map has simple boundary when one simple ambient boundary cycle carries exactly the
boundary edges of the whole map. -/
def HasSimpleBoundary (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  ∃ c : CyclicPath C.skeleton,
    embedding.IsBoundaryCycle c ∧
      ∀ e : OneComplex.GeometricEdge C.skeleton,
        embedding.IsBoundaryEdge e ↔ c.SupportsGeometricEdge e

/-- Definition 5-4-2: an extremal disk of a planar map `embedding` is a submap `K` that is a
topological disk and has a boundary cycle whose edges occur in order in some boundary cycle of the
whole map. -/
def IsExtremalDisk (embedding : TwoManifoldEmbedding C 𝔼²)
    (K : Subcomplex C) : Prop :=
  ∃ boundaryK : CyclicPath K.skeleton.toOneComplex, ∃ boundaryM : CyclicPath C.skeleton,
    K.IsSingularDisc boundaryK ∧
      embedding.IsBoundaryCycle boundaryM ∧
        boundaryCycleOccursInOrder K boundaryK boundaryM

end TwoManifoldEmbedding
end TwoComplex
