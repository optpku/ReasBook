/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_7

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: combinatorial degrees attached to vertices and regions of a planar map.

Layer triage:
- `source-facing`: the degree of a vertex, the degree of a region, and for a chosen planar map
  the number `i(D)` of interior edges occurring in a region boundary cycle.
- `core/canonical`: `OneComplex` is the owner of vertices and oriented edges,
  `TwoComplex.GeometricFace` is the owner of unoriented regions, `Cycle.length` and
  `Cycle.toMultiset` are the canonical multiplicity-sensitive boundary owners, and
  `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` from Definition `5-2-7` is the chapter owner for
  interior edges of a planar map.
- `bridge/view`: an oriented face representative presents a geometric face, and a total boundary
  arrow determines the corresponding geometric edge via `TwoComplex.boundaryArrowGeometricEdge`.

Domain sampling:
1. `OneComplex.initial` is the owner map for the initial vertex of an oriented edge.
2. `Cycle.length` and `Cycle.toMultiset` are the canonical ways to read multiplicity-sensitive
   size and order-insensitive multiplicity data from a cyclic boundary.
3. `TwoComplex.GeometricFace` is the owner carrier for textbook regions, so region invariants
   should be defined on geometric faces rather than on oriented face representatives.
4. `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` from Definition `5-2-7` is the owner predicate
   for interior edges of a planar map, so `i(D)` should count boundary arrows whose geometric
   edge is interior for the chosen planar embedding.
-/

namespace OneComplex

/-- Definition 5-2-8 (1): the degree of a vertex is the number of oriented edges having that
vertex as initial vertex, so a loop based at the vertex contributes twice through its two
orientations. -/
def vertexDegree (C : OneComplex) [Finite C.Edge] (v : C) : ℕ :=
  Nat.card { e : C.Edge // C.initial e = v }

end OneComplex

namespace TwoComplex

/-- Reversing the orientation of a face does not change the number of edges in its boundary
cycle. -/
-- Proof sketch: rewrite the inverse-face boundary as `inverseCycle` and use that
-- `Cycle.length` is unchanged by reversal.
private theorem orientedRegionDegree_eq_of_geometricFaceSetoid (C : TwoComplex) (D E : C.Face)
    (h : C.geometricFaceSetoid.r D E) :
    (C.boundary D).1.length = (C.boundary E).1.length := sorry

/-- Definition 5-2-8 (2): the degree of a region is the number of edges in one of its boundary
cycles, counted with multiplicity. -/
def regionDegree (C : TwoComplex) : GeometricFace C → ℕ :=
  Quotient.lift
    (fun D ↦ (C.boundary D).1.length)
    (C.orientedRegionDegree_eq_of_geometricFaceSetoid)

/-- A geometric face represented by `D` has region degree equal to the length of the boundary
cycle of `D`. -/
-- Proof sketch: evaluate the quotient lift `regionDegree` on the representative `D`.
@[simp] theorem regionDegree_mk (C : TwoComplex) (D : C.Face) :
    C.regionDegree ⟦D⟧ = (C.boundary D).1.length :=
  rfl

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- A planar map has interior vertex degree at least `n` when every interior vertex has degree at
least `n`. -/
def HasInteriorVertexDegreeAtLeast (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] (n : ℕ) : Prop :=
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  ∀ v : C.skeleton, embedding.IsInteriorVertex v → n ≤ C.skeleton.vertexDegree v

/-- A boundary arrow of a region boundary cycle traverses an interior edge exactly when its
underlying geometric edge is interior for the chosen planar map. -/
private def boundaryArrowTraversesInteriorEdge
    (embedding : TwoManifoldEmbedding C 𝔼²) (a : Quiver.Total C.skeleton) : Prop :=
  embedding.IsInteriorEdge (C.boundaryArrowGeometricEdge a)

/-- The multiplicity-sensitive interior-edge count attached to a boundary cycle. -/
def boundaryCycleInteriorEdgeCount
    (embedding : TwoManifoldEmbedding C 𝔼²) (c : Cycle (Quiver.Total C.skeleton)) : ℕ :=
  let _ : DecidablePred embedding.boundaryArrowTraversesInteriorEdge := Classical.decPred _
  c.toMultiset.countP embedding.boundaryArrowTraversesInteriorEdge

/-- The oriented interior-boundary count counts those arrows in an oriented face boundary whose
underlying geometric edge is interior. -/
private theorem orientedBoundaryInteriorEdgeCount_eq_of_geometricFaceSetoid
    (embedding : TwoManifoldEmbedding C 𝔼²) (D E : C.Face) (h : C.geometricFaceSetoid.r D E) :
    embedding.boundaryCycleInteriorEdgeCount (C.boundary D).1 =
      embedding.boundaryCycleInteriorEdgeCount (C.boundary E).1 := sorry

/-- Definition 5-2-8 (3): `i(D)` is the number of interior edges occurring in a boundary cycle of
the region `D` in the chosen planar map, with an edge counted twice when it occurs twice in that
boundary cycle. -/
def boundaryInteriorEdgeCount (embedding : TwoManifoldEmbedding C 𝔼²) : GeometricFace C → ℕ :=
  Quotient.lift
    (fun D ↦ embedding.boundaryCycleInteriorEdgeCount (C.boundary D).1)
    embedding.orientedBoundaryInteriorEdgeCount_eq_of_geometricFaceSetoid

/-- A geometric face represented by `D` has interior-edge count equal to the number of arrows in
its boundary cycle whose underlying geometric edge is interior in the chosen planar map. -/
-- Proof sketch: evaluate the quotient lift `boundaryInteriorEdgeCount` on `D` and unfold the
-- cycle-level multiplicity count.
@[simp] theorem boundaryInteriorEdgeCount_mk
    (embedding : TwoManifoldEmbedding C 𝔼²) (D : C.Face) :
    embedding.boundaryInteriorEdgeCount ⟦D⟧ =
      embedding.boundaryCycleInteriorEdgeCount (C.boundary D).1 :=
  rfl

end

end TwoManifoldEmbedding

end TwoComplex
