/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_8
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊¹" => Metric.sphere (0 : 𝔼²) 1

section

variable {X : Type u}

/-!
Primary domain: annular van Kampen diagrams in the plane.

Layer triage:
- `source-facing`: an annular `R`-diagram with chosen outer and inner boundary cycles whose
  labels represent conjugate elements in the presented group.
- `core/canonical`: `GroupDiagram (FreeGroup X)` is the owner of the labelled diagram,
  `GroupDiagram.IsRDiagram` is the owner of the relator condition,
  `TwoComplex.TwoManifoldEmbedding` with `IsPlanarMap` is the owner of the planar realization, and
  `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` is the owner of an individual ambient boundary
  cycle, while `TwoComplex.Subcomplex.HasSimpleBoundary`, used in Lemma `5-4-3` on
  `C.fullSubcomplex`, is the established whole-boundary simple-cycle owner.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.boundaryCycleSupport` is the owner-side planar
  support of a chosen boundary cycle, and
  `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` is the owner-side annular boundary
  decomposition asserting that the actual ambient boundary subset is the union of two disjoint
  simple closed curves carried by the chosen outer and inner boundary cycles.
  `GroupDiagram.AnnularRDiagram` then packages exactly the source-facing annular `R`-diagram
  data built from that geometry and the `R`-diagram hypothesis. `Loop` and `cyclicPath` provide
  the based representatives needed to read boundary labels.

Domain sampling:
1. `GroupDiagram.IsRDiagram` from Definition `5-1-8` is the chapter owner for the `R`-diagram
   hypothesis.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the owner predicate
   for a chosen boundary cycle.
3. `TwoComplex.Subcomplex.HasSimpleBoundary` from Proposition `3-7-5` is the established owner
   shape for saying that a subcomplex boundary is a simple cycle, with Lemma `5-4-3` using it for
   the whole map via `C.fullSubcomplex`.
4. `GroupDiagram.pathLabel` from Definition `5-1-4` is the owner map for reading the label of a
   based boundary loop.

Primitive vs. derived:
- primitive public data: the owner-side planar support `embedding.boundaryCycleSupport c` of a
  chosen boundary cycle, the generic annular boundary decomposition
  `embedding.HasAnnularBoundaryCycles σ τ` asserting that the actual map boundary is the union of
  two disjoint simple closed curves supported by `σ` and `τ`, and the source-facing owner
  `GroupDiagram.AnnularRDiagram R` consisting of a labelled diagram, a planar embedding, chosen
  outer and inner boundary cycles, and the `R`-diagram hypothesis;
- derived API: the conjugacy conclusion in `PresentedGroup R`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

variable {C : TwoComplex}

/-- The planar support of a chosen boundary cycle is the union of the closed geometric edge-images
of the geometric edges traversed by that cycle. -/
def boundaryCycleSupport (embedding : TwoManifoldEmbedding C 𝔼²)
    (c : CyclicPath C.skeleton) : Set 𝔼² :=
  Set.sUnion (embedding.geometricEdgeSet '' { e | c.SupportsGeometricEdge e })

/-- Chosen outer and inner boundary cycles for an annular planar map. They are required to be
simple boundary cycles whose planar supports are disjoint simple closed curves and whose union is
the actual boundary of the map. -/
structure HasAnnularBoundaryCycles
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (σ τ : CyclicPath C.skeleton) : Prop where
  /-- The underlying `1`-skeleton is connected. -/
  skeleton_connected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)
  /-- `σ` is the outer boundary cycle. -/
  outer_isBoundaryCycle : embedding.IsBoundaryCycle σ
  /-- `τ` is the inner boundary cycle. -/
  inner_isBoundaryCycle : embedding.IsBoundaryCycle τ
  /-- The planar support of the outer boundary cycle is a simple closed curve. -/
  outer_support_isSimpleClosedCurve :
    ∃ γ : 𝕊¹ → 𝔼²,
      Continuous γ ∧ Function.Injective γ ∧
        embedding.boundaryCycleSupport σ = Set.range γ
  /-- The planar support of the inner boundary cycle is a simple closed curve. -/
  inner_support_isSimpleClosedCurve :
    ∃ γ : 𝕊¹ → 𝔼²,
      Continuous γ ∧ Function.Injective γ ∧
        embedding.boundaryCycleSupport τ = Set.range γ
  /-- The actual ambient boundary of the planar map is exactly the union of the two boundary
  components carried by the chosen cycles. -/
  boundary_eq_outer_inner :
    embedding.boundary =
      embedding.boundaryCycleSupport σ ∪ embedding.boundaryCycleSupport τ
  /-- The two boundary components are disjoint as subsets of the plane. -/
  outer_inner_disjoint :
    Disjoint (embedding.boundaryCycleSupport σ) (embedding.boundaryCycleSupport τ)

end TwoManifoldEmbedding
end TwoComplex

namespace GroupDiagram

/-- An annular `R`-diagram is a group diagram in the plane with chosen outer and inner boundary
cycles whose planar supports are disjoint simple closed curves and whose union is the actual
ambient boundary of the planar map. -/
structure AnnularRDiagram (R : Set (FreeGroup X)) extends GroupDiagram (FreeGroup X) where
  /-- A planar realization of the underlying labelled map. -/
  embedding : TwoComplex.TwoManifoldEmbedding source 𝔼²
  /-- The chosen realization is planar. -/
  [isPlanarMap : embedding.IsPlanarMap]
  /-- The chosen outer boundary cycle. -/
  outerBoundary : CyclicPath source.skeleton
  /-- The chosen inner boundary cycle. -/
  innerBoundary : CyclicPath source.skeleton
  /-- The two chosen boundary cycles form the annular boundary of the planar map. -/
  annular : embedding.HasAnnularBoundaryCycles outerBoundary innerBoundary
  /-- The labelled map is an `R`-diagram. -/
  isRDiagram : toGroupDiagram.IsRDiagram R

namespace AnnularRDiagram

variable {R : Set (FreeGroup X)}

/-- An annular `R`-diagram is used via its underlying labelled diagram. -/
instance : CoeOut (AnnularRDiagram R) (GroupDiagram (FreeGroup X)) where
  coe := AnnularRDiagram.toGroupDiagram

-- Proof sketch: choose a path in the connected annular diagram from a vertex on the outer
-- boundary cycle to a vertex on the inner boundary cycle. Cutting the annulus open along that
-- path produces a singular disc whose boundary label is
-- `M.pathLabel outer.2 * b * (M.pathLabel inner.2) * b⁻¹`. The van Kampen relation for an
-- `R`-diagram makes this boundary word trivial in `PresentedGroup R`, so the image of the outer
-- boundary label is conjugate to the inverse of the inner boundary label there.
/-- In an annular `R`-diagram, the image of the label of a chosen outer boundary loop is conjugate
to the inverse of the label of a chosen inner boundary loop in the presented group
`PresentedGroup R`. -/
theorem outerBoundaryLabel_isConj_innerBoundaryLabelInv
    (M : AnnularRDiagram R) (outer inner : Loop M.source.skeleton)
    (houter : cyclicPath outer = M.outerBoundary)
    (hinner : cyclicPath inner = M.innerBoundary) :
    IsConj (PresentedGroup.mk R (M.pathLabel outer.2))
      (PresentedGroup.mk R ((M.pathLabel inner.2)⁻¹)) := sorry

end AnnularRDiagram

/-- Lemma 5-5-1: if `M` is an annular `R`-diagram, `u` is the label of an outer boundary cycle of
`M`, and `z⁻¹` is the label of an inner boundary cycle of `M`, then `u` and `z` represent
conjugate elements of the presented group `PresentedGroup R`. -/
theorem outerBoundaryLabel_isConj_of_innerBoundaryInverseLabel
    {R : Set (FreeGroup X)} (M : AnnularRDiagram R)
    (outer inner : Loop M.source.skeleton)
    (houter : cyclicPath outer = M.outerBoundary)
    (hinner : cyclicPath inner = M.innerBoundary)
    (u z : FreeGroup X)
    (hu : M.pathLabel outer.2 = u) (hz : M.pathLabel inner.2 = z⁻¹) :
    IsConj (PresentedGroup.mk R u) (PresentedGroup.mk R z) := by
  simpa [hu, hz] using
    M.outerBoundaryLabel_isConj_innerBoundaryLabelInv outer inner houter hinner

end GroupDiagram

end
