/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_11_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_8
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_8
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_4
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_5_1

set_option autoImplicit false

noncomputable section

open Set Quiver.Path FreeGroupBasis GroupPresentation

universe u v

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqX_5_5_3 : DecidableEq X := Classical.decEq X

/-!
Primary domain: suitable annular small-cancellation `R`-diagrams.

Layer triage:
- `source-facing`: a reduced annular `R`-diagram with chosen outer and inner boundary cycles,
  the boundary-arc hypothesis excluding intersections whose labels are longer than half a relator,
  and the resulting structure theorem asserting clauses (i)–(iii).
- `core/canonical`: `GroupDiagram F` is the owner of the labelled diagram,
  `TwoComplex.TwoManifoldEmbedding M.source 𝔼²` with `IsPlanarMap` is the owner of the planar
  realization, `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` are the owners of the
  `R`-diagram and reducedness hypotheses, `IsBoundaryCycle` is the owner of the outer and inner
  boundary cycles, `boundaryInteriorEdgeCount` and `OneComplex.vertexDegree` are the owner degree
  maps, `BoundaryIntersectionIsConsecutivePart` and `faceBoundarySupport` are the chapter owners
  for the boundary-arc geometry of a boundary region, and `HasLongSymmetrizedRelatorPart` is the
  owner of the “longer than half a relator” condition.
- `bridge/view`: `HasAnnularBoundaryCycles` from Lemma `5-5-1` is the chapter owner for the
  annular boundary decomposition, `Quiver.Path.CyclicPath.HasPart` is the owner predicate for a
  consecutive boundary segment, and the source boundary arc `σ₁ = ∂D ∩ σ` is represented by a
  total-edge part occurring both on the chosen boundary cycle `σ` and on a boundary cycle of the
  region `D`, with the actual planar intersection recovered as the support of that segment inside
  the canonical boundary support `embedding.boundaryCycleSupport σ`.

Domain sampling:
1. `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` from Definitions `5-1-8` and `5-2-5`
   are the existing owner predicates for a reduced `R`-diagram.
2. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the chapter
   owner for the annular boundary decomposition.
3. `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` and
   `OneComplex.vertexDegree` from Definition `5-2-8` are the chapter owners for
   the source quantities `i(D)` and `d(v)`.
4. `TwoComplex.TwoManifoldEmbedding.BoundaryIntersectionIsConsecutivePart` from
   Definition `5-4-4` is the chapter owner for the consecutive-boundary-arc shape.
5. `TwoComplex.TwoManifoldEmbedding.faceBoundarySupport`,
   `TwoComplex.TwoManifoldEmbedding.boundaryCycleSupport`, and
   `GroupPresentation.HasLongSymmetrizedRelatorPart` from Definition `5-1-1`, Lemma `5-5-1`, and
   Proposition `3-11-2` are the canonical owner/view API for the source intersection
   `∂D ∩ σ` and for the phrase “`> 1 / 2 R`”.

Primitive vs. derived:
- primitive public data: a basis `basis`, relators `R`, a diagram `M`, a planar embedding
  `embedding`, the annular boundary owner `embedding.HasAnnularBoundaryCycles σ τ`, the
  small-cancellation case, reducedness, the `R`-diagram hypothesis, the boundary-arc exclusion
  hypothesis stated on the canonical face-boundary support of a region, and the prohibition on a
  region meeting both boundary cycles;
- derived API: the three theorem-level clauses asserting that no region boundary has all edges
  interior to the ambient map, every region has `i(D) = p / q + 2`, and every interior vertex
  has degree `q`.
-/

private def totalEdgeListLabel (M : GroupDiagram F)
    (segment : List (Quiver.Total M.source.skeleton)) : F :=
  (segment.map fun e ↦ M.label e.hom.1).prod

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {M : GroupDiagram F}

private def totalEdgeSequenceSupport (embedding : TwoManifoldEmbedding M.source 𝔼²)
    (segment : List (Quiver.Total M.source.skeleton)) : Set 𝔼² :=
  sUnion
    (embedding.geometricEdgeSet ''
      { e | e ∈ segment.map M.source.boundaryArrowGeometricEdge })

private def GeometricFaceHasConsecutiveTotalEdgeSequence
    (D : GeometricFace M.source) (segment : List (Quiver.Total M.source.skeleton)) : Prop :=
  ∃ F : M.source.Face,
    (⟦F⟧ : GeometricFace M.source) = D ∧
      ((M.source.boundary F).HasPart segment ∨
        (M.source.boundary F).HasPart (segment.reverse.map Quiver.Total.reverse))

/-- A region has a boundary intersection with the chosen boundary cycle `c` whose label is longer
than half a relator when the canonical face-boundary support of that region meets the chosen
boundary component exactly in the support of a nonempty consecutive shared boundary segment, and
the label of that segment, read along `c`, is longer than half a symmetrized relator from `R*`.
This packages the source phrase
“if `σ₁ = ∂D ∩ σ` is connected, then `φ(σ₁)` is not `> 1 / 2 R`”. -/
def BoundaryCycleIntersectionLongerThanHalfRelator
    (basis : FreeGroupBasis X F) (R : Set F) (embedding : TwoManifoldEmbedding M.source 𝔼²)
    [embedding.IsPlanarMap]
    (c : CyclicPath M.source.skeleton) (D : GeometricFace M.source) : Prop :=
  ∃ segment : List (Quiver.Total M.source.skeleton),
    segment ≠ [] ∧
      embedding.faceBoundarySupport D ∩ embedding.boundaryCycleSupport c =
        embedding.totalEdgeSequenceSupport segment ∧
      GeometricFaceHasConsecutiveTotalEdgeSequence D segment ∧
        c.HasPart segment ∧
          HasLongSymmetrizedRelatorPart (basis.repr '' R)
            (basis.repr (totalEdgeListLabel M segment)).toWord

/-- A region meets both chosen boundary cycles when its combinatorial boundary contains one
geometric edge lying on `σ` and another geometric edge lying on `τ`. This is the owner-side form
of source hypothesis (C). -/
def RegionMeetsBothBoundaryCycles
    (σ τ : CyclicPath M.source.skeleton) (D : GeometricFace M.source) : Prop :=
  (∃ e : OneComplex.GeometricEdge M.source.skeleton,
      e ∈ M.source.boundaryGeometricEdges D ∧ σ.SupportsGeometricEdge e) ∧
    ∃ e : OneComplex.GeometricEdge M.source.skeleton,
      e ∈ M.source.boundaryGeometricEdges D ∧ τ.SupportsGeometricEdge e

variable (basis : FreeGroupBasis X F) (R : Set F)
variable (embedding : TwoManifoldEmbedding M.source 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: apply the boundary-arc exclusion hypotheses to rule out regions whose boundary
-- misses the ambient boundary or meets one boundary component in more than one arc, then pass to
-- the simply connected discs obtained by cutting the annular map along boundary regions and apply
-- the curvature estimate from Theorem `5-4-5` in the two allowed small-cancellation cases. The
-- resulting nonpositive defect sums force every region to meet the boundary, give the uniform
-- value `i(D) = p / q + 2`, and force every interior vertex to have degree exactly `q`.
/-- Theorem 5-5-3: for a reduced annular `R`-diagram whose outer and inner boundary cycles satisfy
the source boundary-arc hypotheses and whose regions do not meet both boundary components, the two
small-cancellation cases `C'(1 / 6)` with `(q, p) = (3, 6)` and
`C'(1 / 4)` together with `T(4)` and `(q, p) = (4, 4)` force the annular structure conclusions
that no region boundary has all its edges interior to the ambient map, every region has
`i(D) = p / q + 2`, and every interior vertex has degree `q`. -/
theorem suitable_annular_r_diagram_has_uniform_region_and_vertex_structure
    (σ τ : CyclicPath M.source.skeleton) (p q : ℕ)
    (hcase :
      ((q, p) = (3, 6) ∧ C'((1 / 6 : ℝ))[basis, R]) ∨
        ((q, p) = (4, 4) ∧ C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
    (hRDiagram : M.IsRDiagram R) (hReduced : M.IsReduced)
    (hannular : embedding.HasAnnularBoundaryCycles σ τ)
    (houter :
      ∀ D : GeometricFace M.source,
        ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R σ D)
    (hinner :
      ∀ D : GeometricFace M.source,
        ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R τ D)
    (hseparate :
      ∀ D : GeometricFace M.source, ¬ RegionMeetsBothBoundaryCycles σ τ D) :
    (∀ D : GeometricFace M.source,
      ¬ M.source.boundaryGeometricEdges D ⊆
        { e : OneComplex.GeometricEdge M.source.skeleton | embedding.IsInteriorEdge e }) ∧
      (∀ D : GeometricFace M.source,
        (embedding.boundaryInteriorEdgeCount D : ℚ) = (p : ℚ) / q + 2) ∧
        (let S := M.source.skeleton
        let _ : Finite S.Edge := finite_orientedEdge embedding
        ∀ v : S,
          embedding.IsInteriorVertex v →
            S.vertexDegree v = q) :=
              sorry

end

end TwoManifoldEmbedding
end TwoComplex

end
