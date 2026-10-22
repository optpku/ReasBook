/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_7
import CombinatorialGroupTheory_Magnus_2004.Chap05.Corollary_5_7_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_5_1

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

open Quiver.Path
open OneComplex

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: annular planar maps after removing the boundary layer.

Layer triage:
- `source-facing`: an annular planar map `A`, the boundary-layer peeling construction producing
  `H`, and the exclusion of boundary linking pairs.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` is the owner of the planar map,
  `TwoManifoldEmbedding.HasAnnularBoundaryCycles` is the owner of annularity, and
  `TwoManifoldEmbedding.IsInteriorRegion` is the owner predicate for the faces remaining after the
  boundary layer is removed.
- `bridge/view`: `Subcomplex.IsBoundaryLayerComplement` is the existing chapter bridge for the
  chosen surviving subcomplex after deleting a boundary layer, `TwoManifoldEmbedding
  .restrictToSubcomplex` is the owner-side bridge to the induced embedding on that carried
  subcomplex, and `Subcomplex.ContainsGeometricFace`,
  `OneComplex.Subcomplex.ContainsGeometricEdge`, `TwoComplex.boundaryGeometricEdges`, and
  `TwoComplex.VertexOnFace` describe the extra gap-removal incidence conditions on the surviving
  `1`-skeleton. `TwoManifoldEmbedding.boundaryCycleSupport` and
  `TwoManifoldEmbedding.faceBoundarySupport` compare boundary regions with the chosen outer and
  inner boundary cycles.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the chapter
   owner for annular boundary data.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` and `IsInteriorRegion` from Definition `5-2-7`
   are the chapter owners for the boundary/interior face partition.
3. `TwoComplex.Subcomplex.IsBoundaryLayerComplement` from Corollary `5-7-3` is the existing
   chapter bridge for the chosen carried complement of the boundary layer, so the extra
   gap-removal content here should refine that owner rather than introduce a second
   embedding-owned predicate.
4. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1`, together with
   `Subcomplex.ContainsGeometricFace`, `OneComplex.Subcomplex.ContainsGeometricEdge`,
   `TwoComplex.boundaryGeometricEdges`, and `TwoComplex.VertexOnFace`, gives the canonical
   induced-subcomplex and incidence API for the peeled annular map.

Primitive vs. derived:
- primitive public data: the annular embedding, its chosen outer and inner boundary cycles, a
  chosen surviving subcomplex extending `Subcomplex.IsBoundaryLayerComplement` by the extra
  face-incidence conditions recording gap removal, and the boundary-linking-pair exclusion;
- derived API: annularity and region nonemptiness for the canonical restricted embedding of the
  peeled subcomplex.
-/

namespace TwoComplex
namespace Subcomplex

section

variable {C : TwoComplex}

/-- A chosen carried subcomplex is obtained by removing the boundary layer and its gaps when it is
already the chapter's canonical boundary-layer complement and its surviving geometric edges and
vertices are exactly those incident with the surviving faces. -/
def IsBoundaryLayerGapRemoval (H : Subcomplex C) (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  H.IsBoundaryLayerComplement embedding ∧
    (∀ e : GeometricEdge C.skeleton,
      H.skeleton.ContainsGeometricEdge e ↔
        ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ e ∈ C.boundaryGeometricEdges ⟦D⟧) ∧
      ∀ v : C.skeleton,
        v ∈ H.skeleton.vertexSet ↔
          ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ C.VertexOnFace v D

namespace IsBoundaryLayerGapRemoval

theorem toIsBoundaryLayerComplement
    {H : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hH : H.IsBoundaryLayerGapRemoval embedding) :
    H.IsBoundaryLayerComplement embedding :=
  hH.1

theorem mem_geometricEdge_iff
    {H : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hH : H.IsBoundaryLayerGapRemoval embedding) (e : GeometricEdge C.skeleton) :
    H.skeleton.ContainsGeometricEdge e ↔
      ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ e ∈ C.boundaryGeometricEdges ⟦D⟧ := by
  rcases hH with ⟨_, hedge, _⟩
  exact hedge e

theorem mem_vertexSet_iff
    {H : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hH : H.IsBoundaryLayerGapRemoval embedding) (v : C.skeleton) :
    v ∈ H.skeleton.vertexSet ↔
      ∃ D : C.Face, H.ContainsGeometricFace ⟦D⟧ ∧ C.VertexOnFace v D := by
  rcases hH with ⟨_, _, hvertex⟩
  exact hvertex v

end IsBoundaryLayerGapRemoval

end

end Subcomplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- A boundary linking pair is a pair of boundary regions on opposite annular boundary components
whose boundary supports meet. This includes the degenerate case `D₁ = D₂`, corresponding to a
single region meeting both boundary components. -/
def IsBoundaryLinkingPair (embedding : TwoManifoldEmbedding C 𝔼²)
    (σ τ : CyclicPath C.skeleton) (D₁ D₂ : GeometricFace C) : Prop :=
  let onOuterBoundary (D : GeometricFace C) :=
    (embedding.faceBoundarySupport D ∩ embedding.boundaryCycleSupport σ).Nonempty
  let onInnerBoundary (D : GeometricFace C) :=
    (embedding.faceBoundarySupport D ∩ embedding.boundaryCycleSupport τ).Nonempty
  ((onOuterBoundary D₁ ∧ onInnerBoundary D₂) ∨
      (onInnerBoundary D₁ ∧ onOuterBoundary D₂)) ∧
    (embedding.faceBoundarySupport D₁ ∩ embedding.faceBoundarySupport D₂).Nonempty

-- Proof sketch: the no-linking-pair hypothesis separates the deleted boundary layer into an outer
-- shell and an inner shell, so deleting the boundary regions leaves a connected annular middle
-- submap. The restricted planar embedding of that induced interior-face subcomplex then carries
-- two disjoint boundary cycles, and at least one region survives because the peeled annulus
-- cannot collapse completely under the stated hypothesis.
/-- Lemma 5-7-5: if `A` is an annular planar map, `H` is the subcomplex obtained from `A` by
removing the boundary layer and its gaps, and `A` has no boundary linking pairs, then the induced
restricted embedding of `H.complex` is again annular and has at least one region. -/
theorem boundaryLayerGapRemoval_has_annularRealizationWithRegion_of_no_boundaryLinkingPairs
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (σ τ : CyclicPath C.skeleton) (hannular : embedding.HasAnnularBoundaryCycles σ τ)
    (H : Subcomplex C) (hH : H.IsBoundaryLayerGapRemoval embedding)
    (hnoLink :
      ∀ D₁ D₂ : GeometricFace C, ¬ embedding.IsBoundaryLinkingPair σ τ D₁ D₂) :
    ∃ σH τH : CyclicPath H.complex.skeleton,
      (embedding.restrictToSubcomplex H).HasAnnularBoundaryCycles σH τH ∧
        Nonempty (GeometricFace H.complex) := sorry

end

end TwoManifoldEmbedding
end TwoComplex
