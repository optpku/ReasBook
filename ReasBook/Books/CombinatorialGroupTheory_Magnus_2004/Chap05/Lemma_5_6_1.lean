/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_3_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_3_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature estimates for planar `[p, q]` maps whose connected components are discs
or annuli.

Layer triage:
- `source-facing`: `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents`,
  expressing that the planar map itself admits a finite connected-component decomposition whose
  components are either simply connected or annular in the induced planar embedding.
- `core/canonical`: `TwoComplex.Subcomplex.IsComponentDecomposition` is the owner abstraction for
  the primitive component data, while `TwoComplex.IsSimplyConnected` and
  `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` are the owner predicates for the two
  allowed component shapes.
- `bridge/view`: `TwoComplex.fullSubcomplex` is the intrinsic ambient subcomplex on which the
  component decomposition lives, and `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` is the
  canonical restriction bridge to the induced embedding on each listed component.

Domain sampling:
1. `TwoComplex.Subcomplex.IsComponentDecomposition` from Proposition `3-9-1` is the owner
   abstraction for the finite component decomposition.
2. `TwoComplex.fullSubcomplex` from Definition `5-1-5` is the canonical ambient subcomplex
   carrying all cells of the map, so the whole-map component decomposition should live there
   rather than behind an extra `S`.
3. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1` is the
   canonical restriction bridge for the induced embedding on each listed component.
4. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for the
   simply connected components.
5. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the owner
   predicate for annular boundary components in a planar realization.

Primitive vs. derived:
- primitive public data: the planar embedding `embedding`, positive integers `p` and `q`
  satisfying `1 / p + 1 / q = 1 / 2`, the `[p, q]` hypothesis, and the existence of a finite
  component decomposition of the ambient map whose pieces satisfy one of the two owner
  component-shape hypotheses;
- derived API: the two inequalities `(6.1)` and `(6.2)` bounding boundary edges and boundary
  vertices by the boundary-vertex defect sum.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- A planar map has simply connected-or-annular components when the full carried subcomplex of
the map admits a finite connected-component decomposition whose induced component embeddings have
one of the two allowed shapes. -/
def HasSimplyConnectedOrAnnularComponents
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (components : ι → Subcomplex C)
    (_ : C.fullSubcomplex.IsComponentDecomposition components),
      ∀ i : ι,
        (components i).complex.IsSimplyConnected ∨
          ∃ σ τ : CyclicPath (components i).complex.skeleton,
            (embedding.restrictToSubcomplex (components i)).HasAnnularBoundaryCycles σ τ

-- Proof sketch: rewrite formula `(3.1)` componentwise using the reciprocal relation
-- `1 / p + 1 / q = 1 / 2`, choose the component decomposition supplied by
-- `embedding.HasSimplyConnectedOrAnnularComponents`, and apply the induced component embedding
-- `embedding.restrictToSubcomplex (components i)` on the annular branch. A simply
-- connected component contributes Euler
-- characteristic `1` while an annular component contributes `0`. The `[p, q]` inequalities make
-- the interior-vertex and region-defect terms nonpositive, giving `(6.1)`; then delete isolated
-- boundary vertices and compare the remaining boundary vertices with boundary edges to obtain
-- `(6.2)`.
/-- Lemma 5-6-1: if a `[p, q]` map admits a finite component decomposition in which every
component is either simply connected or annular in the induced restricted embedding, then the
boundary edge-count and boundary vertex-count satisfy formulas `(6.1)` and `(6.2)`. -/
theorem boundary_edge_and_vertex_counts_le_boundaryVertexDefectSum_of_squareBracketPQMap
    (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2) (hPQ : embedding Is[p, q])
    (hcomponents : embedding.HasSimplyConnectedOrAnnularComponents) :
    embedding.boundaryEdgeCount ≤ ((q : ℚ) / p) * embedding.boundaryVertexDefectSum p ∧
      embedding.boundaryVertexCount ≤ ((q : ℚ) / p) * embedding.boundaryVertexDefectSum p := sorry

end

end TwoManifoldEmbedding
end TwoComplex
