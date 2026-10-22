/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_6_1

universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for planar `[p, q]` maps with disc-or-annulus component
decompositions.

Layer triage:
- `source-facing`: `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents`,
  expressing that the planar map itself admits a finite connected-component decomposition whose
  pieces are either simply connected or annular in the induced planar embedding.
- `core/canonical`: `TwoComplex.Subcomplex.IsComponentDecomposition` is the owner abstraction for
  the primitive component data, while `TwoComplex.IsSimplyConnected`,
  `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles`, and
  `TwoComplex.TwoManifoldEmbedding.boundaryVertexAdjustedDefectSum` are the owner predicates and
  construction used by the theorem.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1`
  is the owner restriction bridge to the induced embedding on each listed component.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents` from Lemma `5-6-1`
   is the source-facing owner for the finite disc-or-annulus component hypothesis.
2. `TwoComplex.Subcomplex.IsComponentDecomposition` from Proposition `3-9-1` is the owner
   abstraction for the finite component decomposition.
3. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from Definition `5-1-1` is the owner
   restriction bridge to a component embedding.
4. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner predicate for the simply
   connected branch.
5. `TwoComplex.TwoManifoldEmbedding.HasAnnularBoundaryCycles` from Lemma `5-5-1` is the owner
   predicate for the annular branch.
6. `TwoComplex.TwoManifoldEmbedding.boundaryVertexAdjustedDefectSum` from Theorem `5-3-2` is the
   owner construction for the boundary curvature sum in the conclusion.

Primitive vs. derived:
- primitive public data: the planar embedding `embedding`, positive integers `p` and `q`
  satisfying `1 / p + 1 / q = 1 / 2`, the `[p, q]` hypothesis, and the existence of a finite
  component decomposition of the ambient map whose pieces satisfy one of the two owner
  component-shape
  hypotheses;
- derived API: the lower bound `0 ≤ embedding.boundaryVertexAdjustedDefectSum p q`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: choose the component decomposition from
-- `embedding.HasSimplyConnectedOrAnnularComponents`. Apply the simply connected
-- boundary-curvature estimate to each disc component and the annular analogue to each annular
-- component via the owner restricted embedding `embedding.restrictToSubcomplex (components i)`.
-- Summing the componentwise inequalities gives a nonnegative total boundary curvature sum for the
-- whole map.
/-- Lemma 5-7-1: if a `[p, q]` map admits a finite connected-component decomposition in which each
component is either simply connected or annular in the induced restricted embedding, then the
curvature sum `∑_M [p / q + 2 - d(v)]`, represented here by
`boundaryVertexAdjustedDefectSum p q`, is nonnegative. -/
theorem boundaryVertexAdjustedDefectSum_nonnegative_of_hasSimplyConnectedOrAnnularComponents
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2) (hPQ : embedding Is[p, q])
    (hcomponents : embedding.HasSimplyConnectedOrAnnularComponents) :
    0 ≤ embedding.boundaryVertexAdjustedDefectSum p q := sorry

end

end TwoManifoldEmbedding
end TwoComplex
