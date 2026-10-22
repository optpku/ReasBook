/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_3_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Corollary_5_3_4

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for connected simply connected planar `(q, p)` maps.

Layer triage:
- `source-facing`: Corollary `5-3-5`, which lower-bounds the boundary-region curvature sum of a
  connected simply connected `(q, p)` map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for the planar map itself,
  `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner for the `(q, p)` condition,
  `TwoComplex.TwoManifoldEmbedding.adjustedInteriorEdgeDefectSum` is the owner construction for the
  curvature sum attached to any selected family of regions, while
  `Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)` and
  `TwoComplex.IsSimplyConnected` are the canonical owners for the connected and simply connected
  parts of the textbook hypothesis, while
  `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` and
  `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` are the owner inputs for the
  boundary-region specialization, and the square-bracket lower-bound corollary from
  `Corollary_5_3_4.lean` is the upstream dual boundary-vertex result.
- `bridge/view`: the textbook sum over boundary regions is realized directly as a finite sum over
  `adjustedInteriorEdgeDefectSum` specialized to the owner predicate `IsBoundaryRegion`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` from
   `Definition_5_3_1.lean`
   is the chapter owner for `(q, p)` maps.
2. `TwoComplex.TwoManifoldEmbedding.IsBoundaryRegion` from
   `Definition_5_2_7.lean`
   is the owner predicate selecting the boundary regions.
3. `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` from
   `Definition_5_2_8.lean`
   is the owner map for the source quantity `i(D)`.
4. `TwoComplex.TwoManifoldEmbedding.adjustedInteriorEdgeDefectSum` from
   `Theorem_5_3_2.lean`
   is the canonical owner for the selected-region curvature sum, so this file should keep only
   the boundary-region specialization rather than a second local owner.

Primitive vs. derived:
- primitive public data: a planar embedding `embedding`, the connected and simply connected
  hypotheses, the source-facing `(q, p)` hypothesis, the positivity of `p` and `q`, the
  reciprocal relation on `p` and `q`, and the hypothesis that the map has more than one region;
- derived API: the boundary-region curvature sum built from `IsBoundaryRegion` and
  `boundaryInteriorEdgeCount`, and its lower bound.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

/-- The curvature sum `∑_M^• [p / q + 2 - i(D)]` over the boundary regions of a planar map. -/
abbrev boundaryRegionAdjustedInteriorEdgeDefectSum (p q : ℚ) : ℚ :=
  embedding.adjustedInteriorEdgeDefectSum embedding.IsBoundaryRegion p q

/-- Source-facing notation for the textbook quantity `σ'(M)`. -/
syntax:max "σ'(" term:max ")[" term:max ", " term:max "]" : term

macro_rules
  | `(σ'($embedding)[$p, $q]) =>
      `(TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum
        $embedding $p $q)

-- Proof sketch: pass to the dual planar map, which is a connected simply connected `[p, q]` map
-- with more than one vertex. Boundary regions of `embedding` correspond to boundary vertices of
-- the dual, and the degree of the dual vertex corresponding to `D` is `i(D)`; then apply
-- Corollary `5-3-4` to the dual map.
/-- Corollary 5-3-5: the curvature sum `∑_M^• [p / q + 2 - i(D)]` over the boundary regions of a
connected simply connected `(q, p)` map with more than one region is at least `p`. -/
theorem curvature_formula_lower_bound_of_simplyConnected_roundBracketQPMap
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [IsSimplyConnected C] (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hQP : embedding Is(q, p))
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hmoreThanOneRegion : (1 : ℚ) < embedding.regionCount) :
    (p : ℚ) ≤ σ'(embedding)[p, q] := sorry

end

end TwoManifoldEmbedding
end TwoComplex
