/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_3_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: curvature lower bounds for connected simply connected planar `[p, q]` maps.

Layer triage:
- `source-facing`: Corollary `5-3-4`, which lower-bounds the boundary curvature sum of a
  connected simply connected `[p, q]` map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for the planar map itself,
  `TwoComplex.TwoManifoldEmbedding.IsSquareBracketPQMap` is the owner for the `[p, q]` condition,
  `Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)` and
  `TwoComplex.IsSimplyConnected` are the canonical owners for the connected and simply connected
  parts of the textbook hypothesis, and
  `TwoComplex.TwoManifoldEmbedding.basic_formula_3_2_of_planar_map` is the owner formula whose
  boundary term is `boundaryVertexAdjustedDefectSum`.
- `bridge/view`: this corollary specializes the owner formula to the connected simply connected
  case, where the Euler term is `1`, and then uses the `[p, q]` lower bounds to control the
  remaining defect sums.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` from Definition `5-1-1` is the ambient owner
   hypothesis for finite planar maps.
2. `positive_integral_reciprocal_sum_eq_half_iff` from Definition `5-3-1` is the chapter-level
   owner for the positive-integral solutions of `1 / p + 1 / q = 1 / 2`, so this corollary
   should keep the positivity hypotheses explicit rather than treating the rational equation over
   `ℕ` as sufficient by itself.
3. `TwoComplex.TwoManifoldEmbedding.IsSquareBracketPQMap` from Definition `5-3-1` is the owner
   abstraction for the textbook `[p, q]` condition.
4. `TwoComplex.TwoManifoldEmbedding.boundaryVertexAdjustedDefectSum` and
  `TwoComplex.TwoManifoldEmbedding.basic_formula_3_2_of_planar_map` from Theorem `5-3-2` are the
  canonical owner API for the curvature formula used here.
5. `Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton)` is the canonical owner for the
   connectedness part of the textbook “simply connected planar map” hypothesis.
6. `TwoComplex.IsSimplyConnected` from Proposition `3-4-2` is the owner abstraction for the
   trivial-`π₁` input that turns the Euler term into `1` once connectedness is also assumed.

Primitive vs. derived:
- primitive public data: a planar embedding `embedding`, the connected and simply connected
  hypotheses, the source-facing `[p, q]` hypothesis, the positivity of `p` and `q`, the
  reciprocal relation on `p` and `q`, and the hypothesis that the map has more than one vertex;
- derived API: the curvature sum `boundaryVertexAdjustedDefectSum p q` and its lower bound.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: apply the basic formula `(3.2)` to the connected simply connected `[p, q]` map,
-- so the Euler term is `1`; then use the `[p, q]` lower bounds to show the interior-vertex and
-- region-defect contributions are nonpositive, and use the “more than one vertex” hypothesis
-- together with the deletion-of-isolated-vertices argument of the text to control the remaining
-- boundary term.
/-- Corollary 5-3-4: the curvature sum `∑_M^• [p / q + 2 - d(v)]` of a connected simply connected
`[p, q]` map with more than one vertex is at least `p`. -/
theorem curvature_formula_lower_bound_of_simplyConnected_squareBracketPQMap
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [IsSimplyConnected C] (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hPQ : embedding Is[p, q])
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hmoreThanOneVertex : (1 : ℚ) < embedding.vertexCount) :
    (p : ℚ) ≤ embedding.boundaryVertexAdjustedDefectSum p q := sorry

end

end TwoManifoldEmbedding
end TwoComplex
