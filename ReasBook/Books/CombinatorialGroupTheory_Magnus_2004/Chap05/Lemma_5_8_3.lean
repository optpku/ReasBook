/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_8_1

universe u v

set_option autoImplicit false

namespace Knot

section

/-!
Primary domain: existence of standard and alternating projections of knots.

Layer triage:
- `source-facing`: a knot `K : Knot`, its projections, and the predicates saying that a projection
  is standard or alternating and that `K` itself is alternating.
- `core/canonical`: `Knot` is the owner abstraction for that primitive knot-projection data,
  including the canonical presentation attached to each projection and the canonically attached
  knot group.
- `bridge/view`: `presentation_of_standard_alternating_projection` from Lemma `5-8-1` is the
  downstream bridge from a standard alternating projection to the presentation-theoretic Chapter
  `5` API.

Domain sampling:
1. `Knot` from Lemma `5-8-1` is the source-facing owner for a knot, its projections, and the
   canonical presentation attached to each projection.
2. `K.Projection` is the owner type for the projections of `K`.
3. `K.IsStandardProjection`, `K.IsAlternatingProjection`, and `K.IsAlternating` are the owner
   predicates for the standard and alternating hypotheses used here.
4. `presentation_of_standard_alternating_projection` from Lemma `5-8-1` is the canonical
   downstream bridge that consumes the data produced by part `(2)` of this lemma.

Primitive vs. derived:
- primitive public data: the knot `K`, its projection type `K.Projection`, and the source-facing
  predicates `K.IsStandardProjection`, `K.IsAlternatingProjection`, and `K.IsAlternating`,
  together with the canonical presentation attached to each projection by the `Knot` owner;
- derived API: the two existence statements of Lemma `5-8-3`.
-/

/-- Lemma 5-8-3 (1): every knot admits a projection that is standard. -/
-- Proof sketch: start from any diagram of the knot and apply the standard normalization process
-- for knot projections to obtain a standard projection representing the same knot.
theorem exists_standard_projection (K : Knot.{u, v}) :
    ∃ P : K.Projection, K.IsStandardProjection P := sorry

/-- Lemma 5-8-3 (2): an alternating knot admits a standard projection that is alternating. -/
-- Proof sketch: begin with an alternating diagram of the knot and run the standardization
-- procedure in a way that preserves the alternating crossing pattern, producing an alternating
-- standard projection.
theorem exists_alternating_standard_projection (K : Knot.{u, v}) (hK : K.IsAlternating) :
    ∃ P : K.Projection, K.IsStandardProjection P ∧ K.IsAlternatingProjection P := sorry

end

end Knot
