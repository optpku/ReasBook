/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_3

universe u v

set_option autoImplicit false

/-- The source-facing knot data used by Section `5.8`: a type of projections, the standard and
alternating predicates on those projections, the ambient alternating-knot predicate, and for each
projection the canonical finite presentation of the attached knot group. -/
structure Knot where
  /-- The type of projections of this knot. -/
  Projection : Type u
  /-- A projection is standard when it has the textbook regularity properties used in Section
  `5.8`. -/
  IsStandardProjection : Projection → Prop
  /-- A projection is alternating when crossings alternate over and under along each component. -/
  IsAlternatingProjection : Projection → Prop
  /-- The ambient knot is alternating. -/
  IsAlternating : Prop
  /-- The canonical knot group attached to this knot. -/
  knotGroup : Type v
  /-- The natural group structure on the knot group. -/
  instGroupKnotGroup : Group knotGroup
  /-- The canonical number of generators in the presentation attached to a projection. -/
  presentationRank : Projection → ℕ
  /-- The canonical relator set in the presentation attached to a projection. -/
  presentationRelators (P : Projection) : Set (FreeGroup (Fin (presentationRank P)))
  /-- The canonical presentation equivalence attached to a projection. -/
  presentationEquiv (P : Projection) :
    PresentedGroup (presentationRelators P) ≃* knotGroup

attribute [instance] Knot.instGroupKnotGroup

noncomputable section

open FreeGroupBasis

namespace Knot

section

/-!
Primary domain: finite small-cancellation presentations coming from standard alternating knot
projections.

Layer triage:
- `source-facing`: a knot `K : Knot`, a chosen projection `P : K.Projection`, and the predicates
  saying that `P` is standard and alternating, together with the canonical presentation data
  already attached to `P`.
- `core/canonical`: `K.presentationRelators P` and `K.presentationEquiv P` reuse the project owner
  `PresentedGroup R ≃* K.knotGroup` for the canonical presentation of the knot group determined by
  `P`, while `C(4)[ofFreeGroup (Fin n), R]` and `T(4)[ofFreeGroup (Fin n), R]` are the Chapter `5`
  owner predicates expressing the small-cancellation conclusion on that relator set.
- `bridge/view`: this file is exactly the bridge from standard/alternating projection hypotheses
  to the Chapter `5` small-cancellation properties of the canonical presentation attached to that
  projection.

Domain sampling:
1. `Knot` in this file is the source-facing owner for a knot, its projections, and the canonical
   presentation attached to each projection.
2. `PresentedGroup R ≃* K.knotGroup` from Definition `2-1-1` is the project's canonical owner for
   a finite presentation of the knot group, and it is recorded here as `K.presentationEquiv P`.
3. `FreeGroupBasis.condition_c`, written `C(4)[FreeGroupBasis.ofFreeGroup (Fin n), R]`, from
   Definition `5-2-2` is the owner predicate for the `C(4)` conclusion.
4. `FreeGroupBasis.condition_t`, written `T(4)[FreeGroupBasis.ofFreeGroup (Fin n), R]`, from
   Definition `5-2-3` is the owner predicate for the `T(4)` conclusion.

Primitive vs. derived:
- primitive public data: the knot `K`, the projection `P : K.Projection`, and the predicates
  `K.IsStandardProjection` and `K.IsAlternatingProjection`, together with the canonical
  projection-attached presentation data `K.presentationRank P`, `K.presentationRelators P`, and
  `K.presentationEquiv P`;
- derived API: finiteness and the canonical `C(4)` and `T(4)` owner predicates for that attached
  relator set.
-/

-- Proof sketch: for a standard alternating projection, its canonical Wirtinger-type presentation
-- is finite. The relators of that canonical presentation have the combinatorial form needed for
-- the Chapter `5` small-cancellation analysis, giving `C(4)` and `T(4)` on the canonical
-- free-group basis.
/-- Lemma 5-8-1: the canonical presentation attached to a standard alternating projection of a
knot is finite and satisfies `C(4)` and `T(4)`. -/
theorem presentation_of_standard_alternating_projection
    (K : Knot.{u, v}) {P : K.Projection} (hP_standard : K.IsStandardProjection P)
    (hP_alternating : K.IsAlternatingProjection P) :
    (K.presentationRelators P).Finite ∧
      C(4)[ofFreeGroup (Fin (K.presentationRank P)), K.presentationRelators P] ∧
      T(4)[ofFreeGroup (Fin (K.presentationRank P)), K.presentationRelators P] := sorry

end

end Knot
