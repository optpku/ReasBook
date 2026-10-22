/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_7

universe u v w

open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-!
Primary domain: Fuchsian complexes, invariant angle measures, and the curvature formula attached
to a strictly quadratic power presentation of an `F`-group.

Layer triage:
- `source-facing`: a chosen presentation `G = (X; R)` with relators `R = {s ^ m(s) : s ∈ S}`,
  a Fuchsian complex for `G`, and the boundary curvature of the faces of that complex.
- `core/canonical`: `PresentedGroup` is the owner for the chosen presentation,
  `IsStrictlyQuadraticSet` is the chapter owner for the strictly quadratic root family,
  and `FuchsianComplex.AngleMeasure.IsInvariant` from Proposition `3-7-7` is the owner predicate
  for invariant angle measures.
- `bridge/view`: `FGroupPowerPresentation` packages the exact power-presentation data used in the
  proposition, while `FuchsianComplex.FaceBoundaryGeometry` supplies the face type and the
  curvature of face boundaries on top of the existing `FuchsianComplex` owner.

Domain sampling:
1. `PresentedGroup R` from the chapter presentation API is the canonical owner for a concrete
   group presentation.
2. `IsStrictlyQuadraticSet` from Chapter `1` is the existing owner predicate for the hypothesis
   that the relator roots form a strictly quadratic family.
3. `TwoComplex.BoundaryStar` gives the face-corner carrier used in Proposition `3-7-7` for the
   minimal-angle type of a Fuchsian complex.

Primitive vs. derived:
- primitive public data: the generator type `X`, the finite root family `S`, the multiplicity
  function `m`, the identification of `G` with the presented group on relators `s ^ m(s)`, the
  Fuchsian complex `K`, and the face-boundary curvature operation on `K`;
- derived API: the curvature identity itself for invariant angle measures.
-/

variable {G : Type u} [Group G]

/-- A chosen power presentation of `G` records a finite generator type `X`, a strictly quadratic
root family `S`, and the multiplicity function whose powers present `G`. -/
structure FGroupPowerPresentation (G : Type u) [Group G] where
  /-- The generator type of the presentation. -/
  X : Type v
  /-- The generator type is finite. -/
  finite_generators : Finite X
  /-- The finite root family whose powers give the relators. -/
  S : Finset (FreeGroup X)
  /-- The multiplicity attached to each root word. -/
  multiplicity : FreeGroup X → ℕ+
  /-- The relator family `R = {s ^ m(s) : s ∈ S}` presents `G`. -/
  presentationEquiv :
    PresentedGroup
        (Set.image (fun s : FreeGroup X ↦ s ^ (multiplicity s : ℕ)) (↑S : Set (FreeGroup X))) ≃* G
  /-- The root family is strictly quadratic over the generator set. -/
  strictlyQuadratic : IsStrictlyQuadraticSet S

attribute [instance] FGroupPowerPresentation.finite_generators

namespace FuchsianComplex

/-- Face-boundary geometry on a Fuchsian complex records the face type together with the curvature
of the boundary of each face for any chosen angle measure. -/
structure FaceBoundaryGeometry (K : FuchsianComplex G) where
  /-- The type of faces of the chosen Fuchsian complex. -/
  Face : Type w
  /-- The curvature of the boundary of a face with respect to a chosen angle measure. -/
  boundaryCurvature : AngleMeasure K → Face → ℝ

/-- Proposition 3-7-8: for a Fuchsian complex attached to a strictly quadratic power presentation,
the curvature of the boundary of any face with respect to an invariant angle measure is
`2π (|X| - ∑_{s ∈ S} 1 / m(s))`. -/
-- Proof sketch: by invariance it suffices to compute the face dual to the identity vertex of the
-- presentation complex. Decompose that face using the common barycentric subdivision, sum the
-- local contributions `π - α(D, g)` over the conjugates of each relator `s ^ {m(s)}`, and use the
-- strict quadraticity identity `∑ |s| = 2 |X|` to simplify the result.
theorem boundaryCurvature_eq_two_pi_mul_card_generators_sub_sum_reciprocal_multiplicity
    (P : FGroupPowerPresentation G) (K : FuchsianComplex G) (Γ : FaceBoundaryGeometry K)
    (α : AngleMeasure K) (hα : α.IsInvariant) (Δ : Γ.Face) :
    Γ.boundaryCurvature α Δ =
      2 * Real.pi *
        ((Nat.card P.X : ℝ) -
          P.S.sum (fun s ↦ (1 : ℝ) / ((P.multiplicity s : ℕ) : ℝ))) := sorry

end FuchsianComplex
