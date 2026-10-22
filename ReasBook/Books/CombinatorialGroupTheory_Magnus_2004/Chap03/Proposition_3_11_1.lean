/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_10_1

-- Declarations for this item are recorded in this dedicated item file.

universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: asphericity of Cayley complexes attached to staggered relator families with a
distinguished ordered generator subset.

Layer triage:
- `source-facing`: the distinguished generator subset `X₀`, the indexed relator family `r`, and
  the staggeredness hypothesis `GroupPresentation.IsStaggeredPresentation X₀ r`.
- `core/canonical`: `CayleyComplex.Coordinates C (PresentedGroup.of : X → PresentedGroup (Set.range r))
  ↥(Set.range r)` is the chosen Cayley-model owner, and `CayleyComplex.Coordinates.IsAspherical`
  is the owner conclusion.
- `bridge/view`: Proposition `3-11-1` itself is the bridge from the source-facing staggeredness
  hypothesis to the canonical asphericity owner for the chosen presentation `P`.

Domain sampling:
1. `GroupPresentation.IsStaggeredPresentation` from Proposition `3-9-5` is the chapter owner for
   staggeredness relative to the distinguished subset `X₀`, so the theorem should use it directly
   rather than falling back to the Chapter `2` indexed-generator proxy.
2. `CayleyComplex.Coordinates C (PresentedGroup.of : X → PresentedGroup (Set.range r))
   ↥(Set.range r)` from Proposition `3-4-1` is the owner abstraction for a chosen actual Cayley
   complex of `(X; Set.range r)`.
3. `CayleyComplex.Coordinates.SphericalDiagram`, its reduction API `SphericalDiagram.IsReduced`
   and `SphericalDiagram.ReductionStep`, and the resulting predicate
   `CayleyComplex.Coordinates.IsAspherical` from Definition `3-10-1` are the owner declarations on
   the asphericity side of the proposition.
4. Proposition `3-9-7` supplies the reduced spherical-diagram obstruction that the reduction API
   feeds into in the staggered setting.

Primitive vs. derived:
- primitive data: the distinguished generator subset `X₀`, the indexed relator family `r`, the
  staggeredness witness `hstaggered`, and the chosen standard Cayley presentation `P`;
- derived API: the asphericity conclusion for `P`.
-/

namespace GroupPresentation

section

variable {X : Type u} [LinearOrder X]
variable {J : Type v} [Preorder J]

-- Proof sketch: start with `Δ : CayleyComplex.Coordinates.SphericalDiagram coords` and use the
-- reduction owner from Definition `3-10-1` to delete extremal two-face subdiscs. Once no further
-- reduction is possible, the resulting reduced spherical diagram would contradict Proposition
-- `3-9-7` in the staggered setting. Hence every spherical diagram reduces to the empty one, which
-- is exactly `coords.IsAspherical`.
/-- Proposition 3-11-1: every actual Cayley complex `C(X; Set.range r)` of a staggered
presentation `(X₀; r)` is aspherical. -/
theorem isAspherical_of_staggered_presentation
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C (Set.range r)) :
    CayleyComplex.Coordinates.IsAspherical coords := sorry

end

end GroupPresentation
