/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_5

universe u v w z

set_option autoImplicit false

noncomputable section

open Quiver.Path
open GroupPresentation

/-!
Primary domain: combinatorial group theory of staggered presentations and disc diagrams over a
presentation complex.

Layer triage:
- `source-facing`: a staggered presentation relative to a distinguished ordered subset `X₀ ⊆ X`,
  an actual presentation complex `K(X; R)` realized by
  `PresentationComplex.Coordinates K X R`, a singular disc `S : TwoComplex.Subcomplex C`, a
  diagram `φ : S.complex → K`, and a boundary loop `p` whose cyclic path is the boundary data in
  `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`.
- `core/canonical`: `GroupPresentation.IsStaggeredPresentation` is the chapter owner for the
  staggered-presentation hypothesis, `PresentationComplex.Coordinates` is the owner for the actual
  presentation complex, `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the
  chapter owner for disc diagrams together with explicit boundary cycle data, `TwoComplex.Hom` is
  the owner for the diagram map, and `basisLetterOccurs` is the chapter owner for the source
  phrase “the generator `x` occurs in the boundary word”.
- `bridge/view`: the source-facing loop `p` is tied to the diagram boundary through the owner
  predicate `TwoComplex.Subcomplex.IsSingularDisc`.

Domain sampling:
1. `GroupPresentation.IsStaggeredPresentation` from Proposition `3-9-5` is the existing chapter
   owner for staggeredness.
2. `PresentationComplex.Coordinates` from Proposition `3-4-3` is the owner abstraction for the
   presentation complex attached to a relator set, so this file should speak directly about
   `K(X; R)` rather than an unrelated `TwoComplex`.
3. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for the
   singular-disc source together with its explicit boundary cycle.
4. `TwoComplex.Hom` from Proposition `3-3-4` is the owner abstraction for a combinatorial diagram
   map into that presentation complex.
5. `basisLetterOccurs` from Proposition `1-7-4` is the chapter owner for the source phrase
   “the generator `x` occurs”.
6. `CayleyComplex.Coordinates.pathLabel` and `boundaryLabel` from Proposition `3-5-9` give the
   established owner pattern for reading a signed word from a loop.

Primitive vs. derived:
- primitive data: the distinguished subset `X₀`, the relator family `r`, the presentation-complex
  coordinates `coords : PresentationComplex.Coordinates K X (Set.range r)`, the singular disc
  `S : TwoComplex.Subcomplex C`, the morphism `φ : S.complex → K`, and the boundary loop `p`
  recorded in `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`;
- derived API: which generators of `X` occur on presentation-complex edges, and the boundary word
  read from a chosen loop after applying the diagram map.
-/

namespace PresentationComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {K : TwoComplex.{v}}

variable {D : TwoComplex.{v}}

/-- The generators occurring in a diagram over the presentation complex are the generators
appearing on the images of its oriented edges. -/
def occurringGenerators (coords : Coordinates K X R)
    (φ : TwoComplex.Hom D K) : Set X :=
  { x | ∃ e : D.skeleton.Edge, (coords.edgeEquiv (φ.toEdge e)).1 = x }

/-- The signed-generator word read along a path in the source `1`-skeleton after applying the
diagram map to the presentation complex. -/
def pathLabel (coords : Coordinates K X R) (φ : TwoComplex.Hom D K) {a b : D.skeleton} :
    Quiver.Path a b → List (SignedLetter X)
  | .nil => []
  | .cons p e => pathLabel coords φ p ++ [coords.edgeEquiv (φ.toEdge e.1)]

/-- The signed-generator boundary word read from a loop in the source `1`-skeleton after applying
the diagram map. -/
def boundaryLabel (coords : Coordinates K X R)
    (φ : TwoComplex.Hom D K) (p : Loop D.skeleton) : List (SignedLetter X) :=
  pathLabel coords φ p.2

section Proposition396

variable [LinearOrder X]
variable {J : Type z} [Preorder J]
local notation "basis" => FreeGroupBasis.ofFreeGroup X

-- Proof sketch: the staggered ordering and the disc-diagram topology force an extremal
-- distinguished face to survive on the outer boundary. The chapter owner
-- `TwoComplex.Subcomplex.IsSingularDisc` packages the source disc together with the fact that the
-- chosen loop `p` carries its boundary cycle. Reading the resulting boundary word through
-- `coords.boundaryLabel φ p`, the extremal generator therefore occurs in that canonical word.
/-- Proposition 3-9-6: let `coords : PresentationComplex.Coordinates K X (Set.range r)` realize
the presentation complex of a staggered relator family `r`, let `S` be a singular disc, let
`φ : S.complex → K` be a diagram over that complex, and let `p` be a loop carrying the boundary
cycle of `S`. If `x` is either the greatest or the least distinguished generator from `X₀`
occurring on the edges of `S.complex`, then `x` already occurs in the boundary word read from
`p`. -/
theorem basisLetterOccurs_boundaryLabel_of_isGreatest_or_isLeast
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    {C : TwoComplex.{v}} (S : TwoComplex.Subcomplex C)
    {K : TwoComplex.{v}} (coords : Coordinates K X (Set.range r))
    (φ : TwoComplex.Hom S.complex K) (p : Loop S.skeleton.toOneComplex)
    (hS : TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)) {x : X}
    (hx : IsGreatest (X₀ ∩ coords.occurringGenerators φ) x ∨
      IsLeast (X₀ ∩ coords.occurringGenerators φ) x) :
    basisLetterOccurs basis x (FreeGroup.mk (coords.boundaryLabel φ p)) := sorry

end Proposition396

end PresentationComplex.Coordinates
