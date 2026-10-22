/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_9
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_1

universe u

open Quiver.Path
open CayleyComplex.Coordinates
open TwoComplex.Subcomplex

set_option autoImplicit false

/-
Layer triage:
- `source-facing`: a reduced boundary word in the normal closure of the relators of a
  presentation, and a genuine singular disc carried by a relator-filled Cayley `2`-complex whose
  boundary label is that word.
- `core/canonical`: `FreeGroup.IsReduced` and `Subgroup.normalClosure` are the owner predicates
  for the reduced-word and normal-closure hypotheses, `CayleyComplex.Coordinates` is the chapter
  owner for an actual Cayley `2`-complex with relator faces, `TwoComplex.Subcomplex` is the owner
  for a carried van Kampen diagram inside that ambient complex,
  `TwoComplex.Subcomplex.IsSingularDisc` is the chapter owner for the source-side disc geometry
  together with its explicit boundary cycle, and `PresentationCoordinates.boundaryLabel` is the
  owner map reading the signed boundary word of an actual Cayley loop.
- `bridge/view`: `PresentationCoordinates.fromIntrinsicCayley` is the canonical sign-sensitive
  map from the intrinsic Cayley graph to the chosen actual Cayley `1`-skeleton, while
  `PresentationCoordinates.boundaryLabel_fromIntrinsicCayley_mapLoop` is the comparison lemma
  relating intrinsic and actual boundary-word readings.

Domain sampling:
1. `FreeGroup.IsReduced` is mathlib's owner predicate for reduced signed words.
2. `Subgroup.normalClosure` is the canonical owner for the normal closure of the relator set.
3. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the chapter owner for an actual
   Cayley `2`-complex whose oriented faces are indexed by relators.
4. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner for a carried singular diagram
   inside that ambient `2`-complex.
5. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for
   disc-like singular diagrams with an explicit boundary cycle.
6. `PresentationCoordinates.boundaryLabel` from Proposition `3-5-9` is the owner map for reading
   signed words on the actual Cayley skeleton, while
   `PresentationCoordinates.fromIntrinsicCayley` and
   `PresentationCoordinates.boundaryLabel_fromIntrinsicCayley_mapLoop` are the comparison
   bridge/view API relating that direct reading to the intrinsic Cayley graph.
7. `GroupPresentation.cayleyOneComplex R` and `GroupPresentation.cayleyPathLabel R` from Lemma
   `3-5-7` remain the intrinsic owner API for signed boundary words.

Primitive vs. derived:
- primitive data: the relator set `R`, the reduced signed word `w`, an ambient `2`-complex `C`
  equipped with actual Cayley coordinates, a singular disc `S : TwoComplex.Subcomplex C`, and a
  boundary loop `p` whose cyclic path is the explicit boundary cycle in the owner predicate
  `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`;
- derived API: the canonical bridge from intrinsic Cayley loops to actual Cayley loops and the
  direct equality `boundaryLabel coords ... = w` expressing that the ambient boundary loop reads
  the word `w`.
-/

namespace GroupPresentation

variable {X : Type u}

/-- Proposition 3-9-2: if a reduced word `w` represents an element of the normal closure of the
relators `R`, then there is a simple singular disc carried by an actual Cayley `2`-complex for
`(X; R)` whose boundary label, read in the chosen Cayley coordinates, is exactly `w`. -/
-- Proof sketch: write the normal-closure element as a product of conjugates of relators and
-- inverse relators, build the corresponding bouquet of singular relator discs in the Cayley
-- diagram, and then apply sewing-up and detachment until the remaining boundary word is the
-- given reduced word `w`.
theorem exists_cayleySingularDisc_of_reduced_mem_normalClosure
    (R : Set (FreeGroup X)) (w : List (SignedLetter X))
    (hw_reduced : FreeGroup.IsReduced w)
    (hw_normal : FreeGroup.mk w ∈ Subgroup.normalClosure R) :
    ∃ (C : TwoComplex) (coords : PresentationCoordinates C R)
      (S : TwoComplex.Subcomplex C) (p : Loop S.skeleton.toOneComplex),
      S.IsSingularDisc (cyclicPath p) ∧
        boundaryLabel coords (S.skeleton.inclusion.mapLoop p) = w := sorry

end GroupPresentation
