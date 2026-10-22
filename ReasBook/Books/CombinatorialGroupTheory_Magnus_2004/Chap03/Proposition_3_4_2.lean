/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Primary domain: the standard Cayley complex attached to a presentation.

Layer triage:
- `source-facing`: an actual `TwoComplex` equipped with the standard Cayley coordinates over the
  presented group `PresentedGroup R`, together with the claim that this Cayley complex is simply
  connected.
- `core/canonical`: `CayleyComplex.Coordinates` is the chapter owner for the Cayley-complex
  realization data, `TwoComplex.IsSimplyConnected` is the owner for simple connectedness of a
  `2`-complex, and `TwoComplex.fundamentalGroup`, written `π(C, v)`, is the owner for the based
  fundamental group.
- `bridge/view`: the pointwise statement `g = 1` is the derived companion of the owner-level
  simply-connectedness statement.

Primitive data vs. derived API:
- primitive data: the actual `TwoComplex` and its Cayley-coordinate realization over
  `PresentedGroup R`;
- derived API: the simple connectedness property and the triviality of each based fundamental
  group.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the chapter owner for realizing an
   actual `TwoComplex` as a Cayley complex with specified coordinates and left translations.
2. `TwoComplex.fundamentalGroup`, written `π(C, v)`, from Definition `3-2-8` is the owner for
   the based fundamental group.
3. `Subsingleton` is the canonical fiberwise consequence of simple connectedness at a basepoint.
-/

namespace TwoComplex

/-- A `2`-complex is simply connected when every based fundamental group is trivial. -/
class IsSimplyConnected (C : TwoComplex) : Prop where
  /-- Every based fundamental group of `C` is a subsingleton. -/
  fundamentalGroup_subsingleton (v : C.skeleton) : Subsingleton (π(C, v))

variable {C : TwoComplex}

instance (v : C.skeleton) [hC : IsSimplyConnected C] : Subsingleton (π(C, v)) :=
  hC.fundamentalGroup_subsingleton v

/-- In a simply connected `2`-complex, every based loop class is trivial. -/
theorem fundamentalGroup_eq_one [IsSimplyConnected C] (v : C.skeleton) (g : π(C, v)) : g = 1 :=
  Subsingleton.elim g 1

end TwoComplex

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Proposition 3-4-2: a `2`-complex equipped with the standard Cayley coordinates over
`PresentedGroup R` is simply connected. -/
-- Proof sketch: the standard Cayley-complex argument contracts every loop to the empty loop by
-- reducing its label in the free group to the normal closure of the relators and then filling the
-- resulting null-homotopy with the attached `2`-cells.
theorem isSimplyConnected
    (coords : PresentationCoordinates C R) :
    TwoComplex.IsSimplyConnected C := sorry

end CayleyComplex.Coordinates
