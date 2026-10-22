/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_3_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_10_1

universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: aspherical presentations, relation modules, and low-degree group resolutions.

Layer triage:
- `source-facing`: an aspherical presentation `(X; R)` with no relator a proper power, and the
  resulting freeness of the relation module `N / [N, N]`.
- `core/canonical`: `CayleyComplex.Coordinates.IsAspherical` is the chapter owner for
  asphericity, `Subgroup.normalClosure R` is the owner for the relator subgroup `N`,
  `quotientGroupRingRight N` is the owner ring for right `ℤG`-modules, and
  `relationIdealQuotient N` from Proposition `2-3-2` is the owner realization of the relation
  module.
- `bridge/view`: the textbook phrase “the relation module `N / [N, N]` is a free `G`-module” is
  expressed directly by `Module.Free (quotientGroupRingRight N) (relationIdealQuotient N)`.

Domain sampling:
1. `CayleyComplex.Coordinates.IsAspherical` from Definition `3-10-1` is the owner asphericity
   predicate for the chosen actual Cayley complex.
2. `Subgroup.normalClosure R` is the canonical owner for the normal closure `N` of the relators.
3. `relationIdealQuotient N` from Proposition `2-3-2` is the chapter owner for the relation
   module attached to the presentation.
4. `Module.Free` is mathlib's owner predicate for “is a free module”.

Primitive vs. derived:
- primitive data: the relator set `R`, the chosen standard Cayley presentation `P`, and the
  relator-side hypothesis that no element of `R` is a proper power;
- derived API: freeness of the canonical relation-module owner `relationIdealQuotient
  (Subgroup.normalClosure R)`.
-/

namespace GroupPresentation

variable {X : Type u} {R : Set (FreeGroup X)}

local notation "N" => Subgroup.normalClosure R
local notation "S" => quotientGroupRingRight N

/-- Corollary 3-10-5: if `G = (X; R)` is aspherical and no relator is a proper power, then the
relation module is a free `G`-module. -/
-- Proof sketch: in the current chapter API, Proposition `2-3-2` already packages the relation
-- module `relationIdealQuotient N` as one of the free terms in the canonical low-degree Fox
-- resolution over `quotientGroupRingRight N`. This corollary is therefore a direct source-facing
-- specialization of that owner theorem.
theorem relationIdealQuotient_free_of_isAspherical_of_relators_not_properPower
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (_ : CayleyComplex.Coordinates.IsAspherical coords)
    (_ : ∀ r ∈ R, ¬ IsProperPower r) :
    Module.Free S (relationIdealQuotient N) := by
  let hres := relation_ideal_free_resolution N
  rcases hres with ⟨_, _, hfree, _, _⟩
  exact hfree

end GroupPresentation
