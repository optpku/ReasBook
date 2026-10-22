/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_3_2
import CombinatorialGroupTheory_Magnus_2004.Chap03.Corollary_3_10_5

universe u

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

/-!
Primary domain: aspherical presentations, relation modules, and projective resolutions of the
trivial module.

Layer triage:
- `source-facing`: an aspherical presentation `(X; R)` with no relator a proper power, and the
  conclusion that the presented group has cohomological dimension at most `2`.
- `core/canonical`: `CayleyComplex.Coordinates.IsAspherical` is the owner asphericity predicate,
  `quotientGroupRingTrivialModule (Subgroup.normalClosure R)` is the owner trivial right
  `ℤG`-module, and `CategoryTheory.HasProjectiveDimensionLE` is the owner abstraction for the
  cohomological-dimension bound.
- `bridge/view`: the same textbook phrase can be witnessed by a projective resolution of the
  canonical trivial module whose terms vanish from degree `3` onward.

Domain sampling:
1. `quotientGroupRingTrivialModule N` from Proposition `2-3-2` is the chapter owner for the
   trivial right `ℤG`-module attached to the presentation.
2. `CategoryTheory.HasProjectiveDimensionLE` from mathlib is the owner predicate for “projective
   dimension at most `n`”.
3. `CategoryTheory.projectiveDimension_le_iff` from mathlib is the canonical comparison between
   the owner predicate and the numerical projective dimension.
4. `relation_ideal_free_resolution` from Proposition `2-3-2` and
   `relationIdealQuotient_free_of_isAspherical_of_relators_not_properPower` from Corollary
   `3-10-5` are the low-degree resolution inputs that produce the degree-`≤ 2` bound.

Primitive vs. derived:
- primitive data: the relator set `R`, the chosen standard Cayley presentation `P`, and the
  relator-side hypothesis that no element of `R` is a proper power;
- derived API: the canonical conclusion `HasProjectiveDimensionLE T 2`, with any explicit
  truncated projective resolution demoted to a bridge theorem.
-/

namespace GroupPresentation

variable {X : Type u} {R : Set (FreeGroup X)}

local notation "N" => Subgroup.normalClosure R
local notation "T" => quotientGroupRingTrivialModule N

/-- Corollary 3-10-6: if `G = (X; R)` is aspherical and no relator is a proper power, then the
canonical trivial `ℤG`-module has projective dimension at most `2`. -/
-- Proof sketch: Proposition `2-3-2` gives the standard low-degree free resolution of the trivial
-- module. Corollary `3-10-5` makes the relation module itself free, so the resolution can be
-- truncated after degree `2`, yielding cohomological dimension at most `2`.
theorem hasProjectiveDimensionLE_two_trivialModule_of_isAspherical_of_relators_not_properPower
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (hAspherical : CayleyComplex.Coordinates.IsAspherical coords)
    (hproper : ∀ r ∈ R, ¬ IsProperPower r) :
    HasProjectiveDimensionLE T 2 := by
  sorry

/-- Companion bridge theorem: the projective-dimension bound in Corollary `3-10-6` may be
realized by a projective resolution of the canonical trivial `ℤG`-module with no terms in degrees
`≥ 3`. -/
theorem exists_projectiveResolution_trivialModule_isZero_from_degree_three_of_isAspherical_of_relators_not_properPower
    {C : TwoComplex}
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (hAspherical : CayleyComplex.Coordinates.IsAspherical coords)
    (hproper : ∀ r ∈ R, ¬ IsProperPower r) :
    ∃ Q : ProjectiveResolution T, ∀ n : ℕ, IsZero (Q.complex.X (n + 3)) := by
  sorry

end GroupPresentation
