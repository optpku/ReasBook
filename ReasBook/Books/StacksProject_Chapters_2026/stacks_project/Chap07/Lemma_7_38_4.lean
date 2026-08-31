module

public import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

namespace CategoryTheory

open GrothendieckTopology
open CategoryTheory.ObjectProperty

/- Domain-style sampling for Lemma 7.38.4:
- primary domain: conservative families of points on Grothendieck sites and their behavior under
  localization to slice sites;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `ObjectProperty.IsConservativeFamilyOfPoints.over`,
  `GrothendieckTopology.HasEnoughPoints`,
  the slice-site instance `[HasEnoughPoints (J.over U)]`;
- source/core/bridge triage:
  `source-facing`: the Stacks statement that a conservative family of points stays conservative on
    each localized site;
  `core/canonical`: the owner theorem `ObjectProperty.IsConservativeFamilyOfPoints.over` and the
    owner class `HasEnoughPoints`;
  `bridge/view`: the localized point construction `Φ.over x` and the derived slice enough-points
    instance.
- primitive data: an object property `P : ObjectProperty (Point J)` and the conservativity proof
  `P.IsConservativeFamilyOfPoints`;
- derived API: the localized family and the enough-points consequence for slice sites.

This file should therefore remain a direct recall/use of the owner theorem, not a parallel local
wrapper around localized point families.
-/

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]
variable {P : ObjectProperty (Point.{w} J)} [ObjectProperty.Small.{w} P]
variable [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
variable {U : C} [HasSheafify (J.over U) (Type w)]

/- Lemma 7.38.4: if `P` is a conservative family of points of the site `(C, J)`, then the
localized points `Φ.over x` for `Φ ∈ P` and `x : Φ.fiber.obj U` form a conservative family of
points of the localized site `(C/U, J.over U)`. This is the canonical mathlib statement encoding
the textbook family `{q_{i, x}}`. -/
recall IsConservativeFamilyOfPoints.over

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]
variable [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
variable {U : C} [HasSheafify (J.over U) (Type w)]
variable [HasEnoughPoints.{w} J]

/- Companion check: if the site `(C, J)` has enough points, then every localization `(C/U,
J.over U)` has enough points as well; in mathlib this is the canonical instance on `J.over U`. -/
#check (inferInstance : HasEnoughPoints.{w} (J.over U))

end

end CategoryTheory
