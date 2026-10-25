module

import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_26_1

@[expose] public section

open CategoryTheory SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 6.26.3:
- primary domain: pseudofunctoriality of pushforward and pullback for sheaves of modules on
  ringed spaces;
- sampled owner declarations:
  `SheafOfModules.pushforwardComp`,
  `SheafOfModules.pullbackComp`,
  `RingedSpace.Hom.toRingCatSheafHom`,
  `RingedSpace.Hom.pushforward`,
  `RingedSpace.Hom.pullback`;
- owner abstraction: the canonical owners are `SheafOfModules.pushforwardComp` and
  `SheafOfModules.pullbackComp`, specialized along
  `RingedSpace.Hom.toRingCatSheafHom`;
- primitive data: composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the ringed-space specializations of those comparison isomorphisms.

Source/core/bridge triage:
- `source-facing`: the ringed-space comparison between pullback or pushforward along a composite
  and the corresponding composite functors;
- `core/canonical`: `SheafOfModules.pushforwardComp` and `SheafOfModules.pullbackComp`;
- `bridge/view`: specialization along `RingedSpace.Hom.toRingCatSheafHom`.

The previous local pullback-composition abbreviation was an exact wrapper around the canonical
owner theorem, so the refined file recalls the owner theorem directly instead of keeping a
parallel local copy. -/

/- Lemma 6.26.3, owner recalls: the only core owners are the canonical comparison isomorphisms
`SheafOfModules.pushforwardComp` and `SheafOfModules.pullbackComp`; the ringed-space statements
below are their source-facing specializations. -/
recall pushforwardComp
recall pullbackComp

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 6.26.3 (1): for morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
pushforward functor along the composite is canonically identified with the composite of the two
pushforward functors. -/
#check
  ((pushforwardComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f)).symm :
    (f ≫ g) _* ≅ f _* ⋙ g _*)

/- Lemma 6.26.3 (2): for morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
pullback along the composite is canonically isomorphic to the composite pullback functor
`f^* ∘ g^*`. -/
#check
  ((pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f)).symm :
    (f ≫ g)^* ≅ g^* ⋙ f^*)

end

end AlgebraicGeometry
