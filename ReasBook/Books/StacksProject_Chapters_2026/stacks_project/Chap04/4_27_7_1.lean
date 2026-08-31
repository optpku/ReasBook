module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Remark_4_27_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling in the left-localization Hom API:
- primary domain: left calculus of fractions and localized Hom-sets
- inspected declarations:
  `CategoryTheory.MorphismProperty.Under.forget`,
  `CategoryTheory.uliftCoyoneda.obj`,
  `CategoryTheory.Localization.exists_leftFraction`,
  `CategoryTheory.MorphismProperty.left_localization_hom_colimit`
- best public owner abstraction: `CategoryTheory.MorphismProperty.left_localization_hom_colimit`

Primitive data: a left multiplicative system `W` and objects `X Y : C`.
Derived API: the Hom-diagram on `Y / W`, its canonical cocone into
`Hom_{W^{-1}\mathcal C}(X, Y)`, and the resulting colimit comparison isomorphism.

This numbered item is a `bridge/view` recall: the source formula is the colimit presentation of
localized morphisms, and the stable public owner is the colimit isomorphism theorem. We therefore
recall the public comparison isomorphism rather than any internal colimit witness.
-/

/- 4.27.7.1: for a left multiplicative system `W`, the localized Hom-set
`Hom_{W^{-1}\mathcal C}(X, Y)` is canonically isomorphic to the colimit over `Y / W` of the
Hom-sets `Hom_\mathcal C(X, Y')`, where `s : Y ⟶ Y'` ranges over arrows in `W`. This is exactly
the canonical comparison isomorphism `CategoryTheory.MorphismProperty.left_localization_hom_colimit`.
-/
recall CategoryTheory.MorphismProperty.left_localization_hom_colimit
