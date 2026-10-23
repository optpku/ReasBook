module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Remark_4_27_15

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling in the right-localization Hom API:
- primary domain: right calculus of fractions and localized Hom-sets
- inspected declarations:
  `CategoryTheory.MorphismProperty.Over.forget`,
  `CategoryTheory.uliftYoneda.obj`,
  `CategoryTheory.Localization.exists_rightFraction`,
  `CategoryTheory.MorphismProperty.right_localization_hom_colimit`
- best public owner abstraction: `CategoryTheory.MorphismProperty.right_localization_hom_colimit`

Primitive data: a right multiplicative system `S` and objects `X Y : C`.
Derived API: the Hom-diagram on `(S/X)ᵒᵖ`, its canonical cocone into
`Hom_{S^{-1}\mathcal C}(X, Y)`, and the resulting colimit comparison isomorphism.

This numbered item is a `bridge/view` recall: the source formula is the colimit presentation of
localized morphisms, and the stable public owner is the colimit isomorphism theorem. We therefore
recall the public comparison isomorphism rather than any internal colimit witness.
-/

/- 4.27.15.1: for a right multiplicative system `S`, the localized Hom-set
`Hom_{S^{-1}\mathcal C}(X, Y)` is canonically isomorphic to the colimit over `(S / X)ᵒᵖ` of the
Hom-sets `Hom_\mathcal C(X', Y)`, where `s : X' ⟶ X` ranges over arrows in `S`. This is exactly
the canonical comparison isomorphism
`CategoryTheory.MorphismProperty.right_localization_hom_colimit`.
-/
recall CategoryTheory.MorphismProperty.right_localization_hom_colimit
