module

import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Limits.Indization.Category
public import stacks_project.Chap04.Lemma_4_22_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe uC vC

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Remark 4.22.5:
- primary domain: the canonical pro-category model `((Ind Cᵒᵖ)ᵒᵖ)` and its owner-level morphism
  formula for diagrams in `C`.
- inspected owner-level declarations:
  `Ind C`,
  `proObjectHomEquivLimitProSystemHomColimitFunctor`,
  `CorepresentableBy.equivUliftCoyonedaIso`,
  `essentiallyConstant_proObject_characterizations`.
- best owner abstractions for this remark:
  `((Ind Cᵒᵖ)ᵒᵖ)` together with `proObjectHomEquivLimitProSystemHomColimitFunctor`; for the
  constant-value criterion, the chapter owner theorem
  `essentiallyConstant_proObject_characterizations` and its fixed-object bridge
  `CorepresentableBy.equivUliftCoyonedaIso`.

Primitive-vs-derived split:
- primitive data: diagrams `F : I ⥤ C` and `G : J ⥤ C`, and an object `X : C` for the
  constant-system comparison.
- derived API: the constant-system embedding `(opOpEquivalence C).inverse ⋙ Ind.yoneda.op`, the
  owner-level Hom formula `proObjectHomEquivLimitProSystemHomColimitFunctor`, the fixed-object
  comparison with `uliftCoyoneda.obj (op X)`, and the essential-constancy criterion recalled
  directly from `essentiallyConstant_proObject_characterizations`.

Source/core/bridge triage:
- `source-facing`: the pro-category model and the formula
  `Mor_{Pro-C}(F, G) = lim_j colim_i Mor_C(F_i, G_j)`.
- `core/canonical`: `((Ind Cᵒᵖ)ᵒᵖ)`, `proObjectHomEquivLimitProSystemHomColimitFunctor`, and
  `IsEssentiallyConstantCofilteredDiagram`.
- `bridge/view`: the fully faithful constant-system embedding and the companion
  `CorepresentableBy ↔ iso to uliftCoyoneda`; this file should recall those owner statements
  directly rather than repackage them as a new existential theorem. -/

/- Remark 4.22.5: a canonical model for the big category `\text{Pro-}\mathcal{C}` of
pro-objects of `C` is the opposite category `((Ind Cᵒᵖ)ᵒᵖ)`, dual to the ind-object construction
of Remark 4.22.4. -/
#check (Ind Cᵒᵖ)ᵒᵖ

/- Companion check: the canonical constant-system embedding of `C` into this pro-category model
is the composite of `(opOpEquivalence C).inverse : C ⥤ Cᵒᵖᵒᵖ` with
`Ind.yoneda.op : Cᵒᵖᵒᵖ ⥤ (Ind Cᵒᵖ)ᵒᵖ`. -/
#check ((opOpEquivalence C).inverse ⋙ Ind.yoneda.op)

/- Companion check: the canonical constant-system embedding into `((Ind Cᵒᵖ)ᵒᵖ)` is fully
faithful, by composing the fully faithful inverse of `opOpEquivalence C` with
`Ind.yoneda.fullyFaithful.op`. -/
#check (opOpEquivalence C).fullyFaithfulInverse.comp Ind.yoneda.fullyFaithful.op

/- Remark 4.22.5: the owner-level morphism formula in the canonical pro-category model identifies
morphisms from the formal pro-object of `G` to the formal pro-object of `F` with the inverse
limit of the Hom-colimit diagram `j ↦ colim_i Hom(F_i, G_j)`. -/
recall proObjectHomEquivLimitProSystemHomColimitFunctor

/- Companion recall: for a fixed `X`, identifying a pro-Hom colimit functor with the constant
pro-object on `X` is exactly the canonical equivalence
`CorepresentableBy.equivUliftCoyonedaIso`. -/
recall CorepresentableBy.equivUliftCoyonedaIso

/- Companion recall: the constant-system criterion for a cofiltered diagram is already owned by
`essentiallyConstant_proObject_characterizations`; together with
`CorepresentableBy.equivUliftCoyonedaIso`, this is the canonical realization-level form of
"being isomorphic to a constant pro-object". -/
recall essentiallyConstant_proObject_characterizations

end CategoryTheory
