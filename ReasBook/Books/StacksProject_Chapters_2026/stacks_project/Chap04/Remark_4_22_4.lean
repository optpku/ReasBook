module

public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Limits.Indization.LocallySmall
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.Functor
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Remark 4.22.4:
- primary domain: ind-objects and representability of the presheaf colimit attached to a filtered
  diagram.
- inspected owner-level declarations:
  `Ind C`,
  `Ind.lim`,
  `Ind.limCompInclusion`,
  `Functor.RepresentableBy`,
  `RepresentableBy.equivUliftYonedaIso`.
- best owner abstraction: the mathlib ind-object category `Ind C`, with the bridge/view to a
  fixed representing object expressed by `Functor.RepresentableBy`.

Primitive-vs-derived split:
- primitive owner data: the filtered diagram `M : I ⥤ C` and its canonical ind-object
  `(Ind.lim I).obj M`.
- derived API: identification of the constant ind-object `Ind.yoneda.obj X` with `(Ind.lim I).obj
  M`, and the induced representability of the presheaf colimit `colimit (M ⋙ uliftYoneda)`.

Source/core/bridge triage:
- `source-facing`: the remark that the big ind-category is `Ind C`.
- `core/canonical`: `Ind C`, `Ind.yoneda`, and `Ind.lim`.
- `bridge/view`: the remaining equivalence below between an isomorphism in `Ind C` and a
  representing structure on the associated presheaf colimit. -/

/- Remark 4.22.4: the big category of ind-objects of `C` is the canonical mathlib construction
`Ind C`. -/
#check Ind C

/- Companion recall: the canonical functor `C ⥤ Ind C` sending `X` to the constant ind-object on
`X` is `Ind.yoneda`. -/
recall Ind.yoneda

/- Companion recall: the constant-system functor `Ind.yoneda : C ⥤ Ind C` is fully faithful. -/
recall Ind.yoneda.fullyFaithful

variable {C}

/- Companion recall: a filtered system in `C` determines an ind-object through the canonical
functor `Ind.lim`. -/
recall Ind.lim

/- Companion recall: computing `Ind.lim` inside presheaves is governed by the canonical comparison
isomorphism `Ind.limCompInclusion`. -/
recall Ind.limCompInclusion

/- Companion recall: the constant ind-object `Ind.yoneda.obj X` becomes the ulift-Yoneda presheaf
through the canonical comparison isomorphism `Ind.yonedaCompInclusion`. -/
recall Ind.yonedaCompInclusion

/- Companion recall: representing data for a presheaf are canonically equivalent to an
isomorphism from `uliftYoneda.obj X`. -/
recall RepresentableBy.equivUliftYonedaIso

/- Companion recall: the textbook ind-Yoneda Hom formula is the canonical owner-level equivalence
`colimitYonedaHomEquiv`, applied to the presheaf presentation supplied by `Ind.limCompInclusion`.
Evaluating `colimit (N ⋙ yoneda)` at `op (M.obj i)` recovers `colim_j Hom_C(M_i, N_j)`. -/
recall colimitYonedaHomEquiv

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

/-- Bridge/view companion to Remark 4.22.4: the constant ind-object on `X` is isomorphic to the
ind-object of a filtered system exactly when the associated presheaf colimit is represented by
`X`. -/
noncomputable def indLim_iso_yoneda_equiv_representableBy
    (M : I ⥤ C) (X : C) :
    (Ind.yoneda.obj X ≅ (Ind.lim I).obj M) ≃
      (colimit (M ⋙ uliftYoneda.{v})).RepresentableBy X :=
  let hInclusion : (Ind.inclusion C).FullyFaithful := Ind.inclusion.fullyFaithful
  let hLim : (Ind.inclusion C).obj ((Ind.lim I).obj M) ≅ colimit (M ⋙ uliftYoneda.{v}) :=
    Ind.limCompInclusion.app M ≪≫
      (HasColimit.isoOfNatIso (isoWhiskerLeft M uliftYonedaIsoYoneda)).symm
  let hYoneda : (Ind.inclusion C).obj (Ind.yoneda.obj X) ≅ uliftYoneda.obj X :=
    Ind.yonedaCompInclusion.app X ≪≫ (uliftYonedaIsoYoneda.app X).symm
  calc
    (Ind.yoneda.obj X ≅ (Ind.lim I).obj M)
      ≃ ((Ind.inclusion C).obj (Ind.yoneda.obj X) ≅
          (Ind.inclusion C).obj ((Ind.lim I).obj M)) :=
        hInclusion.isoEquiv
    _ ≃ (uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{v})) :=
        Iso.isoCongr hYoneda hLim
    _ ≃ (colimit (M ⋙ uliftYoneda.{v})).RepresentableBy X :=
        (RepresentableBy.equivUliftYonedaIso _ _).symm

end

end CategoryTheory
