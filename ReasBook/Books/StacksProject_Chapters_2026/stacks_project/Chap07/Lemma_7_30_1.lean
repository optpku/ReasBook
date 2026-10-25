module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 7.30.1:
- primary domain: localization of a sheaf topos at an object, expressed by the slice-category
  adjunction over that object;
- sampled owner declarations:
  `Over.forgetAdjStar`,
  `Over.forget`,
  `Over.star_obj_left`,
  `Over.star_obj_hom`;
- best owner abstraction: the canonical slice-localization owner is the adjunction
  `Over.forget ℱ ⊣ Over.star ℱ`, packaged by `Over.forgetAdjStar ℱ`;
- primitive data: only the sheaf `ℱ`;
- derived API: the forgetful functor `Over.forget ℱ` and the concrete description of
  `(Over.star ℱ).obj ℋ` through `Over.star_obj_left` and `Over.star_obj_hom`.

Source/core/bridge triage:
- `source-facing`: the identification of the localization morphism at `ℱ` with the standard slice
  forgetful functor and its right adjoint;
- `core/canonical`: `Over.forgetAdjStar ℱ`;
- `bridge/view`: `Over.star_obj_left ℱ` and `Over.star_obj_hom ℱ`, which describe the underlying
  object and structure morphism of the pullback-style inverse-image construction.
-/

/- Lemma 7.30.1: for a sheaf `ℱ` on `(C, J)`, the canonical localization morphism
`Sh(C, J)/ℱ ⥤ Sh(C, J)` is the slice forgetful functor `Over.forget ℱ`, with inverse-image
functor `Over.star ℱ`. The latter sends a sheaf `ℋ` to the slice object over `ℱ` whose
underlying sheaf is `ℱ ⨯ ℋ`, canonically equivalent to the textbook object `ℋ × ℱ / ℱ`; thus
`j_{ℱ!}` is forgetful and `j_ℱ^{-1}` is pullback along `ℱ ⟶ 1`. -/
#check Over.forgetAdjStar ℱ

/- Companion recall: the lower-shriek functor of the localization is the slice forgetful functor
`Over.forget ℱ : Over ℱ ⥤ Sheaf J (Type w)`. -/
#check Over.forget ℱ

/- Companion recall: the inverse-image functor sends `ℋ` to the slice object over `ℱ` with
underlying sheaf `ℱ ⨯ ℋ`. -/
#check Over.star_obj_left ℱ

/- Companion recall: the structure morphism of the inverse-image object is the projection
`ℱ ⨯ ℋ ⟶ ℱ`. -/
#check Over.star_obj_hom ℱ
