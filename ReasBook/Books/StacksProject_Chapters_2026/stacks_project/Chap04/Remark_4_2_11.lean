module

public import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory
namespace ObjectProperty

variable {A : Type u} [Category.{v} A]
variable (F : A ⥤ Type w)

/- Domain-style sampling for Remark 4.2.11:
- primary domain: object properties and full subcategories in `Type w`, together with the
  canonical factorization of a functor through such a full subcategory;
- sampled owner declarations:
  `ObjectProperty.ofObj`,
  `ObjectProperty.lift`,
  `ObjectProperty.liftCompιIso`,
  `ObjectProperty.Small`;
- best owner abstraction: the object property `ofObj F.obj` and its canonical owner
  `FullSubcategory`, with `lift` supplying the factorization of `F`;
- primitive data: only the functor `F : A ⥤ Type w`;
- derived API: the lifted functor through `(ofObj F.obj).FullSubcategory`, the comparison
  isomorphism back to `F`, and the induced smallness statements.

Source/core/bridge triage:
- `source-facing`: the objectwise image property `ofObj F.obj`;
- `core/canonical`: `ObjectProperty.lift` and `ObjectProperty.liftCompιIso`;
- `bridge/view`: the smallness consequences for `ofObj F.obj` and its `FullSubcategory`.

The essential-image owner `Functor.essImage` is intentionally not used here: it closes the image
under isomorphism, whereas the source remark is about the literal objectwise image of a
set-valued functor. -/

/- Core/canonical recall for the source-facing image owner used in this remark: the literal
objectwise image of a family of objects is the object property `ofObj`. -/
recall ofObj

/- Remark 4.2.11: a set-valued functor `F` may be regarded as landing in the full subcategory of
`Type w` spanned by its objectwise image. This is the canonical specialization of
`ObjectProperty.lift` to the object property `ofObj F.obj`. -/
#check (ofObj F.obj).lift F (ofObj_apply F.obj)

/- Companion recall: the owner-level factorization through a full subcategory is
`ObjectProperty.lift`; the remark uses this with `P := ofObj F.obj`. -/
recall lift

/- Companion specialization: the factorization through the full subcategory on the objectwise
image comes with the canonical comparison isomorphism furnished by
`ObjectProperty.liftCompιIso`. -/
#check (ofObj F.obj).liftCompιIso F (ofObj_apply F.obj)

/- Companion recall: the objectwise image property of `F` is small by the canonical
`ObjectProperty.Small` instance for `ofObj F.obj`. -/
#synth ObjectProperty.Small (ofObj F.obj)

/- Consequently, the full subcategory of `Type w` cut out by the objectwise image of `F` is
small, via the canonical derived instance on `P.FullSubcategory`. -/
#synth _root_.Small (ofObj F.obj).FullSubcategory

end ObjectProperty
end CategoryTheory
