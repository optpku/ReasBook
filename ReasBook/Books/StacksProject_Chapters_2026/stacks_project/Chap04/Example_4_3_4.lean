module

public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 4.3.4:
- primary domain: presheaves on a category and the Yoneda realization of representable presheaves;
- inspected owner-level declarations:
  `Presheaf`,
  `yoneda`,
  `yoneda_obj_obj`,
  `yoneda_obj_map`;
- best owner abstraction: the ambient source-facing owner is `Presheaf C`, while the canonical
  core owner for the representable presheaf `h_U` is the Yoneda object `yoneda.obj U : Presheaf C`;
- primitive data: only the Yoneda embedding `yoneda`;
- derived API: the objectwise and morphismwise computation rules `yoneda_obj_obj` and
  `yoneda_obj_map`;
- bridge/view: the reusable source-facing notation `h[U]` for the textbook representable presheaf
  `h_U`.

Source/core/bridge triage:
- `source-facing`: the textbook representable presheaf `h_U : Presheaf C` and its evaluation
  formulas;
- `core/canonical`: `Presheaf`, `yoneda`, `yoneda_obj_obj`, `yoneda_obj_map`;
- `bridge/view`: the notation bridge `h[U]` for the owner object `yoneda.obj U`. -/

namespace RepresentablePresheaf

/- Textbook notation for the representable presheaf `h_U`. Since Lean does not support the
subscripted binder directly as notation, we write this reusable surface form as `h[U]`. -/
scoped notation:max "h[" U "]" => yoneda.obj U

end RepresentablePresheaf

open scoped RepresentablePresheaf

section

variable (U : C)

/- Example 4.3.4: the textbook representable presheaf attached to `U` is the canonical Yoneda
object `h[U] : Presheaf C`. -/
#check (h[U] : Presheaf C)

end

/- Example 4.3.4: the representable presheaves on `C` are organized by the canonical Yoneda
embedding `yoneda : C ⥤ Presheaf C`; the textbook object `h_U` is obtained by evaluating this
owner functor at `U`. -/
recall yoneda

/- Example 4.3.4 (object formula): for each object `U` of a category `C`, the representable
presheaf `h[U] = yoneda.obj U` sends an object `X` to the hom-set `Hom_C(X, U)`. This is the
canonical computation rule `yoneda_obj_obj`. -/
recall yoneda_obj_obj

/- Example 4.3.4 (morphism formula): for `f : X ⟶ Y` in `Cᵒᵖ`, the restriction map of the
representable presheaf `h[U]` is precomposition by `f.unop`, namely
`h[U].map f g = f.unop ≫ g`. This is the canonical computation rule
`yoneda_obj_map`. -/
recall yoneda_obj_map

end CategoryTheory
