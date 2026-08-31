module

public import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/- Domain-style sampling for Definition 7.12.3:
- primary domain: representable sheaves on a subcanonical site, organized by the sheaf-valued
  Yoneda embedding;
- sampled owner API:
  `GrothendieckTopology.Subcanonical`,
  `GrothendieckTopology.yoneda`,
  `GrothendieckTopology.yonedaCompSheafToPresheaf`,
  `GrothendieckTopology.yonedaFullyFaithful`;
- best owner abstraction: the sheaf-valued Yoneda functor `J.yoneda`;
- primitive data: only the subcanonical topology `J` and the induced functor `J.yoneda`, whose
  objects are the representable sheaves and whose morphism map is inherited from ordinary Yoneda;
- derived API: the forgetful comparison `J.yonedaCompSheafToPresheaf` and the full-faithfulness
  witness `J.yonedaFullyFaithful`.

Source/core/bridge triage:
- `source-facing`: for each `U : C`, the representable sheaf attached to `U`;
- `core/canonical`: the owner functor `J.yoneda`;
- `bridge/view`: `J.yonedaCompSheafToPresheaf`, identifying the underlying presheaf of
  `J.yoneda.obj U` with the ordinary representable presheaf.

This file is targeting the `core/canonical` layer: the source notion is already owned upstream by
`J.yoneda`, so the correct refinement is a direct recall of that owner and its thin canonical
companions, not a new local wrapper around representable sheaves.
-/
/- Definition 7.12.3: on a site with subcanonical topology, the representable sheaf attached to
`U : C` is the sheaf `J.yoneda.obj U`; after forgetting to presheaves this is the usual
representable presheaf `yoneda.obj U`, sometimes denoted `\underline{U}` in the textbook. -/
recall yoneda

/- Companion recall: the sheaf-valued Yoneda embedding on a subcanonical site is fully faithful,
so it exhibits `C` as a full subcategory of `Sheaf J (Type v)`. -/
recall yonedaFullyFaithful

/- Companion recall: forgetting a representable sheaf back to presheaves recovers the ordinary
Yoneda embedding. -/
recall yonedaCompSheafToPresheaf

end CategoryTheory.GrothendieckTopology
