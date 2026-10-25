module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w)

/- Domain-style sampling for Definition 7.10.9:
- primary domain: separated presheaves of sets on a Grothendieck site;
- sampled canonical declarations:
  `Presieve.IsSeparatedFor`,
  `Presieve.IsSeparated`,
  `Presieve.IsSheaf.isSeparated`,
  `Presheaf.IsSeparated`;
- source/core/bridge triage:
  `core/canonical`: `Presieve.IsSeparated J F`,
  `bridge/view`: coverwise injectivity criteria such as the plus-construction lemmas.

Primitive data are only the site `(C, J)` and the set-valued presheaf `F`. The coverwise
restriction-map injectivity formulation is derived directly from the defining body of
`Presieve.IsSeparated`. The broader concrete-category predicate `Presheaf.IsSeparated` is not the
owner here, because the source item and the downstream plus API are specifically set-valued.
Accordingly, no separate chapter-level owner or wrapper theorem is kept here.
-/

/- Definition 7.10.9: for a site `(C, J)`, the source-facing owner notion that a set-valued
presheaf `F` is separated is the canonical predicate `Presieve.IsSeparated`. -/
recall Presieve.IsSeparated

/- Source-facing specialization: separatedness of `F` on `(C, J)` is expressed directly as the
proposition `Presieve.IsSeparated J F`. -/
#check (Presieve.IsSeparated J F : Prop)

end CategoryTheory.Presheaf
