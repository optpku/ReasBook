module

public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Definition 7.7.6:
- primary domain: sheaf conditions for category-valued presheaves on a Grothendieck site;
- sampled canonical declarations:
  `CategoryTheory.Presheaf.IsSheaf`,
  `CategoryTheory.Sheaf`,
  `CategoryTheory.Presheaf.isSheaf_iff_multifork`,
  `CategoryTheory.GrothendieckTopology.HasSheafCompose.isSheaf`;
- source-facing layer: the Stacks definition of a sheaf with values in an arbitrary category `A`;
- core/canonical owner: `CategoryTheory.Presheaf.IsSheaf`;
- bridge/view: `CategoryTheory.Sheaf` packages the same owner predicate as the full subcategory of
  sheaf-valued presheaves, `CategoryTheory.Presheaf.isSheaf_iff_multifork` is the canonical
  multifork reformulation of the same owner predicate, and
  `CategoryTheory.GrothendieckTopology.HasSheafCompose.isSheaf` is the derived API for
  postcomposition with sheaf-preserving functors.

Primitive data are only the site `(C, J)`, the value category `A`, and the presheaf
`ℱ : Cᵒᵖ ⥤ A`. The family of set-valued presheaves `ℱ ⋙ coyoneda.obj (op X)` is the defining body
of the canonical owner itself, so there is no separate local wrapper or derived field to keep.
-/

/- Definition 7.7.6: a presheaf `ℱ : Cᵒᵖ ⥤ A` with values in a category `A` is a sheaf on the
site `(C, J)` if for every object `E : A`, the set-valued presheaf `ℱ ⋙ coyoneda.obj (op E)` is a
sheaf. This is exactly `Presheaf.IsSheaf`. -/
recall Presheaf.IsSheaf
