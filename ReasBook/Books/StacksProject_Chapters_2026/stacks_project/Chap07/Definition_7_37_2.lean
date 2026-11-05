module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Definition 7.37.2:
- primary domain: points of a Grothendieck topology and morphisms between them;
- sampled owner declarations:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.Hom`,
  `GrothendieckTopology.Point.Hom.presheafFiber`,
  `GrothendieckTopology.Point.Hom.sheafFiber`.
-/
/- Source/core/bridge triage for Definition 7.37.2:
- source-facing notion: a morphism of points of the site `(C, J)`
- core/canonical owner: `GrothendieckTopology.Point.Hom`
- bridge/view: the induced maps on presheaf fibers and sheaf fibers, namely
  `GrothendieckTopology.Point.Hom.presheafFiber` and
  `GrothendieckTopology.Point.Hom.sheafFiber`
- primitive data: a natural transformation `p'.fiber ⟶ p.fiber`
- derived API: functoriality on presheaf and sheaf fibers, together with the component formulas used
  in [Lemma_7_37_1](/volume/math/AI4M/users/zcwang/stacks_project/stacks_project/Items/Chap07/Lemma_7_37_1.lean)
-/
/- Definition 7.37.2: for points `p` and `p'` of the site `(C, J)`, a morphism `p ⟶ p'` is the
canonical mathlib notion `GrothendieckTopology.Point.Hom p p'`, whose data is a natural
transformation `p'.fiber ⟶ p.fiber`. -/
recall GrothendieckTopology.Point.Hom

end CategoryTheory
