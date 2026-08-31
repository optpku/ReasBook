module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 7.2.1:
- primary domain: set-valued presheaves on a category
- sampled canonical declarations:
  `CategoryTheory.Functor`,
  the ambient functor category `Cᵒᵖ ⥤ Type w`,
  the chapter owner `Presheaf C` from Definition 4.3.3,
  the site-level sheaf owner `Sheaf J (Type w)`, whose primitive underlying object is again a
  set-valued presheaf
- best owner abstraction in this chapter/project: `Presheaf C`
- primitive data: only the underlying contravariant functor
- derived API: natural transformations and the inherited category structure from the functor
  category
-/
/-
Source/core/bridge triage for Definition 7.2.1:
- source-facing notion: a set-valued presheaf on `C`
- core/canonical owner in this chapter/project: `Presheaf C`, introduced in Definition 4.3.3
- derived API: the category structure and natural-transformation morphisms are inherited from the
  functor category `Cᵒᵖ ⥤ Type w`
-/
/-
Definition 7.2.1: a presheaf of sets on `C` is the chapter owner `Presheaf C` from
Definition 4.3.3, i.e. a contravariant functor
`Cᵒᵖ ⥤ Type w`.
-/
recall Presheaf

end CategoryTheory
