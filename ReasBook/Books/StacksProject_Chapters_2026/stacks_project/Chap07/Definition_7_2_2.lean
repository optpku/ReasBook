module

public import stacks_project.Chap04.Definition_4_3_2
import Mathlib.Tactic.Recall

@[expose] public section

universe uC vC uA vA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C]
variable (A : Type uA) [Category.{vA} A]

/- Domain-style sampling for Definition 7.2.2:
- primary domain: presheaves as contravariant functors in `CategoryTheory`
- sampled owner declarations:
  the Chapter 4 owner recall `(Cᵒᵖ ⥤ A)` from Definition 4.3.2,
  `NatTrans` and `F ⟶ G` from Definition 4.2.15,
  the specialized chapter owner `Presheaf C` from Definition 4.3.3
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`
- primitive data: only the standard functor data on `Cᵒᵖ`
- derived API: natural transformations and the inherited category structure; `Presheaf C` is only
  the `Type`-valued specialization
-/
/- Source/core/bridge triage for Definition 7.2.2:
- source-facing notion: an `A`-valued presheaf on `C`
- core/canonical owner: the Chapter 4 owner `Cᵒᵖ ⥤ A`
- bridge/view: `Presheaf C` when `A = Type _`
-/
/- Definition 7.2.2 is exactly Definition 4.3.2 in presheaf language: an `A`-valued presheaf on
`C` is an object of the functor category `Cᵒᵖ ⥤ A`. -/
#check (Cᵒᵖ ⥤ A)

/- Companion recall: the primitive data are the usual functor data out of `Cᵒᵖ`. -/
recall Functor

end

end CategoryTheory
