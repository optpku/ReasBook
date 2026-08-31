module

public import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe vC uC vA uA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C]
variable (A : Type uA) [Category.{vA} A]

/- Domain-style sampling for Definition 4.3.2:
- primary domain: opposite-category presentations of contravariant functors
- sampled canonical declarations:
  `CategoryTheory.Functor`,
  `Category.opposite`,
  the functor-category notation `(· ⥤ ·)`,
  the chapter owner `Presheaf` from `Definition_4_3_3`
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`, i.e. `CategoryTheory.Functor`
  specialized to source `Cᵒᵖ` and target `A`
- primitive data: only the ordinary functor data and axioms for a functor out of the opposite
  category
- derived API: natural transformations and the inherited category structure on the functor
  category; the chapter owner `Presheaf C` is only the high-reuse specialization
  `Cᵒᵖ ⥤ Type _`, not a second generic owner
-/
/- Source/core/bridge triage for Definition 4.3.2:
- `source-facing`: a contravariant functor from `C` to `A`
- `core/canonical`: the functor category `Cᵒᵖ ⥤ A`
- primitive data: only an ordinary functor out of the opposite category
- derived API: natural transformations and the ambient category structure inherited from the
  functor category
- `bridge/view`: the chapter alias `Presheaf C` when `A = Type _`
-/

/- Definition 4.3.2: a contravariant functor from `C` to `A` is canonically an object of the
functor category `Cᵒᵖ ⥤ A`, so the refined item is a direct recall of that owner type expression
rather than a parallel local alias. -/
#check (Cᵒᵖ ⥤ A)

/- Companion recall: the primitive data of a contravariant functor are exactly the standard
object map, morphism map, and functoriality axioms of `CategoryTheory.Functor`, specialized to
source `Cᵒᵖ` and target `A`. -/
recall Functor

end

end CategoryTheory
