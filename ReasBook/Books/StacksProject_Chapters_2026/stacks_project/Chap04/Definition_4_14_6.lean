module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {I : Type w} (M : I → C)

/- Domain-style sampling for Definition 4.14.6:
- `piObj` is the owner abstraction for the product object of a family `M : I → C`.
- `HasProduct` is the canonical existence class for that product.
- `Pi.π` is the derived canonical family of product projections.

Primitive-vs-derived split:
- primitive data: none in this file; the product is already owned upstream as the limit object of
  `Discrete.functor M`.
- derived API: the existence predicate `HasProduct M` and the projections `Pi.π M`. -/

/- Source/core/bridge triage for Definition 4.14.6:
- `source-facing`: the textbook product of a family.
- `core/canonical`: `piObj`.
- `bridge/view`: the discrete-diagram presentation `limit (Discrete.functor M)`, already built
  into the owner. -/

/- Companion recall: existence of the product of the family `M` is expressed by the canonical
typeclass `HasProduct M`. -/
recall HasProduct

section

variable [HasProduct M]

/- Definition 4.14.6: for a family `M : I → C`, the product is the canonical mathlib object
`∏ᶜ M`, i.e. `piObj M = limit (Discrete.functor M)` in the discrete-diagram presentation. -/
#check (∏ᶜ M : C)

/- Companion recall: the core owner declaration for the product object `∏ᶜ M` is `piObj`. -/
recall piObj

/- Companion recall: the product projections from the family members into `∏ᶜ M` are the canonical
morphisms `Pi.π`. -/
recall Pi.π

end

end CategoryTheory.Limits
