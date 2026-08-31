module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Limits

variable {I : Type w}
variable {C : Type u} [Category.{v} C]
variable (M : I → C)

/- Domain-style sampling for Definition 4.14.7:
- primary domain: categorical coproducts as colimits of discrete diagrams.
- sampled owner abstractions in `Mathlib.CategoryTheory.Limits.Shapes.Products`:
  `Cofan`, `HasCoproduct`, `sigmaObj`, `Sigma.ι`.

Primitive-vs-derived split:
- primitive data in the domain: a cofan together with its colimit universal property.
- primitive data in this file: none; the coproduct owner is already supplied upstream by
  `sigmaObj M = colimit (Discrete.functor M)`.
- derived API: the existence predicate `HasCoproduct M` and the canonical coproduct injections
  `Sigma.ι M`. -/

/- Source/core/bridge triage for Definition 4.14.7:
- `source-facing`: the textbook coproduct of a family.
- `core/canonical`: `sigmaObj`.
- `bridge/view`: the discrete-diagram presentation `colimit (Discrete.functor M)`, already built
  into the owner. -/

/- Companion recall: existence of the coproduct of the family `M` is expressed by the canonical
typeclass `HasCoproduct M`. -/
recall HasCoproduct

section

variable [HasCoproduct M]

/- Definition 4.14.7: for a family `M : I → C`, the coproduct is the canonical mathlib object
`∐ M`, i.e. `sigmaObj M = colimit (Discrete.functor M)` in the discrete-diagram presentation. -/
#check (∐ M : C)

/- Companion recall: the core owner declaration for the coproduct object `∐ M` is `sigmaObj`. -/
recall sigmaObj

/- Companion recall: the coproduct injections from the family members into `∐ M` are the canonical
morphisms `Sigma.ι`. -/
recall Sigma.ι

end

end CategoryTheory.Limits
