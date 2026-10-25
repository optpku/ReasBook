module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 4.4.2:
- primary domain: binary products as limits of pair diagrams.
- sampled owner declarations:
  `HasBinaryProduct X Y`,
  `HasBinaryProducts C`,
  `hasBinaryProducts_of_hasLimit_pair`,
  `pair X Y`.
- owner split:
  `HasBinaryProducts C` is the core/canonical owner abstraction for products of pairs in `C`,
  while `HasBinaryProduct X Y` is the canonical fixed-pair abbreviation.
- primitive data: for each pair `X`, `Y`, the existence of a limit of `pair X Y`.
- derived API: the canonical owner `HasBinaryProducts C`, the fixed-pair abbreviation
  `HasBinaryProduct X Y`, and the constructor `hasBinaryProducts_of_hasLimit_pair`.
-/

/- Source/core/bridge triage for Definition 4.4.2:
- `source-facing`: the textbook property that every pair of objects admits a product.
- `core/canonical`: the mathlib typeclass `HasBinaryProducts C`.
- `bridge/view`: the pointwise abbreviation `HasBinaryProduct X Y` and the constructor
  `hasBinaryProducts_of_hasLimit_pair` connecting the global owner to the pointwise formulation. -/

/- Canonical recall: the Stacks notion that a category has products of pairs is the canonical
mathlib typeclass `CategoryTheory.Limits.HasBinaryProducts`. -/
recall HasBinaryProducts

/- Definition 4.4.2 also uses the canonical fixed-pair abbreviation for the statement that
`X` and `Y` admit a binary product. -/
#check HasBinaryProduct X Y

section

variable [∀ {X Y : C}, HasLimit (pair X Y)]

/- Companion recall: once the primitive limit data `HasLimit (pair X Y)` is available for every
pair `X`, `Y`, the corresponding global owner instance is the canonical theorem
`hasBinaryProducts_of_hasLimit_pair`. -/
recall hasBinaryProducts_of_hasLimit_pair

end

end CategoryTheory.Limits
