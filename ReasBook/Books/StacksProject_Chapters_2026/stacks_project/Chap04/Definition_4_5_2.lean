module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 4.5.2:
- primary domain: binary coproducts in `CategoryTheory.Limits`;
- sampled owner declarations:
  `HasBinaryCoproducts`,
  `HasBinaryCoproduct`,
  `hasBinaryCoproducts_of_hasColimit_pair`,
  `Definition_4_4_2` as the product-side chapter analogue;
- owner split:
  `HasBinaryCoproducts C` is the core/canonical owner abstraction for coproducts of pairs in `C`,
  while `HasBinaryCoproduct X Y` is the canonical pointwise abbreviation for a fixed pair.
- primitive data: for each pair `X`, `Y`, the existence of a colimit of `pair X Y`.
- derived API: the pointwise abbreviation `HasBinaryCoproduct X Y`, the canonical owner
  `HasBinaryCoproducts C`, and the constructor `hasBinaryCoproducts_of_hasColimit_pair`.
-/

/- Source/core/bridge triage for Definition 4.5.2:
- `source-facing`: the textbook property that every pair of objects admits a coproduct.
- `core/canonical`: the mathlib typeclass `HasBinaryCoproducts C`.
- `bridge/view`: the pointwise abbreviation `HasBinaryCoproduct X Y` and the constructor
  `hasBinaryCoproducts_of_hasColimit_pair` connecting the global owner to the pointwise
  formulation. -/

/- Canonical recall: the Stacks notion that a category has coproducts of pairs is the canonical
mathlib typeclass `CategoryTheory.Limits.HasBinaryCoproducts`. -/
recall HasBinaryCoproducts

/-
Definition 4.5.2 also uses the canonical fixed-pair abbreviation for the statement that `X` and
`Y` admit a binary coproduct.
-/
#check HasBinaryCoproduct X Y

section

variable [∀ {X Y : C}, HasColimit (pair X Y)]

/- Companion recall: once the primitive colimit data `HasColimit (pair X Y)` is available for
every pair `X`, `Y`, the corresponding global owner instance is the canonical theorem
`hasBinaryCoproducts_of_hasColimit_pair`. -/
recall hasBinaryCoproducts_of_hasColimit_pair

end

end CategoryTheory.Limits
