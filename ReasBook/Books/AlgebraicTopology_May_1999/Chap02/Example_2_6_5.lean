/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u₁ u₂

open CategoryTheory CategoryTheory.Limits

variable {ι : Type u₁} {C : Type u₂} [Category.{v} C] (f : ι → C)

/- Example 2.6.5: when a diagram is indexed by a discrete type `ι`, the existence of its colimit
is expressed by the canonical coproduct class `HasCoproduct f`. -/
#check (HasCoproduct f : Prop)

/- Dually, the existence of its limit is expressed by the canonical product class
`HasProduct f`. -/
#check (HasProduct f : Prop)

variable [HasCoproduct f]

/- The colimit of a discrete diagram is the coproduct object `∐ f`. In sets and topological
spaces, these recover disjoint unions. -/
#check (∐ f : C)

variable [HasProduct f]

/- The limit of a discrete diagram is the product object `∏ᶜ f`. In the standard examples, these
recover Cartesian products. -/
#check (∏ᶜ f : C)

/- Topological spaces have arbitrary coproducts and products, giving disjoint unions and Cartesian
products. -/
#check (inferInstance : HasCoproducts TopCat)

/- Topological spaces have arbitrary products. -/
#check (inferInstance : HasProducts TopCat)

/- Abelian groups have arbitrary coproducts and products; the coproducts are direct sums. -/
#check (inferInstance : HasCoproducts AddCommGrpCat)

/- Abelian groups have arbitrary products. -/
#check (inferInstance : HasProducts AddCommGrpCat)

/- Groups have arbitrary products, giving Cartesian products in `GrpCat`. -/
#check (inferInstance : HasProducts GrpCat)

/- For groups, the indexed free product carries the canonical coproduct inclusions
`Monoid.CoprodI.of`, and its universal property is expressed by `Monoid.CoprodI.lift`. -/
#check Monoid.CoprodI.of
#check Monoid.CoprodI.lift
