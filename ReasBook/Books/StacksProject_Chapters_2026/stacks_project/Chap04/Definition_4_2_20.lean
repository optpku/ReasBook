module

public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Prod

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {X₁ X₂ X₃ : C} {Y₁ Y₂ Y₃ : D}

/- Domain-style sampling for Definition 4.2.20:
- primary domain: product categories in `CategoryTheory`;
- inspected owner declarations: `CategoryStruct.prod`, `prod'`, `Prod.mkHom`, `prod_comp`;
- best owner abstraction: the canonical category instance `prod'` on `C × D`; `CategoryStruct.prod`
  is only the lower structural precursor, not a second public owner.

Primitive-vs-derived split:
- primitive data inherited by the owner stack: the hom-types, identities, and composition on
  `C × D`, implemented upstream by `CategoryStruct.prod` and promoted to a category by `prod'`;
- derived API: the standard product-morphism constructor `Prod.mkHom` together with the pointwise
  identity and composition formulas `prod_id'` and `prod_comp`. -/

/- Source/core/bridge triage for Definition 4.2.20:
- `source-facing`: the textbook description of the product category with pair objects, pair
  morphisms, and componentwise composition.
- `core/canonical`: the mathlib owner instance `CategoryTheory.prod'`.
- `bridge/view`: `Prod.mkHom`, `prod_id'`, and `prod_comp` as the direct source-facing formulas for
  morphisms, identities, and composition. -/

/- Definition 4.2.20 is a `core/canonical` recall: the product category of `C` and `D` is the
canonical mathlib category instance `CategoryTheory.prod'` on `C × D`. -/
recall prod'

/- Definition 4.2.20, source object form: an object of the product category is simply a pair
`(X₁, Y₁) : C × D`. -/
#check ((X₁, Y₁) : C × D)

/- Definition 4.2.20, source hom-set form: a morphism in the product category from `(X₁, Y₁)` to
`(X₂, Y₂)` is the canonical hom-type `((X₁, Y₁) ⟶ (X₂, Y₂))`, definitionally a pair of component
morphisms. -/
#check (((X₁, Y₁) : C × D) ⟶ (X₂, Y₂))

/- Companion recall: `Prod.mkHom` is the canonical constructor for morphisms in the product
category from their two components. -/
recall Prod.mkHom

/- Definition 4.2.20, source morphism constructor: a pair of component morphisms determines the
canonical product-category morphism `f ×ₘ g`. -/
#check fun (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) ↦ f ×ₘ g

/- Definition 4.2.20, source identity formula: the identity of `(X₁, Y₁)` is `(𝟙 X₁, 𝟙 Y₁)`,
packaged canonically by `prod_id'`. -/
recall prod_id'

/- Companion recall: `prod_comp` is derived API for the owner instance `prod'`, giving the
canonical componentwise composition rule in the product category. -/
recall prod_comp

end CategoryTheory
