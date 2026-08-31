module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoricalPullback
open scoped CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Domain-style sampling for Example 4.31.3:
- primary domain: categorical pullbacks of functors between categories;
- sampled owner-level declarations:
  `CategoricalPullback`,
  `CategoricalPullback.π₁`,
  `CategoricalPullback.π₂`,
  `CategoricalPullback.catCommSq`;
- best owner abstraction: the canonical pullback owner `F ⊡ G`;
- primitive data: owned by `CategoricalPullback`;
- derived API: the projection functors `π₁ F G`, `π₂ F G`, and the canonical square `catCommSq`.

Source/core/bridge triage:
- `source-facing`: the textbook `2`-fibre product category attached to `F` and `G`;
- `core/canonical`: `F ⊡ G`;
- `bridge/view`: the projection functors and their canonical commutative square. -/

/- Example 4.31.3: the textbook `2`-fibre product category attached to functors `F : A ⥤ C` and
`G : B ⥤ C` is the canonical categorical pullback `F ⊡ G`. -/
#check (F ⊡ G)

/- Companion check: the first projection `F ⊡ G ⥤ A` is the canonical functor `π₁ F G`. -/
#check (π₁ F G : F ⊡ G ⥤ A)

/- Companion check: the second projection `F ⊡ G ⥤ B` is the canonical functor `π₂ F G`. -/
#check (π₂ F G : F ⊡ G ⥤ B)

/- Companion check: the canonical commutative square
`CatCommSq (π₁ F G) (π₂ F G) F G` is the instance `catCommSq`. -/
#check (inferInstance : CatCommSq (π₁ F G) (π₂ F G) F G)

end CategoryTheory.Limits
