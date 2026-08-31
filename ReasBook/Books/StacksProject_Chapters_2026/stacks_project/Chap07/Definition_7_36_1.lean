module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_15_1_Topoi

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f g : MorphismOfTopoiIn J K)

/- Domain-style sampling for Definition 7.36.1:
- primary domain: morphisms of topoi and their `2`-morphisms;
- sampled owner API:
  `MorphismOfTopoiIn`,
  the direct-image notation `f _*`,
  `MorphismOfTopoiIn.adjunction`,
  the natural-transformation type `(f _* ⟶ g _*)`;
- source-facing notion: a `2`-morphism `f ⇒ g` between morphisms of topoi `Sh(K) ⟶ Sh(J)`;
- core/canonical owner: the functor-category Hom type between direct images, `(f _* ⟶ g _*)`;
- bridge/view: a ringed-topos `2`-morphism is this same natural transformation together with the
  extra structure-sheaf compatibility condition, so no additional owner is needed here.

Primitive data are only the two morphisms of topoi `f` and `g`. The underlying `2`-morphism is
already canonically the natural-transformation type between their pushforward functors, so this
item should remain a direct recall rather than introducing a parallel alias or wrapper structure.
-/
/- Definition 7.36.1: for morphisms of topoi `f, g : Sh(K) ⟶ Sh(J)`, a `2`-morphism from `f` to
`g` is a transformation of functors `f_* ⟶ g_*`; in mathlib notation this is the canonical type
`f _* ⟶ g _*`. -/
#check ((show Sheaf K (Type w) ⥤ Sheaf J (Type w) from f _*) ⟶
  (show Sheaf K (Type w) ⥤ Sheaf J (Type w) from g _*))

end CategoryTheory
