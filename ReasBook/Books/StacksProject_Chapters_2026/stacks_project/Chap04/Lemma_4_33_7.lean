module

public import stacks_project.Chap04.CanonicalFiberPseudofunctor

@[expose] public section

/-!
# Lemma 4.33.7

This file records the three source-text items of Lemma 4.33.7. The implementation package still
lives under `Chap04.CanonicalFiberPseudofunctor`; the declarations here are thin textbook-facing
aliases so the Stacks tags are owned by the lemma file.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace PullbackChoice

variable {p : S ⥤ C} (hc : PullbackChoice p)

/-- Lemma 4.33.7 (1): for composable morphisms `f : V ⟶ U` and `g : W ⟶ V`, a chosen pullback
system on the fibred category `p : S ⥤ C` provides the canonical isomorphism
`(g ≫ f)^* ≅ f^* ⋙ g^*` between pullback functors on the standard fibers. -/
noncomputable abbrev pullbackCompositionIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    hc.pullbackFunctor (g ≫ f) ≅ hc.pullbackFunctor f ⋙ hc.pullbackFunctor g :=
  hc.pullbackCompIso f g

/-- Lemma 4.33.7 (2): the canonical unit isomorphism
`α_U : 𝟭 (Fiber p U) ≅ (𝟙 U)^*`. -/
noncomputable abbrev pullbackIdentityIso
    (U : C) :
    𝟭 (Fiber p U) ≅ hc.pullbackFunctor (𝟙 U) :=
  hc.pullbackIdIso U

/-- Lemma 4.33.7 (3): the fiber categories, pullback functors, composition comparisons
`α_{g,f}`, and unit comparisons `α_U` assemble into a pseudofunctor `Cᵒᵖ ⥤ᵖ Cat`, i.e. into the
canonical mathlib model of a pseudofunctor to the source text's `(2,1)`-category of categories. -/
noncomputable abbrev chosenFiberPseudofunctor :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  hc.fiberPseudofunctor

end PullbackChoice

end CategoryTheory
