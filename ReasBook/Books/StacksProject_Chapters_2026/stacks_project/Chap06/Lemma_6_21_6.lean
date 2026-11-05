module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Topology.Sheaves.Functors
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe w v u

/- Domain-style sampling for Lemma 6.21.6:
- primary domain: inverse image functors on presheaves and sheaves over topological spaces;
- sampled owner declarations:
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `Adjunction.leftAdjointCompIso`,
  `Adjunction.conjugateEquiv_leftAdjointCompIso_inv`,
  and the raw definitional equality
  `TopCat.{Presheaf,Sheaf}.pushforward A (f ≫ g) =
    TopCat.{Presheaf,Sheaf}.pushforward A f ⋙
      TopCat.{Presheaf,Sheaf}.pushforward A g`;
- owner abstraction: the canonical owner is `Adjunction.leftAdjointCompIso`, applied to the
  pullback-pushforward adjunctions and the definitional equality of the right-adjoint
  pushforward functors under composition;
- primitive data: composable continuous maps `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the source-facing comparison isomorphisms
  `TopCat.Sheaf.pullbackComp` and `TopCat.Presheaf.pullbackComp`.

Source/core/bridge triage:
- `source-facing`: inverse image along a composite continuous map agrees with the composite inverse
  image functor; the textbook item is the `Type u` specialization;
- `core/canonical`: `Adjunction.leftAdjointCompIso`;
- `bridge/view`: the namespace-specialized `pullbackComp` declarations below, kept because the
  immediate downstream files use this source-facing vocabulary directly. -/

/-- Helper for Lemma 6.21.6: if the composite right adjoint is definitionally equal to a given
right adjoint, then uniqueness of left adjoints yields the corresponding comparison isomorphism on
left adjoints. -/
public noncomputable def leftAdjointCompIsoOfEq
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)
    (h : G₂₀ = G₂₁ ⋙ G₁₀) :
    F₀₁ ⋙ F₁₂ ≅ F₀₂ :=
  -- Package the definitional equality of right adjoints as an isomorphism, then invoke
  -- uniqueness of left adjoints for the two adjunction presentations.
  Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ (eqToIso h.symm)

namespace TopCat.Sheaf

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- Lemma 6.21.6 (1), in canonical owner form: pullback of sheaves along a composite continuous
map is canonically isomorphic to the composite pullback functor. The Stacks statement is the
specialization `A = Type u`. -/
def pullbackComp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback A g ⋙ pullback A f ≅ pullback A (f ≫ g) :=
  -- Follow the source proof: both functors are left adjoint to the same pushforward functor,
  -- since pushforward along a composite is definitionally the composite pushforward.
  leftAdjointCompIsoOfEq
    (pullbackPushforwardAdjunction A g)
    (pullbackPushforwardAdjunction A f)
    (pullbackPushforwardAdjunction A (f ≫ g))
    (show pushforward A (f ≫ g) = pushforward A f ⋙ pushforward A g from rfl)

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {C : Type u} [Category.{w} C] [HasColimits C]

/-- Lemma 6.21.6 (2), in canonical owner form: pullback of presheaves along a composite
continuous map is canonically isomorphic to the composite pullback functor. The Stacks statement
is the specialization `C = Type u`. -/
def pullbackComp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback C g ⋙ pullback C f ≅ pullback C (f ≫ g) :=
  -- The presheaf case is the same adjunction-uniqueness argument, now using the presheaf
  -- pullback-pushforward adjunctions.
  leftAdjointCompIsoOfEq
    (pullbackPushforwardAdjunction C g)
    (pullbackPushforwardAdjunction C f)
    (pullbackPushforwardAdjunction C (f ≫ g))
    (show pushforward C (f ≫ g) = pushforward C f ⋙ pushforward C g from rfl)

end TopCat.Presheaf
