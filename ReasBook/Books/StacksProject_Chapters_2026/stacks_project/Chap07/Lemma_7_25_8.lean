module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_21_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u₁ v₁ uA vA

noncomputable section

section

variable {C : Type u₁} [Category.{v₁} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)

/- Domain-style sampling for Lemma 7.25.8:
- primary domain: relocalization between slice sites and the induced sheaf functors;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPushforwardCocontinuousComp'`,
  `Functor.sheafPullbackComp'`,
  `Functor.sheafPullback`,
  `GrothendieckTopology.overMapPullback`;
- source-facing layer: the textbook comparison between localization at `V`, localization at `U`,
  and relocalization along `f`;
- core/canonical owner: the specialized slice-site functors `J.overPullback`, `J.overMapPullback`,
  and the canonical comparison
  `Functor.sheafPushforwardContinuousComp' (Over.mapForget f)`;
- bridge/view: the direct-image and lower-shriek functors are the cocontinuous pushforward and
  pullback owners attached to `Over.map f` and `Over.forget U`.

Primitive data are only the site `J` and the morphism `f`. The inverse-image comparison is derived
from the canonical owner isomorphism, the direct-image comparison is definitional, and the
lower-shriek comparison is the direct specialization of the canonical pullback-composition owner
`Functor.sheafPullbackComp'`.
-/

variable (A : Type uA) [Category.{vA} A]

/- Lemma 7.25.8: the inverse-image comparison `j_U⁻¹ ⋙ j⁻¹ ≅ j_V⁻¹` is exactly the specialized
canonical owner `Functor.sheafPushforwardContinuousComp'` for the triangle
`Over.map f ⋙ Over.forget U ≅ Over.forget V`. -/
#check
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget f) A (J.over V) (J.over U) J :
    J.overPullback A U ⋙ J.overMapPullback A f ≅ J.overPullback A V)

/- The direct-image comparison `j_* ⋙ j_{U*} ≅ j_{V*}` is the specialized owner
`Functor.sheafPushforwardCocontinuousComp'` for the canonical isomorphism
`Over.mapForget f : Over.map f ⋙ Over.forget U ≅ Over.forget V`; no chapter-local wrapper is
needed. -/
section DirectImage

variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.forget V).op.HasPointwiseRightKanExtension F]

#check
  (Functor.sheafPushforwardCocontinuousComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
      (Over.map f).sheafPushforwardCocontinuous A (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPushforwardCocontinuous A (J.over U) J ≅
        (Over.forget V).sheafPushforwardCocontinuous A (J.over V) J)

end DirectImage

/- The lower-shriek comparison `j_! ⋙ j_{U!} ≅ j_{V!}` is exactly the slice specialization of the
canonical owner `Functor.sheafPullbackComp'` for the triangle
`Over.map f ⋙ Over.forget U ≅ Over.forget V`. -/
section LowerShriek

variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasLeftKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasLeftKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ A, (Over.forget V).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) A] [HasWeakSheafify J A]

#check
  (Functor.sheafPullbackComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
      (Over.map f).sheafPullback A (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPullback A (J.over U) J ≅
        (Over.forget V).sheafPullback A (J.over V) J)

end LowerShriek

end
