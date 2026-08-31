module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section Continuous

variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [G.IsContinuous J K]

/-- The source-facing comparison from sheafifying after precomposition along a continuous functor
to precomposing a sheafified presheaf. -/
def pushforwardContinuousSheafificationComparison :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj G.op ⋙ presheafToSheaf J (Type w) ⟶
      presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K where
  app F :=
    ObjectProperty.homMk <|
      sheafifyLift J
        (Functor.whiskerLeft G.op (toSheafify K F))
        ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj F).property
  naturality η := by
    intro Y f
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj Y).property
    change toSheafify J (G.op ⋙ η) ≫
        sheafifyMap J (Functor.whiskerLeft G.op f) ≫
        sheafifyLift J
          (Functor.whiskerLeft G.op (toSheafify K Y))
          ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj Y).property =
      toSheafify J (G.op ⋙ η) ≫
        sheafifyLift J
          (Functor.whiskerLeft G.op (toSheafify K η))
          ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj η).property ≫
        ((G.sheafPushforwardContinuous (Type w) J K).map ((presheafToSheaf K (Type w)).map f)).hom
    rw [← Category.assoc]
    rw [← toSheafify_naturality J (Functor.whiskerLeft G.op f)]
    rw [Category.assoc, toSheafify_sheafifyLift]
    rw [← Category.assoc]
    rw [toSheafify_sheafifyLift]
    change Functor.whiskerLeft G.op f ≫
        Functor.whiskerLeft G.op (toSheafify K Y) =
      Functor.whiskerLeft G.op (toSheafify K η) ≫
        Functor.whiskerLeft G.op (((presheafToSheaf K (Type w)).map f).hom)
    ext X a
    let h :=
      congrArg
        (fun α ↦ α.app (G.op.obj X))
        (toSheafify_naturality K f)
    exact congrFun h a

/-- For a continuous and cocontinuous functor of sites with pointwise right Kan extensions, the
source-facing sheafification comparison is an isomorphism. -/
theorem pushforwardContinuousSheafificationComparison_isIso
    [G.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F] :
    IsIso (G.pushforwardContinuousSheafificationComparison J K) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  -- Compare the local component with mathlib's canonical sheafification-compatibility isomorphism.
  have hcomp :
      (G.pushforwardContinuousSheafificationComparison J K).app F =
        (G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F := by
    apply Sheaf.hom_ext
    change sheafifyLift J
        (Functor.whiskerLeft G.op (toSheafify K F))
        ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj F).property =
      ((G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F).hom
    simpa using
      (G.pushforwardContinuousSheafificationCompatibility_hom_app_hom (Type w) J K F).symm
  rw [hcomp]
  exact
    (inferInstance :
      IsIso ((G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F))

section CocontinuousBridge

variable [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F]

/-- Under the stronger cocontinuous/right-Kan-extension hypotheses, the source-facing comparison
agrees componentwise with mathlib's canonical compatibility isomorphism. -/
theorem pushforwardContinuousSheafificationCompatibility_hom_app_eq_comparison_app
    (F : Dᵒᵖ ⥤ Type w) :
    (G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F =
      (G.pushforwardContinuousSheafificationComparison J K).app F := by
  apply Sheaf.hom_ext
  change ((G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F).hom =
      sheafifyLift J
        (Functor.whiskerLeft G.op (toSheafify K F))
        ((presheafToSheaf K (Type w) ⋙ G.sheafPushforwardContinuous (Type w) J K).obj F).property
  simpa using
    G.pushforwardContinuousSheafificationCompatibility_hom_app_hom (Type w) J K F

end CocontinuousBridge

end Continuous

/- Domain-style sampling for Lemma 7.20.3:
- primary domain: sheaves on sites under a cocontinuous functor, expressed through sheafification
  and right Kan extension;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`,
  `sheafificationAdjunction`;
- source-facing layer: the set-valued sheafified pullback along a cocontinuous functor, owned here
  by `G.sheafPullbackCocontinuous J K`;
- core/canonical ingredients: `G.op.ranAdjunction (Type w)` together with
  `sheafificationAdjunction J (Type w)`;
- bridge/view: the adjunction identifying the constructed pullback with the canonical
  cocontinuous pushforward as right adjoint.

Primitive data are the cocontinuous functor and the right Kan extension hypotheses for
`Type`-valued presheaves. The pullback functor is the source-facing owner for this item, while its
set-valued adjunction and exactness statements are derived API from the canonical right-Kan-
extension and sheafification owners.
-/

/-- The pullback of sheaves along a cocontinuous functor, obtained by precomposing the
underlying presheaf and then sheafifying. -/
def sheafPullbackCocontinuous
    (G : C ⥤ D)
    (A : Type (w + 1)) [Category.{w} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J A] :
    Sheaf K A ⥤ Sheaf J A :=
  sheafToPresheaf K A ⋙
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙
    presheafToSheaf J A

section Cocontinuous

variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F]

/-- Lemma 7.20.3 (1): for a cocontinuous functor of sites, the set-valued sheafified pullback
is left adjoint to the cocontinuous direct-image functor on sheaves. -/
noncomputable def sheafPullbackCocontinuousAdjunction
    [HasWeakSheafify J (Type w)] :
    G.sheafPullbackCocontinuous (Type w) J K ⊣ G.sheafPushforwardCocontinuous (Type w) J K :=
  ((G.op.ranAdjunction (Type w)).comp (sheafificationAdjunction J (Type w))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K (Type w)) (Functor.FullyFaithful.id _)
    (Iso.refl _)
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type w) J K).symm

-- Proof sketch: reinterpret the explicit adjunction object
-- `sheafPullbackCocontinuousAdjunction` via its bundled `IsLeftAdjoint` structure.
/-- The cocontinuous sheafified pullback functor is canonically a left adjoint. -/
theorem sheafPullbackCocontinuousAdjunction_isLeftAdjoint
    [HasWeakSheafify J (Type w)] :
    (G.sheafPullbackCocontinuous (Type w) J K).IsLeftAdjoint := by
  -- The adjunction was constructed above, so we expose its bundled left-adjoint structure.
  exact (G.sheafPullbackCocontinuousAdjunction J K).isLeftAdjoint

-- Proof sketch: the functor is right exact because it is a left adjoint by
-- `sheafPullbackCocontinuousAdjunction`; it is left exact because it is the composite of the
-- left exact sheafification functor with precomposition by `G.op`, which is a right adjoint.
/-- Lemma 7.20.3 (2): the cocontinuous pullback functor on sheaves of sets is exact. -/
theorem sheafPullbackCocontinuous_exact
    [HasSheafify J (Type w)] :
    exactFunctor (Sheaf K (Type w)) (Sheaf J (Type w))
      (G.sheafPullbackCocontinuous (Type w) J K) := by
  let _ : (G.sheafPullbackCocontinuous (Type w) J K).IsLeftAdjoint :=
    G.sheafPullbackCocontinuousAdjunction_isLeftAdjoint J K
  let _ : PreservesFiniteLimits (G.sheafPullbackCocontinuous (Type w) J K) :=
    by
      dsimp [sheafPullbackCocontinuous]
      letI : PreservesFiniteLimits
          (sheafToPresheaf K (Type w) ⋙
            (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj G.op) :=
        comp_preservesFiniteLimits _ _
      letI : PreservesFiniteLimits
          ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj G.op ⋙
            presheafToSheaf J (Type w)) :=
        comp_preservesFiniteLimits _ _
      exact comp_preservesFiniteLimits _ _
  rw [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

end Cocontinuous

end CategoryTheory.Functor
