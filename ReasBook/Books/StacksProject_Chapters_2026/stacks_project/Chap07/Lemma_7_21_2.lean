module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_21_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe t u₁ u₂ u₃ v₁ v₂ v₃

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
variable (u : C ⥤ D) (v : D ⥤ E)
variable [Functor.IsCocontinuous u J K] [Functor.IsCocontinuous v K L]

/- Domain-style sampling for Lemma 7.21.2:
- primary domain: cocontinuous functors between sites and their induced direct-image functors on
  sheaf categories;
- sampled owner API:
  `CategoryTheory.isCocontinuous_comp`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the textbook statement that direct images for cocontinuous functors compose;
  `core/canonical`: `Functor.sheafPushforwardCocontinuous` for `A`-valued sheaves;
  `bridge/view`: the composition isomorphism for that owner, parallel to the continuous-side
  owner theorem in mathlib.

Primitive data are just the cocontinuous functors and the right Kan extension hypotheses for
`A`-valued presheaves. The composition isomorphism is derived API from that owner abstraction, so
the public statement should live at the owner level for arbitrary coefficients `A`, not only at the
specialization `A = Type t`.
-/

/- Lemma 7.21.2: the composite of two cocontinuous functors between sites is again
cocontinuous. -/
recall CategoryTheory.isCocontinuous_comp

namespace CategoryTheory.Functor

section

variable {A : Type t} [Category A]
variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
variable [∀ F : Dᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension F]

/-- A natural isomorphism between cocontinuous functors of sites induces the corresponding
isomorphism between their sheaf pushforward functors. This is the cocontinuous analogue of
`Functor.sheafPushforwardContinuousIso`. -/
@[simps!]
noncomputable def sheafPushforwardCocontinuousIso
    {u' : C ⥤ D} (e : u ≅ u')
    [u'.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ≅
      u'.sheafPushforwardCocontinuous A J K := by
  let ranIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ≅
        (u'.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) :=
    ((u.op.ranAdjunction A).ofNatIsoLeft
        ((whiskeringLeft _ _ _).mapIso (NatIso.op e.symm))).rightAdjointUniq
      (u'.op.ranAdjunction A)
  let uPush := u.sheafPushforwardCocontinuous A J K
  let u'Push := u'.sheafPushforwardCocontinuous A J K
  let presheafIso :
      uPush ⋙ sheafToPresheaf K A ≅
        u'Push ⋙ sheafToPresheaf K A :=
    calc
      uPush ⋙ sheafToPresheaf K A ≅ sheafToPresheaf J A ⋙ u.op.ran :=
        u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K
      _ ≅ sheafToPresheaf J A ⋙ u'.op.ran :=
        isoWhiskerLeft _ ranIso
      _ ≅ u'Push ⋙ sheafToPresheaf K A :=
        (u'.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf K A) presheafIso

/-- The cocontinuous sheaf pushforward attached to a composite is the composite of the
cocontinuous sheaf pushforwards attached to the factors. -/
@[simps!]
noncomputable def sheafPushforwardCocontinuousComp
    [∀ F : Cᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ⋙
      v.sheafPushforwardCocontinuous A K L ≅
        (letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
         (u ⋙ v).sheafPushforwardCocontinuous A J L) := by
  letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
  let uPush := u.sheafPushforwardCocontinuous A J K
  let vPush := v.sheafPushforwardCocontinuous A K L
  let uvPush := (u ⋙ v).sheafPushforwardCocontinuous A J L
  let ranCompIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ⋙ (v.op.ran : (Dᵒᵖ ⥤ A) ⥤ Eᵒᵖ ⥤ A) ≅
        ((u ⋙ v).op.ran : (Cᵒᵖ ⥤ A) ⥤ Eᵒᵖ ⥤ A) :=
    (((v.op.ranAdjunction A).comp (u.op.ranAdjunction A)).ofNatIsoLeft
      (whiskeringLeftObjCompIso u.op v.op).symm).rightAdjointUniq
      ((u ⋙ v).op.ranAdjunction A)
  let presheafIso :
      (uPush ⋙ vPush) ⋙ sheafToPresheaf L A ≅
        uvPush ⋙ sheafToPresheaf L A :=
    calc
      (uPush ⋙ vPush) ⋙ sheafToPresheaf L A ≅
          uPush ⋙ (vPush ⋙ sheafToPresheaf L A) :=
        Functor.associator _ _ _
      _ ≅ uPush ⋙ (sheafToPresheaf K A ⋙ v.op.ran) :=
        isoWhiskerLeft _ (v.sheafPushforwardCocontinuousCompSheafToPresheafIso A K L)
      _ ≅ (uPush ⋙ sheafToPresheaf K A) ⋙ v.op.ran :=
        (Functor.associator _ _ _).symm
      _ ≅ (sheafToPresheaf J A ⋙ u.op.ran) ⋙ v.op.ran :=
        isoWhiskerRight (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) _
      _ ≅ sheafToPresheaf J A ⋙ (u.op.ran ⋙ v.op.ran) :=
        Functor.associator _ _ _
      _ ≅ sheafToPresheaf J A ⋙ (u ⋙ v).op.ran :=
        isoWhiskerLeft _ ranCompIso
      _ ≅ uvPush ⋙ sheafToPresheaf L A :=
        (u ⋙ v).sheafPushforwardCocontinuousCompSheafToPresheafIso A J L |>.symm
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf L A) presheafIso

/-- If `u ⋙ v` is identified with another cocontinuous functor `uv`, then the composite of the
cocontinuous sheaf pushforwards for `u` and `v` identifies with the cocontinuous sheaf
pushforward for `uv`. This is the cocontinuous analogue of
`Functor.sheafPushforwardContinuousComp'`. -/
@[simps!]
noncomputable def sheafPushforwardCocontinuousComp'
    {uv : C ⥤ E} (euv : u ⋙ v ≅ uv)
    [uv.IsCocontinuous J L]
    [∀ F : Cᵒᵖ ⥤ A, uv.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ⋙
      v.sheafPushforwardCocontinuous A K L ≅
        uv.sheafPushforwardCocontinuous A J L := by
  letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
  letI : ∀ F : Cᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension F := by
    intro F Y
    rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso F (NatIso.op euv) Y]
    infer_instance
  exact sheafPushforwardCocontinuousComp J K L u v ≪≫
    sheafPushforwardCocontinuousIso J L (u ⋙ v) euv

end

section

variable {A : Type t} [Category A]
variable [Functor.IsContinuous u J K] [Functor.IsContinuous v K L]
variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]
variable [∀ F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F]
variable [HasWeakSheafify K A] [HasWeakSheafify L A]

/-- The sheaf pullback attached to a composite of continuous functors is canonically the
composite of the corresponding sheaf pullbacks. This is the left-adjoint mate of
`Functor.sheafPushforwardContinuousComp'`. -/
@[simps!]
noncomputable def sheafPullbackComp'
    {uv : C ⥤ E} (euv : u ⋙ v ≅ uv)
    [Functor.IsContinuous uv J L]
    [∀ F : Cᵒᵖ ⥤ A, uv.op.HasLeftKanExtension F] :
    u.sheafPullback A J K ⋙ v.sheafPullback A K L ≅
      uv.sheafPullback A J L :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        (u.sheafAdjunctionContinuous A J K)
        (v.sheafAdjunctionContinuous A K L)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' euv A J K L))
    (uv.sheafAdjunctionContinuous A J L)

end

end CategoryTheory.Functor

end
