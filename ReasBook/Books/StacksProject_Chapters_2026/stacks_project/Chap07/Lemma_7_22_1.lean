module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_20_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Functor Opposite
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v)

/-
Domain-style sampling for Lemma 7.22.1:
- primary domain: sheaf-theoretic direct and inverse image constructions attached to a
  cocontinuous functor with a right adjoint;
- sampled owner API:
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`,
  `Functor.sheafPullbackCocontinuous`,
  `Functor.lanAdjunction`,
  `Adjunction.leftAdjointUniq`,
  `Adjunction.rightAdjointUniq`;
- source-facing layer: the comparison of `g_*` with pullback of underlying presheaves along the
  right adjoint, and the comparison of `g⁻¹` with the sheafification of the canonical left Kan
  extension functor `v.op.lan`;
- core/canonical owner: `u.sheafPushforwardCocontinuous (Type w) J K` and
  `u.sheafPullbackCocontinuous (Type w) J K`, together with the presheaf owner
  `v.op.lanAdjunction (Type w)`;
- bridge/view: the displayed natural isomorphisms obtained from uniqueness of left and right
  adjoints.

Primitive data are the adjunction `u ⊣ v`, the cocontinuous/Kan-extension hypotheses needed for
the pushforward owner, and the weak sheafification hypothesis needed for the pullback owner. Once
`adj : u ⊣ v` is fixed, the Kan-extension existence assumptions are derived locally from the
induced adjunction on presheaf precomposition, so they should not remain in the public theorem
headers. The public declarations below are derived bridge isomorphisms, so they should reuse
those owner functors rather than restating their raw sheafification formulas or introducing a
public chosen left adjoint in place of the canonical `v.op.lan`.
-/

section Pushforward

variable [u.IsCocontinuous J K]
variable (K)

theorem hasPointwiseRightKanExtension_of_adjunction
    (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v) :
    ∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P := fun P ↦ by
  intro Y
  change HasLimit (StructuredArrow.proj Y u.op ⋙ P)
  let _ : ∀ X : Dᵒᵖ, HasInitial (StructuredArrow X u.op) :=
    let h : u.op.IsRightAdjoint := Adjunction.isRightAdjoint (adj.op)
    isRightAdjoint_iff_hasInitial_structuredArrow.mp h
  infer_instance

/-- Lemma 7.22.1 (1): for a cocontinuous functor `u` with right adjoint `v`, the direct image of a
sheaf along the morphism of topoi associated to `u` is canonically the pullback of the underlying
presheaf along `v`; equivalently, its value at `V` is `ℱ(v.obj V)`. -/
noncomputable def sheafPushforwardCocontinuousRightAdjointIso
    (ℱ : Sheaf J (Type w)) :
    letI := hasPointwiseRightKanExtension_of_adjunction u v adj
    ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).1 ≅
      v.op ⋙ ℱ.1 :=
  by
    letI := hasPointwiseRightKanExtension_of_adjunction u v adj
    exact
      (u.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type w) J K).app ℱ ≪≫
    ((u.op.ranAdjunction (Type w)).rightAdjointUniq
      (adj.op.whiskerLeft (Type w))).app ℱ.1

-- Proof sketch: the declaration `sheafPushforwardCocontinuousRightAdjointIso` is already the
-- canonical comparison isomorphism; evaluate its `hom` at `op V` and use that components of an
-- isomorphism are isomorphisms in `Type`.
/-- The canonical comparison map realizing the direct-image formula is objectwise an isomorphism. -/
theorem sheafPushforwardCocontinuousRightAdjointIso_hom_app_isIso
    (ℱ : Sheaf J (Type w)) (V : D) :
    letI := hasPointwiseRightKanExtension_of_adjunction u v adj
    IsIso
      ((sheafPushforwardCocontinuousRightAdjointIso K u v adj ℱ).hom.app (op V)) := by
  letI := hasPointwiseRightKanExtension_of_adjunction u v adj
  infer_instance

end Pushforward

section Pullback

variable [HasWeakSheafify J (Type w)]

theorem hasPointwiseLeftKanExtension_of_adjunction
    (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v) :
    ∀ P : Dᵒᵖ ⥤ Type w, v.op.HasPointwiseLeftKanExtension P := fun P ↦ by
  intro Y
  change HasColimit (CostructuredArrow.proj v.op Y ⋙ P)
  let _ : ∀ X : Cᵒᵖ, HasTerminal (CostructuredArrow v.op X) :=
    let h : v.op.IsLeftAdjoint := Adjunction.isLeftAdjoint (adj.op)
    isLeftAdjoint_iff_hasTerminal_costructuredArrow.mp h
  infer_instance

/-- Lemma 7.22.1 (2): the canonical inverse-image owner
`u.sheafPullbackCocontinuous (Type w) J K` is objectwise the sheafification of the canonical left
Kan extension `v.op.lan`; this is the intrinsic source formula `(v_p 𝒢)^#`. -/
noncomputable def sheafifyPullbackIsoSheafifyLeftKanExtension
    (𝒢 : Sheaf K (Type w)) :
    letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
    (u.sheafPullbackCocontinuous (Type w) J K).obj 𝒢 ≅
      (presheafToSheaf J (Type w)).obj ((v.op.lan).obj 𝒢.1) :=
  by
    letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
    exact
      (presheafToSheaf J (Type w)).mapIso
        (((adj.op.whiskerLeft (Type w)).leftAdjointUniq (v.op.lanAdjunction (Type w))).app 𝒢.1)

-- Proof sketch: the declaration `sheafifyPullbackIsoSheafifyLeftKanExtension` is already an
-- isomorphism in the sheaf category, so its `hom` is automatically an isomorphism.
/-- The canonical comparison map from the cocontinuous inverse image to the sheafification of
`v.op.lan` is an isomorphism. -/
theorem sheafifyPullbackIsoSheafifyLeftKanExtension_hom_isIso
    (𝒢 : Sheaf K (Type w)) :
    letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
    IsIso
      ((sheafifyPullbackIsoSheafifyLeftKanExtension u v adj 𝒢).hom :
        (u.sheafPullbackCocontinuous (Type w) J K).obj 𝒢 ⟶
          (presheafToSheaf J (Type w)).obj ((v.op.lan).obj 𝒢.1)) := by
  -- Reuse the already-constructed comparison isomorphism in the same Kan-extension context.
  letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
  infer_instance

end Pullback

end CategoryTheory
