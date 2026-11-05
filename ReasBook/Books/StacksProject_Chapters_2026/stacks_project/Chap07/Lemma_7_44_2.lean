module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.sheafPullbackConstruction

universe u₁ u₂ v w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable {A : Type w} [Category.{max u₁ u₂ v} A]
variable {FA : A → A → Type (max u₁ u₂ v)} {CA : A → Type (max u₁ u₂ v)}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-
Domain-style sampling for Lemma 7.44.2:
- primary domain: direct- and inverse-image functors on presheaves and sheaves of algebraic
  structures, together with their compatibility with the forgetful functor to sets;
- sampled owner API:
  `Functor.lanAdjunction`,
  `Functor.lanCompIsoOfPreserves`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma asserting that presheaf/sheaf inverse and direct image for
  algebraic structures are the expected adjoint functors and commute with forgetting to sets;
  `core/canonical`: the presheaf left Kan extension owner `u.op.lan`, the sheaf pushforward owner
  `u.sheafPushforwardContinuous A J K` under continuity, and the sheaf pullback owner
  `u.sheafPullback A J K` under the standard continuity/Kan-extension/sheafification hypotheses;
  `bridge/view`: `Functor.lanCompIsoOfPreserves`, `sheafComposeNatIso`, and
  `Functor.sheafPullbackConstruction.sheafPullbackIso`, which transport the forgetful functor
  across the canonical owners.

Primitive data are only the functor `u`, the site topologies, the existence of the relevant left
Kan extensions, and the preservation hypotheses letting `forget A` commute with Kan extension and
sheafification. The adjunctions and forget-comparison maps are derived API owned upstream, so this
file should reuse those owners directly and keep only the source-facing comparison statements.
-/

section PresheafAdjunction

variable (u : C ⥤ D)
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]

/- Canonical presheaf adjunction recall: on presheaves of `A`-valued algebraic structures, the
pullback functor `uₚ`, realized as left Kan extension along `u.op`, is left adjoint to the
pushforward functor `u^p`, realized as precomposition by `u.op`. -/
recall Functor.lanAdjunction

end PresheafAdjunction

-- Proof sketch: both composites act on a presheaf `P : Dᵒᵖ ⥤ A` by precomposition with `u.op`
-- and then objectwise application of the forgetful functor `forget A`, so the two functors agree
-- definitionally.
/-- Lemma 7.44.2 (1): presheaf pushforward, i.e. precomposition with `u.op`, commutes with
taking the underlying set-valued presheaf. Applied to algebraic-structure categories, this is the
compatibility of direct image with the underlying presheaf of sets. -/
theorem presheaf_pushforward_forget
    (u : C ⥤ D) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op ⋙
        (whiskeringRight Cᵒᵖ A (Type (max u₁ u₂ v))).obj (forget A) =
      (whiskeringRight Dᵒᵖ A (Type (max u₁ u₂ v))).obj (forget A) ⋙
        (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v))).obj u.op := rfl

section PresheafForgetPullback

variable (u : C ⥤ D)
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]

/- Canonical presheaf pullback/forget recall: for presheaves of algebraic structures, forgetting to
sets commutes with the presheaf pullback `uₚ`, i.e. the left Kan extension along `u.op`, via the
canonical comparison isomorphism. -/
recall Functor.lanCompIsoOfPreserves

end PresheafForgetPullback

section Sheaves

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D)

section SheafAdjunction

variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K A]

/- Canonical sheaf adjunction recall: on sheaves of `A`-valued algebraic structures, the
inverse-image functor `f⁻¹`, realized as `u.sheafPullback A J K`, is left adjoint to the
direct-image functor `f_* = u.sheafPushforwardContinuous A J K`. -/
recall Functor.sheafAdjunctionContinuous

end SheafAdjunction

-- Proof sketch: `u.sheafPushforwardContinuous` is defined by precomposition with `u.op`, and
-- `sheafCompose` is obtained by objectwise composition with `forget A`; thus the two composites
-- agree definitionally.
/-- Lemma 7.44.2 (2): sheaf pushforward commutes with taking the underlying sheaf of sets.
Applied to algebraic-structure categories, this is the compatibility of direct image with the
underlying sheaf of sets. -/
theorem sheaf_pushforward_forget
    [u.IsContinuous J K]
    [J.HasSheafCompose (forget A)]
    [K.HasSheafCompose (forget A)] :
    u.sheafPushforwardContinuous A J K ⋙ sheafCompose J (forget A) =
      sheafCompose K (forget A) ⋙ u.sheafPushforwardContinuous (Type (max u₁ u₂ v)) J K := rfl

-- Proof sketch: realize both pullback functors by left Kan extension followed by sheafification,
-- use clause (2) to move `forget A` across the left Kan extension, and then use compatibility of
-- sheafification with `forget A` to identify the resulting set-valued sheaf.
section SheafPullbackForget

variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v), u.op.HasLeftKanExtension P]
variable [(forget A).PreservesLeftKanExtensions u.op]
variable [HasWeakSheafify K A]
variable [HasWeakSheafify K (Type (max u₁ u₂ v))]
variable [J.HasSheafCompose (forget A)]
variable [K.HasSheafCompose (forget A)]
variable [K.PreservesSheafification (forget A)]

/-
Bridge/view step: the explicit Kan-extension-and-sheafification construction of pullback commutes
with forgetting to sets via the canonical sheafification comparison `sheafComposeNatIso` and the
canonical Kan-extension comparison `(forget A).lanCompIsoOfPreserves u.op`.
-/
noncomputable def sheafPullbackConstruction_forget :
    sheafPullbackConstruction.sheafPullback u A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙
        sheafPullbackConstruction.sheafPullback u (Type (max u₁ u₂ v)) J K :=
  (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (sheafToPresheaf J A)
        (Functor.associator _ _ _ ≪≫
          isoWhiskerLeft u.op.lan
            (sheafComposeNatIso K (forget A) (sheafificationAdjunction K A)
              (sheafificationAdjunction K (Type (max u₁ u₂ v)))).symm)) ≪≫
    isoWhiskerLeft (sheafToPresheaf J A)
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight ((forget A).lanCompIsoOfPreserves u.op)
          (presheafToSheaf K (Type (max u₁ u₂ v))) ≪≫
        Functor.associator _ _ _) ≪≫
    Iso.refl _

/-- Lemma 7.44.2 (3): sheaf pullback commutes with taking the underlying sheaf of sets. Applied to
algebraic-structure categories, this is the compatibility of inverse image with the underlying
sheaf of sets. -/
noncomputable def sheaf_pullback_forget
    :
    u.sheafPullback A J K ⋙ sheafCompose K (forget A) ≅
      sheafCompose J (forget A) ⋙ u.sheafPullback (Type (max u₁ u₂ v)) J K :=
  isoWhiskerRight (sheafPullbackIso u A J K) (sheafCompose K (forget A)) ≪≫
    sheafPullbackConstruction_forget J K u ≪≫
    isoWhiskerLeft (sheafCompose J (forget A))
      (sheafPullbackIso u (Type (max u₁ u₂ v)) J K).symm

-- Proof sketch: this is the componentwise `hom ≫ inv = 𝟙` identity for the natural isomorphism
-- `sheaf_pullback_forget`.
/-- The comparison isomorphism `sheaf_pullback_forget` is componentwise invertible. -/
theorem sheaf_pullback_forget_hom_inv_app
    (ℱ : Sheaf J A) :
    ((sheaf_pullback_forget J K u).hom.app ℱ) ≫
        ((sheaf_pullback_forget J K u).inv.app ℱ) =
      𝟙 ((u.sheafPullback A J K ⋙ sheafCompose K (forget A)).obj ℱ) := by
  -- Specialize the natural-isomorphism identity to the comparison isomorphism at `ℱ`.
  simpa using Iso.hom_inv_id_app (sheaf_pullback_forget J K u) ℱ

end SheafPullbackForget

end Sheaves

end CategoryTheory

end
