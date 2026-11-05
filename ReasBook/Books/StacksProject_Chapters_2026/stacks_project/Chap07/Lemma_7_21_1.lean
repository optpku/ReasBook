module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_15_1_Topoi
public import stacks_project.Chap07.Lemma_7_20_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.21.1:
- primary domain: morphisms of topoi induced by cocontinuous functors of sites;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `Functor.sheafPullbackCocontinuous_exact`;
- source-facing layer: the cocontinuous-functor specialization producing a morphism
  `Sh(J) ⟶ Sh(K)`;
- core/canonical owner: `MorphismOfTopoiIn`, with constructor style already set by
  `Functor.morphismOfTopoiInOfContinuous`;
- bridge/view: the simp lemmas identifying `g_*` and `g⁻¹` with the cocontinuous
  pushforward/pullback functors.

Primitive data are just the cocontinuous functor and the sheafification/right-Kan-extension
hypotheses. The adjunction and left exactness are derived from the owner declarations in
Lemma 7.20.3, so the public API should reuse those rather than restating them as separate local
data.
-/

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsCocontinuous J K] [HasSheafify J (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]

/-- Lemma 7.21.1: a cocontinuous functor of sites `u : C ⥤ D` determines a morphism of topoi
`g : Sh(J) ⟶ Sh(K)` whose direct image is `u.sheafPushforwardCocontinuous` and whose inverse
image is the sheafified pullback `u.sheafPullbackCocontinuous J K`. -/
def morphismOfTopoiInOfCocontinuous
    : MorphismOfTopoiIn K J where
  inverseImageFunctor :=
    (LeftExactFunctor.ofExact (Sheaf K (Type w)) (Sheaf J (Type w))).obj <|
      let _ : PreservesFiniteLimits (u.sheafPullbackCocontinuous (Type w) J K) :=
        (u.sheafPullbackCocontinuous_exact J K).1
      let _ : PreservesFiniteColimits (u.sheafPullbackCocontinuous (Type w) J K) :=
        (u.sheafPullbackCocontinuous_exact J K).2
      ExactFunctor.of (u.sheafPullbackCocontinuous (Type w) J K)
  pushforward := u.sheafPushforwardCocontinuous (Type w) J K
  adjunction := u.sheafPullbackCocontinuousAdjunction J K

-- Proof sketch: unfold `morphismOfTopoiInOfCocontinuous`; the direct-image field was defined to
-- be `u.sheafPushforwardCocontinuous (Type w) J K`.
/-- The direct-image functor of `morphismOfTopoiInOfCocontinuous` is the cocontinuous sheaf
pushforward functor. -/
@[simp] theorem morphismOfTopoiInOfCocontinuous_pushforward :
    (u.morphismOfTopoiInOfCocontinuous J K) _* =
      u.sheafPushforwardCocontinuous (Type w) J K := rfl

-- Proof sketch: unfold `morphismOfTopoiInOfCocontinuous`; the inverse-image field was defined to
-- be `u.sheafPullbackCocontinuous J K`.
/-- The inverse-image functor of `morphismOfTopoiInOfCocontinuous` is the sheafified inverse-image
functor attached to the cocontinuous functor. -/
@[simp] theorem morphismOfTopoiInOfCocontinuous_inverseImage :
    (u.morphismOfTopoiInOfCocontinuous J K)⁻¹ =
      u.sheafPullbackCocontinuous (Type w) J K := by
  -- The inverse-image notation is the stored left-exact functor, so this is definitional.
  rfl

-- Proof sketch: unfold `morphismOfTopoiInOfCocontinuous`; its `adjunction` field was defined to
-- be `u.sheafPullbackCocontinuousAdjunction J K`.
/-- The cocontinuous morphism of topoi is defined using the canonical adjunction between the
sheafified pullback and pushforward functors. -/
theorem morphismOfTopoiInOfCocontinuous_spec :
    (u.morphismOfTopoiInOfCocontinuous J K).adjunction =
      u.sheafPullbackCocontinuousAdjunction J K := by
  -- The adjunction field was assigned directly in the defining structure.
  rfl

end CategoryTheory.Functor
