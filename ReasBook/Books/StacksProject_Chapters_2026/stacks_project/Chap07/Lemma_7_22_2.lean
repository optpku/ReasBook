module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_14_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v)

/- Domain-style sampling for Lemma 7.22.2:
- primary domain: adjunctions between Grothendieck sites and the induced direct-image functors on
  sheaves;
- sampled owner API:
  `RepresentablyFlat.of_isRightAdjoint`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for a continuous right adjoint `v` with left adjoint `u`;
  `core/canonical`: the owner class `IsMorphismOfSites K J v` and the sheaf pushforward owners
  attached to `u` and `v`;
  `bridge/view`: the right-adjoint-specific theorem below, and the comparison isomorphism between
  the two direct-image functors.

Primitive data are the adjunction `u ⊣ v`, continuity of `v`, and the right-Kan-extension
hypotheses needed for the `A`-valued cocontinuous pushforward owner, together with the explicit
cocontinuity owner on `u` needed to form `u.sheafPushforwardCocontinuous`. Representable
flatness and the site-morphism structure of `v` are derived from the owner API, so they should
remain internal instance plumbing rather than a parallel public wrapper.
-/

-- Proof sketch: after composing both direct-image functors with `sheafToPresheaf K (Type w)`,
-- the continuous pushforward of `v` is definitionally pullback along `v.op`, while the
-- cocontinuous pushforward of `u` is canonically identified with that same presheaf functor by
-- `Adjunction.rightAdjointUniq` applied to `u.op.ranAdjunction` and `adj.op.whiskerLeft`. Since
-- `sheafToPresheaf K (Type w)` is fully faithful, this presheaf comparison lifts uniquely to the
-- claimed isomorphism of sheaf functors.
/-- Lemma 7.22.2: if `u : \mathcal C \to \mathcal D` is cocontinuous with right adjoint
`v : \mathcal D \to \mathcal C` and `v` is continuous, then `v` defines the morphism of sites
`(\mathcal C, J) \to (\mathcal D, K)`, and the direct-image functor of its associated morphism of
topoi is canonically isomorphic to the cocontinuous direct-image functor attached to `u`, i.e. to
`g_*`. In the canonical API this cocontinuity is supplied by the explicit owner
`u.IsCocontinuous J K`. -/
noncomputable def continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    by
      let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
      let _ : IsMorphismOfSites K J v := inferInstance
      exact
        v.sheafPushforwardContinuous A K J ≅
          u.sheafPushforwardCocontinuous A J K := by
  let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
  let _ : IsMorphismOfSites K J v := inferInstance
  let e : u.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op :=
    (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) ≪≫
      Functor.isoWhiskerLeft (sheafToPresheaf J A)
        (Adjunction.rightAdjointUniq (u.op.ranAdjunction A) (adj.op.whiskerLeft A))
  exact ((fullyFaithfulSheafToPresheaf K A).whiskeringRight (Sheaf J A)).preimageIso <|
    (v.sheafPushforwardContinuousCompSheafToPresheafIso A K J) ≪≫ e.symm

/-- The forward comparison morphism from the continuous direct image along `v` to the
cocontinuous direct image along `u` is an isomorphism. -/
-- Proof sketch: this morphism is the `hom` of the canonical isomorphism
-- `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`.
theorem continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward_hom_isIso
    (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    IsIso
      ((continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
          u v A adj).hom :
        v.sheafPushforwardContinuous A K J ⟶
          u.sheafPushforwardCocontinuous A J K) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism.
  infer_instance

end CategoryTheory
