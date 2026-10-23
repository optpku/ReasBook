module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_21_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u v

section

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 6.31.1:
- primary domain: restriction / inverse image of presheaves and sheaves along an open inclusion in
  `TopCat`;
- sampled owner declarations:
  `TopCat.Presheaf.pullbackObjObjOfImageOpen`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`,
  `TopCat.Sheaf.stalkPullbackIso`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `Adjunction.isIso_counit_of_iso`;
- owner abstraction: the canonical owners are the pullback and stalk comparison APIs for open maps
  and open embeddings, together with the pullback-pushforward adjunction and the explicit functor
  isomorphism `j_* ⋙ j⁻¹ ≅ 𝟭` for an open inclusion; the source-facing counit-is-iso statements
  should therefore be thin companions to that owner-level comparison;
- primitive data: an open subset `U : Opens X`, together with a presheaf or sheaf on `X`;
- derived API: the objectwise and stalkwise identifications for restriction to `U`, and the
  resulting counit isomorphisms.

Source/core/bridge triage:
- `source-facing`: the Stacks specialization to the inclusion `j : U ↪ X`;
- `core/canonical`: the mathlib and chapter owners above;
- `bridge/view`: only the counit-is-iso clauses remain as local declarations. -/

/- Lemma 6.31.1 (1): for an open inclusion `j : U ↪ X`, the presheaf pullback of `ℱ` evaluates on
an open `V ⊆ U` as the value of `ℱ` on the same open subset viewed in `X`. This is exactly the
open-inclusion specialization of the canonical owner
`TopCat.Presheaf.pullbackObjObjOfImageOpen`. -/
recall TopCat.Presheaf.pullbackObjObjOfImageOpen

/- Lemma 6.31.1 (2): for a sheaf `𝒢` on `X`, the inverse-image sheaf along the open inclusion
`j : U ↪ X` is given on an open `V ⊆ U` by the sections of `𝒢` on the same open viewed in `X`.
This is the objectwise specialization of the open-embedding owner
`Topology.IsOpenEmbedding.sheafPullbackIso`. -/
recall Topology.IsOpenEmbedding.sheafPullbackIso

/- Lemma 6.31.1 (3): for `x ∈ U`, the stalk of the inverse-image sheaf `j⁻¹𝒢` at `x` is
canonically identified with the stalk of `𝒢` at the corresponding point of `X`. This is exactly
the chapter owner `TopCat.Sheaf.stalkPullbackIso`, specialized to `Opens.inclusion' U`. -/
recall TopCat.Sheaf.stalkPullbackIso

private noncomputable def openSubsetPresheafPushforwardPullbackIso
    {C : Type v} [Category.{u} C] [CategoryTheory.Limits.HasColimits C] (U : Opens X) :
    TopCat.Presheaf.pushforward C U.inclusion' ⋙ TopCat.Presheaf.pullback C U.inclusion' ≅
      𝟭 ((TopCat.of U).Presheaf C) := by
  let openFunctor : Opens (TopCat.of U) ⥤ Opens X := U.isOpenEmbedding.functor
  let eComp : openFunctor.op ⋙ (Opens.map U.inclusion').op ≅
      𝟭 ((Opens (TopCat.of U))ᵒᵖ) :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by simp [openFunctor]))
      (fun {V W} i ↦ by
        apply Subsingleton.elim)
  change (Functor.whiskeringLeft _ _ _).obj (Opens.map U.inclusion').op ⋙
      TopCat.Presheaf.pullback C U.inclusion' ≅ _
  exact
    Functor.isoWhiskerLeft _ (IsOpenMap.pullbackIso U.isOpenEmbedding.isOpenMap) ≪≫
      (Functor.whiskeringLeftObjCompIso openFunctor.op
        (Opens.map U.inclusion').op).symm ≪≫
      (Functor.whiskeringLeft _ _ _).mapIso eComp ≪≫
      Functor.whiskeringLeftObjIdIso

private noncomputable def openSubsetSheafPushforwardSheafPullbackIso
    (U : Opens X) :
    TopCat.Sheaf.pushforward (Type u) U.inclusion' ⋙ U.isOpenEmbedding.sheafPullback (Type u) ≅
      𝟭 ((TopCat.of U).Sheaf (Type u)) := by
  let openFunctor : Opens (TopCat.of U) ⥤ Opens X := U.isOpenEmbedding.functor
  let inclusionMap : Opens X ⥤ Opens (TopCat.of U) := Opens.map U.inclusion'
  let J : GrothendieckTopology (Opens (TopCat.of U)) := Opens.grothendieckTopology (TopCat.of U)
  let K : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  haveI : openFunctor.IsContinuous J K := by
    simpa [openFunctor, J, K] using U.isOpenEmbedding.functor_isContinuous
  haveI : inclusionMap.IsContinuous K J := by
    apply Functor.isContinuous_of_coverPreserving
    · simpa [inclusionMap, J, K] using compatiblePreserving_opens_map U.inclusion'
    · simpa [inclusionMap, J, K] using coverPreserving_opens_map U.inclusion'
  haveI : (openFunctor ⋙ inclusionMap).IsContinuous J J := by
    simpa [openFunctor, inclusionMap, J, K] using
      (Functor.isContinuous_comp openFunctor inclusionMap J K J)
  let eComp : openFunctor ⋙ inclusionMap ≅ 𝟭 (Opens (TopCat.of U)) :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by
        change inclusionMap.obj (openFunctor.obj V) = V
        exact map_functor_eq V))
      (fun {V W} i ↦ by
        apply Subsingleton.elim)
  simpa [TopCat.Sheaf.pushforward, Topology.IsOpenEmbedding.sheafPullback, openFunctor,
    inclusionMap, J, K] using
    (openFunctor.sheafPushforwardContinuousComp inclusionMap (Type u) J K J ≪≫
      Functor.sheafPushforwardContinuousId' eComp (Type u) J)

private noncomputable def openSubsetSheafPushforwardPullbackIso
    (U : Opens X) :
    TopCat.Sheaf.pushforward (Type u) U.inclusion' ⋙ TopCat.Sheaf.pullback (Type u) U.inclusion' ≅
      𝟭 ((TopCat.of U).Sheaf (Type u)) :=
  Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type u) U.inclusion')
    (U.isOpenEmbedding.sheafPullbackIso (Type u)) ≪≫
      openSubsetSheafPushforwardSheafPullbackIso U

/-- Lemma 6.31.1 (1): on presheaves over `U`, the counit `j_p j_* ⟶ 𝟭` is an isomorphism. -/
theorem openSubsetPresheafPullbackPushforwardCounit_isIso
    {C : Type v} [Category.{u} C] [CategoryTheory.Limits.HasColimits C] (U : Opens X) :
    IsIso
      (TopCat.Presheaf.pullbackPushforwardAdjunction C U.inclusion').counit := by
  let _ :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction C U.inclusion').isIso_counit_of_iso
      (openSubsetPresheafPushforwardPullbackIso U)
  infer_instance

/-- Lemma 6.31.1 (2): on sheaves over `U`, the counit `j⁻¹ j_* ⟶ 𝟭` is an isomorphism. -/
theorem openSubsetSheafPullbackPushforwardCounit_isIso
    (U : Opens X) :
    IsIso
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) U.inclusion').counit := by
  let _ :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) U.inclusion').isIso_counit_of_iso
      (openSubsetSheafPushforwardPullbackIso U)
  infer_instance

end
