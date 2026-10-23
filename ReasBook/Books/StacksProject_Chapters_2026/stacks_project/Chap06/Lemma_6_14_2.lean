module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous


@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Presheaf

/-- Helper for Lemma 6.14.2: a natural transformation between two functors which both preserve a
colimit, and which is an isomorphism on every object of the diagram, is an isomorphism on the
colimit point. -/
private theorem isIso_natTrans_app_of_isColimit
    {C : Type*} [Category C] {E : Type*} [Category E]
    {P Q : C ⥤ E} (τ : P ⟶ Q)
    {J : Type*} [SmallCategory J] {D : J ⥤ C} {c : Limits.Cocone D}
    (hP : Limits.IsColimit (P.mapCocone c)) (hQ : Limits.IsColimit (Q.mapCocone c))
    (hiso : ∀ j, IsIso (τ.app (D.obj j))) :
    IsIso (τ.app c.pt) := by
  haveI : ∀ j, IsIso ((Functor.whiskerLeft D τ).app j) := hiso
  haveI : IsIso (Functor.whiskerLeft D τ) := NatIso.isIso_of_isIso_app _
  have heq : τ.app c.pt =
      (Limits.IsColimit.coconePointsIsoOfNatIso hP hQ
        (asIso (Functor.whiskerLeft D τ))).hom := by
    apply hP.hom_ext
    intro j
    have hr := Limits.IsColimit.comp_coconePointsIsoOfNatIso_hom hP hQ
      (asIso (Functor.whiskerLeft D τ)) j
    refine Eq.trans ?_ hr.symm
    simp only [Functor.mapCocone_ι_app, asIso_hom, Functor.whiskerLeft_app]
    exact τ.naturality (c.ι.app j)
  rw [heq]
  exact (Limits.IsColimit.coconePointsIsoOfNatIso hP hQ
    (asIso (Functor.whiskerLeft D τ))).isIso_hom

private noncomputable instance presheaf_pushforward₀_preservesColimitsOfShape
    {C D : Type*} [Category C] [Category D]
    {J : Type*} [Category J]
    [Limits.HasColimitsOfShape J AddCommGrpCat.{u}]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u}) :
    Limits.PreservesColimitsOfShape J (PresheafOfModules.pushforward₀.{u} F R) where
  preservesColimit {K} :=
    { preserves := fun {c} hc => ⟨by
        haveI : ∀ {Y Z : Dᵒᵖ} (f : Y ⟶ Z),
            Limits.PreservesColimit (K ⋙ PresheafOfModules.evaluation.{u} R Z)
              (ModuleCat.restrictScalars.{u} (R.map f).hom) := fun f => by
          infer_instance
        refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X => ?_)
        change Limits.IsColimit
          ((PresheafOfModules.evaluation.{u} R (F.op.obj X)).mapCocone c)
        exact Limits.isColimitOfPreserves
          (PresheafOfModules.evaluation.{u} R (F.op.obj X)) hc⟩ }

private noncomputable instance presheaf_pullback_preservesColimitsOfShape
    {C D : Type*} [Category C] [Category D]
    {J : Type*} [Category J]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) [(PresheafOfModules.pushforward.{u} φ).IsRightAdjoint] :
    Limits.PreservesColimitsOfShape J (PresheafOfModules.pullback.{u} φ) :=
by
  let hpres := (PresheafOfModules.pullbackPushforwardAdjunction φ).leftAdjoint_preservesColimits
  exact hpres.preservesColimitsOfShape

/-
Domain-style sampling for Lemma 6.14.2:
- primary domain: change of rings for presheaves of modules and stalkwise scalar extension on a
  topological space;
- sampled owner API:
  `PresheafOfModules.pullback`,
  `PresheafOfModules.restrictScalars`,
  `PresheafOfModules.pullbackPushforwardAdjunction`,
  `ModuleCat.extendRestrictScalarsAdj`;
- best owner abstraction: presheaf-level change of rings along the canonical underlying
  ring-presheaf morphism `Functor.whiskerRight p (forget₂ CommRingCat RingCat)`;
- source/core/bridge triage:
  `source-facing`: the stalkwise base-change comparison map and its induced isomorphism;
  `core/canonical`: the change-of-rings adjunction for `PresheafOfModules` and the
    `extendScalars ⊣ restrictScalars` adjunction on stalk modules;
  `bridge/view`: forgetting commutativity from `CommRingCat` to `RingCat`.

Primitive data are only the morphism `p : 𝒪 ⟶ 𝒪'`, the `𝒪`-module presheaf `ℱ`, and the point
`x`. The underlying ring-presheaf morphism is derived support, so this file should reuse the
canonical whiskered morphism directly instead of keeping a renamed shell for it.
-/

/-- The underlying presheaf map into a restricted-scalars target. -/
public noncomputable abbrev underlyingPresheafMapToRestricted
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) :
    ℱ.presheaf ⟶ 𝒢.presheaf :=
  show ℱ.presheaf ⟶ 𝒢.presheaf from
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map φ

/-- The underlying stalk map into a restricted-scalars target. -/
public noncomputable abbrev stalkUnderlyingMapToRestricted
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) (x : X) :
    (stalkFunctor Ab x).obj ℱ.presheaf ⟶ (stalkFunctor Ab x).obj 𝒢.presheaf :=
  (stalkFunctor Ab x).map (underlyingPresheafMapToRestricted p φ)

/-- Semilinearity of the stalk map into a restricted-scalars target. -/
-- Proof sketch: the stalk map comes from a morphism of presheaf modules, so it is linear after
-- restricting scalars along the induced ring map on stalks.
public theorem stalkUnderlyingMapToRestricted_map_smul
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) (x : X) :
    ∀ (r : 𝒪.stalk x) (m : ↑(stalk ℱ.presheaf x)),
      (show ↑(stalk 𝒢.presheaf x) from
        stalkUnderlyingMapToRestricted p φ x (r • m)) =
        (show 𝒪'.stalk x from ((stalkFunctor CommRingCat x).map p) r) •
          (show ↑(stalk 𝒢.presheaf x) from
            stalkUnderlyingMapToRestricted p φ x m) := by
  intro r m
  obtain ⟨U, hxU, rU, hr⟩ := TopCat.Presheaf.germ_exist 𝒪 x r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist ℱ.presheaf x m
  let W : Opens X := U ⊓ V
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : 𝒪.obj (op W) := 𝒪.map iWU.op rU
  let mW : ℱ.obj (op W) := ℱ.map iWV.op mV
  -- Pass to a common neighborhood representative for both the scalar and the section.
  have hrW : 𝒪.germ W x hxW rW = r := by
    simpa [W, iWU, hxW, rW] using (𝒪.germ_res_apply iWU x hxW rU).trans hr
  have hmW : TopCat.Presheaf.germ ℱ.presheaf W x hxW mW = m := by
    simpa [W, iWV, hxW, mW] using
      (TopCat.Presheaf.germ_res_apply ℱ.presheaf iWV x hxW mV).trans hm
  have hsmulW :
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) = r • m := by
    rw [PresheafOfModules.germ_smul (M := ℱ) x W hxW rW mW, hrW, hmW]
  have hpW :
      (show 𝒪'.stalk x from ((stalkFunctor CommRingCat x).map p) r) =
        𝒪'.germ W x hxW (p.app (op W) rW) := by
    rw [← hrW]
    simpa [W, hxW, rW] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW p rW)
  have hmφW :
      (show ↑(stalk 𝒢.presheaf x) from stalkUnderlyingMapToRestricted p φ x m) =
        TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (op W) mW) := by
    rw [← hmW]
    simpa [stalkUnderlyingMapToRestricted, underlyingPresheafMapToRestricted, W, hxW, mW] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        (underlyingPresheafMapToRestricted p φ) mW)
  -- Evaluate the stalk map on that representative, use sectionwise linearity of `φ.app`,
  -- then translate back to the given stalk elements.
  calc
    (show ↑(stalk 𝒢.presheaf x) from stalkUnderlyingMapToRestricted p φ x (r • m))
        = TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (op W) (rW • mW)) := by
          rw [← hsmulW]
          simpa [stalkUnderlyingMapToRestricted, underlyingPresheafMapToRestricted, W, hxW, rW,
            mW] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
              (underlyingPresheafMapToRestricted p φ) (rW • mW))
    _ = TopCat.Presheaf.germ 𝒢.presheaf W x hxW (rW • φ.app (op W) mW) := by
          congr 1
          exact (φ.app (op W)).hom.map_smul rW mW
    _ = 𝒪'.germ W x hxW (p.app (op W) rW) •
          TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (op W) mW) := by
          simpa using (PresheafOfModules.germ_smul (M := 𝒢) x W hxW (p.app (op W) rW)
            (φ.app (op W) mW))
    _ = (show 𝒪'.stalk x from ((stalkFunctor CommRingCat x).map p) r) •
          (show ↑(stalk 𝒢.presheaf x) from stalkUnderlyingMapToRestricted p φ x m) := by
          rw [hpW, hmφW]

/-- Helper for Lemma 6.14.2: the stalk functor sends the identity ring-presheaf morphism to the
identity ring homomorphism on the stalk. -/
private theorem stalkFunctor_map_id_hom
    {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (((stalkFunctor CommRingCat x).map (𝟙 R)).hom) = RingHom.id (R.stalk x) := by
  exact congrArg CommRingCat.Hom.hom ((stalkFunctor CommRingCat x).map_id R)

/-- The stalk map into a restricted-scalars target induced by a morphism of presheaf modules. -/
public noncomputable def stalkModuleMapToRestrict
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢) (x : X) :
    ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) ⟶
      (ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (ModuleCat.of (𝒪'.stalk x) ↑(stalk 𝒢.presheaf x)) :=
  let restrictedTarget :
      ModuleCat (𝒪.stalk x) :=
    (ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
      (ModuleCat.of (𝒪'.stalk x) ↑(stalk 𝒢.presheaf x))
  let restrictedHom :
      ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) →ₗ[𝒪.stalk x]
        restrictedTarget :=
    { toFun := stalkUnderlyingMapToRestricted p φ x
      map_add' := fun m n ↦ by
        simpa using (stalkUnderlyingMapToRestricted p φ x).hom.map_add m n
      map_smul' := stalkUnderlyingMapToRestricted_map_smul p φ x }
  show ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) ⟶ restrictedTarget from
    ConcreteCategory.ofHom restrictedHom

/-- The canonical comparison from the extended-scalar stalk `ℱ_x ⊗[𝒪_x] 𝒪'_x` to the stalk of
the canonically pulled back presheaf. -/
noncomputable def stalkBaseChangeComparison
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
      (ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x)) ⟶
        ModuleCat.of (𝒪'.stalk x)
          ↑(stalk
            ((PresheafOfModules.pullback
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ).presheaf x) :=
  ((ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom)).homEquiv
      _ _).symm
    (stalkModuleMapToRestrict p
      (show ℱ ⟶
          (PresheafOfModules.restrictScalars
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
            ((PresheafOfModules.pullback
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ) from
        (PresheafOfModules.pullbackPushforwardAdjunction
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) x)

/-- Helper for Lemma 6.14.2: the global pullback of `ℱ` viewed as a presheaf of `𝒪'`-modules
without the explicit identity whisker in the target ring presheaf. -/
private noncomputable abbrev stalkBaseChangePulledBackModule
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat) :=
  show PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat) from
    (PresheafOfModules.pullback
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ

private instance {X : TopCat.{u}} (x : X) : InitiallySmall.{u} (OpenNhds x) :=
  initiallySmall_of_essentiallySmall (OpenNhds x)

/-- Helper for Lemma 6.14.2: the inclusion of open neighborhoods into all opens is full. -/
private instance openNhds_inclusion_full {X : TopCat.{u}} (x : X) :
    (OpenNhds.inclusion x).Full where
  map_surjective := by
    intro U V f
    refine ⟨homOfLE f.le, ?_⟩
    cases U
    cases V
    rfl

/-- Helper for Lemma 6.14.2: the inclusion of open neighborhoods into all opens is faithful. -/
private instance openNhds_inclusion_faithful {X : TopCat.{u}} (x : X) :
    (OpenNhds.inclusion x).Faithful where
  map_injective := by
    intro U V f g h
    exact Subsingleton.elim f g

/-- Helper for Lemma 6.14.2: the neighborhood ring diagram whose colimit computes `𝒪_x`. -/
private abbrev stalkNeighborhoodRing
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    (OpenNhds x)ᵒᵖ ⥤ RingCat.{u} :=
  ((OpenNhds.inclusion x).op ⋙ 𝒪) ⋙ forget₂ CommRingCat RingCat

/-- Helper for Lemma 6.14.2: the restricted module presheaf on the neighborhood category of `x`. -/
private abbrev stalkNeighborhoodModule
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    PresheafOfModules (stalkNeighborhoodRing 𝒪 x) :=
  (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ

/-- Helper for Lemma 6.14.2: the restricted ring morphism on the neighborhood category of `x`. -/
private abbrev stalkNeighborhoodRingHom
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    stalkNeighborhoodRing 𝒪 x ⟶ stalkNeighborhoodRing 𝒪' x :=
  Functor.whiskerLeft (OpenNhds.inclusion x).op
    (Functor.whiskerRight p (forget₂ CommRingCat RingCat))

/-- Helper for Lemma 6.14.2: the canonical colimit cocone for the neighborhood ring diagram. -/
private abbrev stalkNeighborhoodRingCocone
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    CategoryTheory.Limits.Cocone (stalkNeighborhoodRing 𝒪 x) :=
  CategoryTheory.Limits.colimit.cocone (stalkNeighborhoodRing 𝒪 x)

/-- Helper for Lemma 6.14.2: the induced ring map on neighborhood-colimit stalk rings. -/
private noncomputable abbrev stalkNeighborhoodRingMap
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (stalkNeighborhoodRingCocone 𝒪 x).pt →+* (stalkNeighborhoodRingCocone 𝒪' x).pt :=
  (CategoryTheory.Limits.colim.map (stalkNeighborhoodRingHom p x)).hom

/-- Helper for Lemma 6.14.2: the neighborhood colimit ring map intertwines the cocone legs with
the restricted ring morphism. -/
private theorem stalkNeighborhoodRingMap_comp_ι
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (U : (OpenNhds x)ᵒᵖ) :
    (stalkNeighborhoodRingMap p x).comp
        ((stalkNeighborhoodRingCocone 𝒪 x).ι.app U).hom =
      ((stalkNeighborhoodRingCocone 𝒪' x).ι.app U).hom.comp
        ((stalkNeighborhoodRingHom p x).app U).hom := by
  -- This is the usual `ι_map` compatibility for the colimit cocones of the neighborhood diagrams.
  simpa [stalkNeighborhoodRingMap, Category.assoc] using
    congrArg RingCat.Hom.hom
      (CategoryTheory.Limits.colimit.ι_map (stalkNeighborhoodRingHom p x) U)

/-- Helper for Lemma 6.14.2: at a fixed neighborhood, the two ways of restricting scalars from the
stalk ring to the neighborhood ring are canonically identified. -/
private noncomputable abbrev stalkNeighborhoodRestrictScalarsConstIsoApp
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodRingCocone 𝒪' x).pt)) (U : (OpenNhds x)ᵒᵖ) :
    (((ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x)) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x)).obj M).obj U ≅
      ((PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
          PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).obj M).obj U :=
  (ModuleCat.restrictScalarsComp'App
      ((stalkNeighborhoodRingCocone 𝒪 x).ι.app U).hom
      (stalkNeighborhoodRingMap p x)
      ((stalkNeighborhoodRingMap p x).comp
        ((stalkNeighborhoodRingCocone 𝒪 x).ι.app U).hom)
      rfl M).symm ≪≫
    ModuleCat.restrictScalarsComp'App
      ((stalkNeighborhoodRingHom p x).app U).hom
      ((stalkNeighborhoodRingCocone 𝒪' x).ι.app U).hom
      ((stalkNeighborhoodRingMap p x).comp
        ((stalkNeighborhoodRingCocone 𝒪 x).ι.app U).hom)
      (stalkNeighborhoodRingMap_comp_ι p x U)
      M

/-- Helper for Lemma 6.14.2: the objectwise comparison between the two restricted constant
presheaves is natural in the neighborhood variable. -/
private theorem stalkNeighborhoodRestrictScalarsConstIso_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodRingCocone 𝒪' x).pt))
    {U V : (OpenNhds x)ᵒᵖ} (f : U ⟶ V) :
    (((ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x)).obj M).map f) ≫
      (ModuleCat.restrictScalars ((stalkNeighborhoodRing 𝒪 x).map f).hom).map
        (stalkNeighborhoodRestrictScalarsConstIsoApp p x M V).hom =
      (stalkNeighborhoodRestrictScalarsConstIsoApp p x M U).hom ≫
        (((PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
            PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).obj M).map f) := by
  -- Both sides are the identity on the underlying abelian groups after unfolding the two
  -- constant-presheaf transition maps and the comparison isomorphisms.
  ext m
  rfl

/-- Helper for Lemma 6.14.2: the objectwise comparison assembles to a morphism of module
presheaves on the neighborhood category. -/
private theorem stalkNeighborhoodRestrictScalarsConstIso_component_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodRingCocone 𝒪' x).pt)) :
    ∀ ⦃U V : (OpenNhds x)ᵒᵖ⦄ (f : U ⟶ V),
      (((ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
          PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x)).obj M).map f) ≫
        (ModuleCat.restrictScalars ((stalkNeighborhoodRing 𝒪 x).map f).hom).map
          (stalkNeighborhoodRestrictScalarsConstIsoApp p x M V).hom =
        (stalkNeighborhoodRestrictScalarsConstIsoApp p x M U).hom ≫
          (((PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
              PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).obj M).map f) :=
by
  intro U V f
  exact stalkNeighborhoodRestrictScalarsConstIso_naturality p x M f

/-- Helper for Lemma 6.14.2: the objectwise comparison is natural in the coefficient module. -/
private theorem stalkNeighborhoodRestrictScalarsConstIso_app_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    {M N : ModuleCat ((stalkNeighborhoodRingCocone 𝒪' x).pt)} (η : M ⟶ N) (U : (OpenNhds x)ᵒᵖ) :
    (((ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x)).map η).app U) ≫
      (stalkNeighborhoodRestrictScalarsConstIsoApp p x N U).hom =
    (stalkNeighborhoodRestrictScalarsConstIsoApp p x M U).hom ≫
      (((PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
          PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).map η).app U) := by
  -- The comparison isomorphism does not change the underlying elements, so it commutes with
  -- every morphism of coefficient modules.
  ext m
  rfl

/-- Helper for Lemma 6.14.2: the component isomorphisms are natural in the coefficient module. -/
private theorem stalkNeighborhoodRestrictScalarsConstIso_functor_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    {M N : ModuleCat ((stalkNeighborhoodRingCocone 𝒪' x).pt)} (η : M ⟶ N) :
    ((ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
          PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x)).map η) ≫
        (PresheafOfModules.isoMk
          (stalkNeighborhoodRestrictScalarsConstIsoApp p x N)
          (stalkNeighborhoodRestrictScalarsConstIso_component_naturality p x N)).hom =
      (PresheafOfModules.isoMk
          (stalkNeighborhoodRestrictScalarsConstIsoApp p x M)
          (stalkNeighborhoodRestrictScalarsConstIso_component_naturality p x M)).hom ≫
        ((PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
            PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).map η) := by
  -- Naturality of the functor-level comparison is checked objectwise on neighborhoods.
  ext U m
  rfl

private noncomputable def stalkNeighborhoodRestrictScalarsConstIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x) ≅
      PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
        PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x) :=
  NatIso.ofComponents
    (fun M ↦
      PresheafOfModules.isoMk
        (stalkNeighborhoodRestrictScalarsConstIsoApp p x M)
        (stalkNeighborhoodRestrictScalarsConstIso_component_naturality p x M))
    (fun {_ _} η ↦ stalkNeighborhoodRestrictScalarsConstIso_functor_naturality p x η)

/-- Helper for Lemma 6.14.2: the right-adjoint comparison in the orientation needed to transport
the neighborhood pullback/colimit adjunction to the common right adjoint. -/
private noncomputable abbrev stalkNeighborhoodRestrictScalarsConstIsoSymm
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
        PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x) ≅
      ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x) :=
  (stalkNeighborhoodRestrictScalarsConstIso p x).symm

/-- Helper for Lemma 6.14.2: the neighborhood ring diagram on `OpenNhds x` is filtered-colimit
data computing the ring stalk. -/
private noncomputable abbrev stalkNeighborhoodRingIsColimit
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    CategoryTheory.Limits.IsColimit (stalkNeighborhoodRingCocone 𝒪 x) :=
  CategoryTheory.Limits.colimit.isColimit (stalkNeighborhoodRing 𝒪 x)

/-- Helper for Lemma 6.14.2: the neighborhood ring morphism viewed over the identity functor on
`OpenNhds x`, which is the form required by `PresheafOfModules.pullback`. -/
private noncomputable abbrev stalkNeighborhoodRingHomOverId
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    stalkNeighborhoodRing 𝒪 x ⟶ (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x :=
  show stalkNeighborhoodRing 𝒪 x ⟶ (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
    stalkNeighborhoodRingHom p x

/-- Helper for Lemma 6.14.2: the untransported neighborhood pullback/colimit adjunction whose
right adjoint still lands in the restricted constant presheaf over `𝒪'`. -/
private noncomputable abbrev stalkNeighborhoodPullbackAdjunctionRaw
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
        PresheafOfModules.colimitFunctor (stalkNeighborhoodRingIsColimit 𝒪' x)) ⊣
      PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪' x) ⋙
        PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x) :=
  (PresheafOfModules.pullbackPushforwardAdjunction (stalkNeighborhoodRingHomOverId p x)).comp
    (PresheafOfModules.colimitAdjunction (stalkNeighborhoodRingIsColimit 𝒪' x))

/-- Helper for Lemma 6.14.2: cache the transported neighborhood pullback/colimit adjunction so
Lean elaborates the `ofNatIsoRight` transport only once. -/
private noncomputable def stalkNeighborhoodPullbackAdjunction
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
        PresheafOfModules.colimitFunctor (stalkNeighborhoodRingIsColimit 𝒪' x)) ⊣
      ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodRingCocone 𝒪 x) :=
  (stalkNeighborhoodPullbackAdjunctionRaw p x).ofNatIsoRight
    (stalkNeighborhoodRestrictScalarsConstIsoSymm p x)

/-- Helper for Lemma 6.14.2: the transported neighborhood adjunction unit is the original unit
followed by the right-adjoint comparison map. -/
private theorem stalkNeighborhoodPullbackAdjunction_unit_app
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x)) :
    (stalkNeighborhoodPullbackAdjunction p x).unit.app M =
      (stalkNeighborhoodPullbackAdjunctionRaw p x).unit.app M ≫
        (stalkNeighborhoodRestrictScalarsConstIsoSymm p x).hom.app
          ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
              PresheafOfModules.colimitFunctor (stalkNeighborhoodRingIsColimit 𝒪' x)).obj M) := by
  -- The cached adjunction is defined by `Adjunction.ofNatIsoRight`, whose unit is explicit.
  rfl

/-- Helper for Lemma 6.14.2: forgetting commutativity preserves the neighborhood colimit that
computes the stalk ring. -/
private noncomputable abbrev commRingStalkToRingStalkIso
    {X : TopCat.{u}} (x : X) (𝒪 : X.Presheaf CommRingCat.{u}) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk 𝒪 x) ≅
      TopCat.Presheaf.stalk (𝒪 ⋙ forget₂ CommRingCat RingCat) x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ 𝒪)

/-- Helper for Lemma 6.14.2: the neighborhood ring diagram also has the forgotten actual stalk
as a colimit point. -/
private noncomputable def stalkNeighborhoodActualStalkCocone
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    CategoryTheory.Limits.Cocone (stalkNeighborhoodRing 𝒪 x) where
  pt := (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk 𝒪 x)
  ι :=
    { app := fun U ↦
        (stalkNeighborhoodRingCocone 𝒪 x).ι.app U ≫ (commRingStalkToRingStalkIso x 𝒪).inv
      naturality := by
        intro U V f
        -- Postcompose the original colimit-cocone naturality relation with the preserved-colimit
        -- inverse so that the new cocone still satisfies the compatibility square.
        change (((stalkNeighborhoodRing 𝒪 x).map f ≫
              (stalkNeighborhoodRingCocone 𝒪 x).ι.app V) ≫
            (commRingStalkToRingStalkIso x 𝒪).inv) =
          (stalkNeighborhoodRingCocone 𝒪 x).ι.app U ≫ (commRingStalkToRingStalkIso x 𝒪).inv
        exact congrArg (fun k ↦ k ≫ (commRingStalkToRingStalkIso x 𝒪).inv)
          ((stalkNeighborhoodRingCocone 𝒪 x).w f) }

/-- Helper for Lemma 6.14.2: the canonical comparison from the anonymous neighborhood colimit ring
to the forgotten actual stalk ring is the inverse preserved-colimit isomorphism. -/
private theorem stalkNeighborhoodRingIsColimit_desc_actualStalkCocone
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    (stalkNeighborhoodRingIsColimit 𝒪 x).desc (stalkNeighborhoodActualStalkCocone 𝒪 x) =
      (commRingStalkToRingStalkIso x 𝒪).inv := by
  -- Both morphisms agree on every neighborhood germ of the original ring-valued colimit cocone.
  apply (stalkNeighborhoodRingIsColimit 𝒪 x).hom_ext
  intro U
  -- Rewrite the target leg to the chosen cocone field and use the colimit `fac` formula.
  change (stalkNeighborhoodRingCocone 𝒪 x).ι.app U ≫
      (stalkNeighborhoodRingIsColimit 𝒪 x).desc (stalkNeighborhoodActualStalkCocone 𝒪 x) =
    (stalkNeighborhoodActualStalkCocone 𝒪 x).ι.app U
  exact (stalkNeighborhoodRingIsColimit 𝒪 x).fac (stalkNeighborhoodActualStalkCocone 𝒪 x) U

/-- Helper for Lemma 6.14.2: the forgotten actual commutative stalk ring is a colimit of the
neighborhood ring diagram. -/
private noncomputable def stalkNeighborhoodActualStalkIsColimit
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    CategoryTheory.Limits.IsColimit (stalkNeighborhoodActualStalkCocone 𝒪 x) := by
  let hcolim := stalkNeighborhoodRingIsColimit 𝒪 x
  have hdesc :
      hcolim.desc (stalkNeighborhoodActualStalkCocone 𝒪 x) =
        (commRingStalkToRingStalkIso x 𝒪).inv :=
    stalkNeighborhoodRingIsColimit_desc_actualStalkCocone 𝒪 x
  -- The actual stalk cocone is colimiting because its comparison with the existing colimit point
  -- is the inverse of an isomorphism.
  haveI : IsIso (hcolim.desc (stalkNeighborhoodActualStalkCocone 𝒪 x)) := by
    rw [hdesc]
    infer_instance
  exact CategoryTheory.Limits.IsColimit.ofPointIso hcolim

/-- Helper for Lemma 6.14.2: each leg of the actual-stalk cocone is the forgotten germ map. -/
private theorem stalkNeighborhoodActualStalkCocone_ι_app
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (stalkNeighborhoodActualStalkCocone 𝒪 x).ι.app U =
      (forget₂ CommRingCat RingCat).map (𝒪.germ U.unop.1 x U.unop.2) := by
  -- Expand the cocone leg and identify it with the preserved-colimit comparison on germs.
  change (stalkNeighborhoodRingCocone 𝒪 x).ι.app U ≫ (commRingStalkToRingStalkIso x 𝒪).inv =
    (forget₂ CommRingCat RingCat).map (𝒪.germ U.unop.1 x U.unop.2)
  simpa [TopCat.Presheaf.germ] using
    (ι_preservesColimitIso_inv (G := forget₂ CommRingCat RingCat)
      (F := (OpenNhds.inclusion x).op ⋙ 𝒪) U)

/-- Helper for Lemma 6.14.2: the preserved-colimit comparison identifies the commutative-ring
stalk map with the ring-valued stalk map on the neighborhood diagram. -/
private theorem commRingStalkToRingStalkIso_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (commRingStalkToRingStalkIso x 𝒪).inv ≫
        (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) ≫
          (commRingStalkToRingStalkIso x 𝒪').hom =
      (stalkFunctor RingCat x).map (Functor.whiskerRight p (forget₂ CommRingCat RingCat)) := by
  -- Compare both morphisms on neighborhood germs of the ring-valued stalk colimit.
  apply TopCat.Presheaf.stalk_hom_ext (F := 𝒪 ⋙ forget₂ CommRingCat RingCat)
  intro U hxU
  let j : (OpenNhds x)ᵒᵖ := op ⟨U, hxU⟩
  have h₁ :
      Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪 ⋙ forget₂ CommRingCat RingCat) j ≫
          (commRingStalkToRingStalkIso x 𝒪).inv ≫
            (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) ≫
              (commRingStalkToRingStalkIso x 𝒪').hom =
        (forget₂ CommRingCat RingCat).map (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪) j) ≫
          (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) ≫
            (commRingStalkToRingStalkIso x 𝒪').hom := by
    have h₁a :
        (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪 ⋙ forget₂ CommRingCat RingCat) j ≫
            (commRingStalkToRingStalkIso x 𝒪).inv) ≫
          (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) =
        (forget₂ CommRingCat RingCat).map (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪) j) ≫
          (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) := by
      -- Convert the source germ from the ring-valued colimit back to the forgotten commutative stalk.
      simpa [j, commRingStalkToRingStalkIso, Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p))
          (ι_preservesColimitIso_inv (G := forget₂ CommRingCat RingCat)
            (F := (OpenNhds.inclusion x).op ⋙ 𝒪) j)
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ (commRingStalkToRingStalkIso x 𝒪').hom) h₁a
  have h₂ :
      (forget₂ CommRingCat RingCat).map (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪) j) ≫
          (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) ≫
            (commRingStalkToRingStalkIso x 𝒪').hom =
        (forget₂ CommRingCat RingCat).map
            (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪) j ≫
              ((stalkFunctor CommRingCat x).map p)) ≫
          (commRingStalkToRingStalkIso x 𝒪').hom := by
    -- Merge the two forgotten stalk maps into one mapped composition.
    simp [Category.assoc]
  have h₃ :
      (forget₂ CommRingCat RingCat).map
          (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪) j ≫
            ((stalkFunctor CommRingCat x).map p)) ≫
          (commRingStalkToRingStalkIso x 𝒪').hom =
        (forget₂ CommRingCat RingCat).map
            (p.app (op U) ≫ Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪') j) ≫
          (commRingStalkToRingStalkIso x 𝒪').hom := by
    have h₃a :
        (forget₂ CommRingCat RingCat).map
            (Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪) j ≫
              ((stalkFunctor CommRingCat x).map p)) =
          (forget₂ CommRingCat RingCat).map
            (p.app (op U) ≫ Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪') j) := by
      -- Functoriality of the commutative-ring stalk expresses the intermediate map on germs.
      simpa [j, TopCat.Presheaf.stalkFunctor, TopCat.Presheaf.germ] using
        congrArg
          (fun k ↦ (forget₂ CommRingCat RingCat).map k)
          (TopCat.Presheaf.stalkFunctor_map_germ (C := CommRingCat) (U := U) (x := x) (hx := hxU)
            (f := p))
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ (commRingStalkToRingStalkIso x 𝒪').hom) h₃a
  have h₄ :
      (forget₂ CommRingCat RingCat).map
          (p.app (op U) ≫ Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪') j) ≫
          (commRingStalkToRingStalkIso x 𝒪').hom =
        (Functor.whiskerRight p (forget₂ CommRingCat RingCat)).app (op U) ≫
          Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪' ⋙ forget₂ CommRingCat RingCat) j := by
    -- Transport the target germ across the preserved-colimit comparison for `𝒪'`.
    simpa [j, commRingStalkToRingStalkIso, Functor.map_comp, Category.assoc] using
      congrArg
        (fun k ↦ (Functor.whiskerRight p (forget₂ CommRingCat RingCat)).app (op U) ≫ k)
        (ι_preservesColimitIso_hom (G := forget₂ CommRingCat RingCat)
          (F := (OpenNhds.inclusion x).op ⋙ 𝒪') j)
  have h₅ :
      (Functor.whiskerRight p (forget₂ CommRingCat RingCat)).app (op U) ≫
          Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪' ⋙ forget₂ CommRingCat RingCat) j =
        Limits.colimit.ι ((OpenNhds.inclusion x).op ⋙ 𝒪 ⋙ forget₂ CommRingCat RingCat) j ≫
          (stalkFunctor RingCat x).map (Functor.whiskerRight p (forget₂ CommRingCat RingCat)) := by
    -- The ring-valued stalk functor gives the same sectionwise description on neighborhood germs.
    simpa [j, TopCat.Presheaf.stalkFunctor, TopCat.Presheaf.germ] using
      (TopCat.Presheaf.stalkFunctor_map_germ (C := RingCat) (U := U) (x := x) (hx := hxU)
        (f := Functor.whiskerRight p (forget₂ CommRingCat RingCat))).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 6.14.2: the actual stalk map intertwines the actual-stalk cocone legs with
the neighborhood restriction morphism. -/
private theorem stalkActualRingMap_comp_ι
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (U : (OpenNhds x)ᵒᵖ) :
    (((stalkFunctor CommRingCat x).map p).hom).comp
        ((stalkNeighborhoodActualStalkCocone 𝒪 x).ι.app U).hom =
      ((stalkNeighborhoodActualStalkCocone 𝒪' x).ι.app U).hom.comp
        ((stalkNeighborhoodRingHom p x).app U).hom := by
  -- After identifying both cocone legs with forgotten germ maps, this is the usual stalk
  -- functoriality square for `p` on the neighborhood `U`.
  simpa [stalkNeighborhoodActualStalkCocone_ι_app, stalkNeighborhoodRingHom, Functor.map_comp,
    Category.assoc] using
    congrArg RingCat.Hom.hom <|
      congrArg ((forget₂ CommRingCat RingCat).map) <|
        (TopCat.Presheaf.stalkFunctor_map_germ (C := CommRingCat) (U := U.unop.1) (x := x)
          (hx := U.unop.2) (f := p))

/-- Helper for Lemma 6.14.2: at a fixed neighborhood, the two actual-stalk restriction functors
agree on the nose after comparing the source and target cocone legs. -/
private noncomputable abbrev stalkActualRestrictScalarsConstIsoApp
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt)) (U : (OpenNhds x)ᵒᵖ) :
    (((ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x)).obj M).obj U ≅
      ((PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
          PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).obj M).obj U :=
  (ModuleCat.restrictScalarsComp'App
      ((stalkNeighborhoodActualStalkCocone 𝒪 x).ι.app U).hom
      (((stalkFunctor CommRingCat x).map p).hom)
      ((((stalkFunctor CommRingCat x).map p).hom).comp
        ((stalkNeighborhoodActualStalkCocone 𝒪 x).ι.app U).hom)
      rfl M).symm ≪≫
    ModuleCat.restrictScalarsComp'App
      ((stalkNeighborhoodRingHom p x).app U).hom
      ((stalkNeighborhoodActualStalkCocone 𝒪' x).ι.app U).hom
      ((((stalkFunctor CommRingCat x).map p).hom).comp
        ((stalkNeighborhoodActualStalkCocone 𝒪 x).ι.app U).hom)
      (stalkActualRingMap_comp_ι p x U)
      M

/-- Helper for Lemma 6.14.2: the forward actual-stalk restriction comparison fixes each
generator. -/
private theorem stalkActualRestrictScalarsConstIsoApp_hom_apply
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt)) (U : (OpenNhds x)ᵒᵖ)
    (m : M) :
    ModuleCat.Hom.hom (stalkActualRestrictScalarsConstIsoApp p x M U).hom m = m := by
  -- Both `restrictScalarsComp'App` components only repackage the same underlying element.
  rfl

/-- Helper for Lemma 6.14.2: the inverse actual-stalk restriction comparison also fixes each
generator. -/
private theorem stalkActualRestrictScalarsConstIsoApp_inv_apply
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt)) (U : (OpenNhds x)ᵒᵖ)
    (m : M) :
    ModuleCat.Hom.hom (stalkActualRestrictScalarsConstIsoApp p x M U).inv m = m := by
  -- The inverse comparison is the identity on the same underlying additive generator.
  rfl

/-- Helper for Lemma 6.14.2: the objectwise comparison for the actual-stalk right adjoints is
natural in the neighborhood variable. -/
private theorem stalkActualRestrictScalarsConstIso_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt))
    {U V : (OpenNhds x)ᵒᵖ} (f : U ⟶ V) :
    (((ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x)).obj M).map f) ≫
      (ModuleCat.restrictScalars ((stalkNeighborhoodRing 𝒪 x).map f).hom).map
        (stalkActualRestrictScalarsConstIsoApp p x M V).hom =
      (stalkActualRestrictScalarsConstIsoApp p x M U).hom ≫
        (((PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
            PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).obj M).map f) := by
  -- Both sides are the identity on the underlying abelian group of `M`.
  ext m
  rfl

/-- Helper for Lemma 6.14.2: the objectwise actual-stalk comparison assembles to a morphism of
module presheaves on the neighborhood category. -/
private theorem stalkActualRestrictScalarsConstIso_component_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt)) :
    ∀ ⦃U V : (OpenNhds x)ᵒᵖ⦄ (f : U ⟶ V),
      (((ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
          PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x)).obj M).map
          f) ≫
        (ModuleCat.restrictScalars ((stalkNeighborhoodRing 𝒪 x).map f).hom).map
          (stalkActualRestrictScalarsConstIsoApp p x M V).hom =
        (stalkActualRestrictScalarsConstIsoApp p x M U).hom ≫
          (((PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
              PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).obj M).map f) :=
by
  intro U V f
  exact stalkActualRestrictScalarsConstIso_naturality p x M f

/-- Helper for Lemma 6.14.2: the actual-stalk comparison is natural in the coefficient module. -/
private theorem stalkActualRestrictScalarsConstIso_app_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    {M N : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt)} (η : M ⟶ N)
    (U : (OpenNhds x)ᵒᵖ) :
    (((ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x)).map η).app U) ≫
      (stalkActualRestrictScalarsConstIsoApp p x N U).hom =
    (stalkActualRestrictScalarsConstIsoApp p x M U).hom ≫
      (((PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
          PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).map η).app U) := by
  -- The comparison does not alter underlying elements, so it commutes with every module map.
  ext m
  rfl

/-- Helper for Lemma 6.14.2: the actual-stalk component isomorphisms are natural in the
coefficient module. -/
private theorem stalkActualRestrictScalarsConstIso_functor_naturality
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    {M N : ModuleCat ((stalkNeighborhoodActualStalkCocone 𝒪' x).pt)} (η : M ⟶ N) :
    ((ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
          PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x)).map η) ≫
        (PresheafOfModules.isoMk
          (stalkActualRestrictScalarsConstIsoApp p x N)
          (stalkActualRestrictScalarsConstIso_component_naturality p x N)).hom =
      (PresheafOfModules.isoMk
          (stalkActualRestrictScalarsConstIsoApp p x M)
          (stalkActualRestrictScalarsConstIso_component_naturality p x M)).hom ≫
        ((PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
            PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x)).map η) := by
  -- Naturality of the functor-level comparison is checked objectwise on neighborhoods.
  ext U m
  rfl

/-- Helper for Lemma 6.14.2: the actual-stalk right adjoints are compared by a natural
isomorphism before transporting the neighborhood pullback adjunction. -/
private noncomputable def stalkActualRestrictScalarsConstIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x) ≅
      PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
        PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x) :=
  NatIso.ofComponents
    (fun M ↦
      PresheafOfModules.isoMk
        (stalkActualRestrictScalarsConstIsoApp p x M)
        (stalkActualRestrictScalarsConstIso_component_naturality p x M))
    (fun {_ _} η ↦ stalkActualRestrictScalarsConstIso_functor_naturality p x η)

/-- Helper for Lemma 6.14.2: before transporting to the common right adjoint, the neighborhood
pullback/colimit adjunction lands in the actual target stalk. -/
private noncomputable abbrev stalkActualPullbackAdjunctionRaw
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
        PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)) ⊣
      PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪' x) ⋙
        PresheafOfModules.restrictScalars (stalkNeighborhoodRingHom p x) :=
  (PresheafOfModules.pullbackPushforwardAdjunction (stalkNeighborhoodRingHomOverId p x)).comp
    (PresheafOfModules.colimitAdjunction (stalkNeighborhoodActualStalkIsColimit 𝒪' x))

/-- Helper for Lemma 6.14.2: transport the neighborhood pullback/colimit adjunction so its right
adjoint matches the actual-stalk extension-of-scalars adjunction on the nose. -/
private noncomputable def stalkActualPullbackAdjunction
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
        PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)) ⊣
      ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x) :=
  (stalkActualPullbackAdjunctionRaw p x).ofNatIsoRight
    (stalkActualRestrictScalarsConstIso p x).symm

/-- Helper for Lemma 6.14.2: the transported actual-pullback adjunction unit is the raw unit
followed by the right-adjoint comparison map coming from `ofNatIsoRight`. -/
private theorem stalkActualPullbackAdjunction_unit_app
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x)) :
    (stalkActualPullbackAdjunction p x).unit.app M =
      (stalkActualPullbackAdjunctionRaw p x).unit.app M ≫
        (stalkActualRestrictScalarsConstIso p x).symm.hom.app
          ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
              PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
            M) := by
  -- This is the explicit unit formula for `Adjunction.ofNatIsoRight`.
  rfl

/-- Helper for Lemma 6.14.2: transporting modules along the commutative-to-ring stalk
identifications intertwines restriction of scalars by the actual stalk map with restriction of
scalars by the neighborhood-colimit ring map. -/
private noncomputable def commRingStalkRestrictScalarsIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom ⋙
        ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ≅
      ModuleCat.restrictScalars (stalkNeighborhoodRingMap p x) ⋙
        ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪).hom.hom := by
  let f :
      𝒪.stalk x →+* 𝒪'.stalk x :=
    ((stalkFunctor CommRingCat x).map p).hom
  let g :
      𝒪'.stalk x →+* (stalkNeighborhoodRingCocone 𝒪' x).pt :=
    (commRingStalkToRingStalkIso x 𝒪').hom.hom
  let f' :
      𝒪.stalk x →+* (stalkNeighborhoodRingCocone 𝒪 x).pt :=
    (commRingStalkToRingStalkIso x 𝒪).hom.hom
  let g' :
      (stalkNeighborhoodRingCocone 𝒪 x).pt →+* (stalkNeighborhoodRingCocone 𝒪' x).pt :=
    stalkNeighborhoodRingMap p x
  have hmap_cat :
      (forget₂ CommRingCat RingCat).map ((stalkFunctor CommRingCat x).map p) ≫
          (commRingStalkToRingStalkIso x 𝒪').hom =
        (commRingStalkToRingStalkIso x 𝒪).hom ≫
          (show TopCat.Presheaf.stalk (𝒪 ⋙ forget₂ CommRingCat RingCat) x ⟶
              TopCat.Presheaf.stalk (𝒪' ⋙ forget₂ CommRingCat RingCat) x from
            RingCat.ofHom (stalkNeighborhoodRingMap p x)) := by
    -- Precompose the naturality square with the source stalk isomorphism to isolate the two
    -- composite restriction maps from the commutative stalk to the ring-valued target stalk.
    simpa [stalkNeighborhoodRingMap, stalkNeighborhoodRingHom, TopCat.Presheaf.stalkFunctor,
      Category.assoc] using
      congrArg
        (fun k ↦ (commRingStalkToRingStalkIso x 𝒪).hom ≫ k)
        (commRingStalkToRingStalkIso_naturality p x)
  have hmap :
      g.comp f = g'.comp f' := by
    simpa [f, g, f', g'] using congrArg RingCat.Hom.hom hmap_cat
  -- Replace both composites of restriction functors by the same restriction functor.
  exact
    (ModuleCat.restrictScalarsComp' f g (g.comp f) rfl).symm ≪≫
      eqToIso (by simpa [hmap] using congrArg ModuleCat.restrictScalars hmap) ≪≫
      ModuleCat.restrictScalarsComp' f' g' (g'.comp f') rfl

/-- Helper for Lemma 6.14.2: the actual-stalk cocone point carries the commutative ring
structure coming from the commutative ring stalk. -/
private instance stalkNeighborhoodActualStalkCommRing
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    CommRing ((stalkNeighborhoodActualStalkCocone 𝒪 x).pt) :=
  inferInstanceAs (CommRing ↑(TopCat.Presheaf.stalk 𝒪 x))

/-- Helper for Lemma 6.14.2: the colimit module over the actual source stalk, viewed as an
`𝒪_x`-module. -/
private noncomputable abbrev stalkNeighborhoodActualStalkModule
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ModuleCat (𝒪.stalk x) :=
  (PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x)).obj
    (stalkNeighborhoodModule 𝒪 ℱ x)

/-- Helper for Lemma 6.14.2: the colimit leg for the restricted neighborhood module is the usual
stalk germ map on the underlying presheaf. -/
private theorem stalkNeighborhoodModule_colimit_ι_eq_germ
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : Opens X) (hxU : x ∈ U) (m : ℱ.obj (op U)) :
    (CategoryTheory.Limits.colimit.ι (stalkNeighborhoodModule 𝒪 ℱ x).presheaf (op ⟨U, hxU⟩)) m =
      TopCat.Presheaf.germ ℱ.presheaf U x hxU m := by
  rfl

/-- Helper for Lemma 6.14.2: the actual-stalk colimit scalar action agrees with the usual germ
formula on neighborhood generators. -/
private theorem stalkNeighborhoodActualStalkModule_ι_smul_eq_germ_smul
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : Opens X) (hxU : x ∈ U) (r : 𝒪.obj (op U)) (m : ℱ.obj (op U)) :
    (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
        TopCat.Presheaf.germ ℱ.presheaf U x hxU (r • m)) =
      𝒪.germ U x hxU r •
        (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
          TopCat.Presheaf.germ ℱ.presheaf U x hxU m) := by
  -- Rewrite the abstract `ι_smul` statement for the actual-stalk colimit cocone to the concrete
  -- germ maps at the chosen neighborhood.
  simpa [PresheafOfModules.ModuleColimit.ιR, PresheafOfModules.ModuleColimit.ιM,
    stalkNeighborhoodActualStalkModule, stalkNeighborhoodActualStalkCocone_ι_app,
    stalkNeighborhoodModule_colimit_ι_eq_germ] using
    (PresheafOfModules.ModuleColimit.smul_eq
      (cR := stalkNeighborhoodActualStalkCocone 𝒪 x)
      (stalkNeighborhoodActualStalkIsColimit 𝒪 x)
      (hcM := CategoryTheory.Limits.colimit.isColimit (stalkNeighborhoodModule 𝒪 ℱ x).presheaf)
      (U := op ⟨U, hxU⟩) r m).symm

/-- Helper for Lemma 6.14.2: the actual-stalk colimit module uses the same scalar action as the
ordinary stalk module. -/
private theorem stalkNeighborhoodActualStalkModuleIso_map_smul
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ∀ (r : 𝒪.stalk x) (m : ↑(stalk ℱ.presheaf x)),
      (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
          ((r • m : ↑(ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x))))) =
        r •
          (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
              m) := by
  intro r m
  obtain ⟨U, hxU, rU, hr⟩ := TopCat.Presheaf.germ_exist 𝒪 x r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist ℱ.presheaf x m
  let W : Opens X := U ⊓ V
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : 𝒪.obj (op W) := 𝒪.map iWU.op rU
  let mW : ℱ.obj (op W) := ℱ.map iWV.op mV
  -- Move both representatives to a common neighborhood so that the scalar identity is generated
  -- by a single `ι_smul` computation.
  have hrW : 𝒪.germ W x hxW rW = r := by
    simpa [W, iWU, hxW, rW] using (𝒪.germ_res_apply iWU x hxW rU).trans hr
  have hmW : TopCat.Presheaf.germ ℱ.presheaf W x hxW mW = m := by
    simpa [W, iWV, hxW, mW] using
      (TopCat.Presheaf.germ_res_apply ℱ.presheaf iWV x hxW mV).trans hm
  have hsmulW :
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) = r • m := by
    rw [PresheafOfModules.germ_smul (M := ℱ) x W hxW rW mW, hrW, hmW]
  calc
    (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
        ((r • m : ↑(ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x)))))
        =
      (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
        TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW)) := by
          rw [← hsmulW]
    _ = 𝒪.germ W x hxW rW •
          (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from
            TopCat.Presheaf.germ ℱ.presheaf W x hxW mW) := by
          -- The actual-colimit module structure is generated by the same neighborhood germ formula.
          exact stalkNeighborhoodActualStalkModule_ι_smul_eq_germ_smul 𝒪 ℱ x W hxW rW mW
    _ = r • (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from m) := by
          rw [hrW, hmW]

/-- Helper for Lemma 6.14.2: the actual-stalk colimit module identifies with the ordinary stalk
module. -/
private noncomputable def stalkNeighborhoodActualStalkModuleIso
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x) ≅
      stalkNeighborhoodActualStalkModule 𝒪 ℱ x :=
  letI : Module (𝒪.stalk x) ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) :=
    (stalkNeighborhoodActualStalkModule 𝒪 ℱ x).isModule
  let e : ↑(stalk ℱ.presheaf x) ≃ₗ[𝒪.stalk x] ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) :=
    { __ := AddEquiv.refl _
      map_smul' := stalkNeighborhoodActualStalkModuleIso_map_smul 𝒪 ℱ x }
  e.toModuleIso

/-- Helper for Lemma 6.14.2: the forward actual-stalk source identification fixes each
generator. -/
private theorem stalkNeighborhoodActualStalkModuleIso_hom_apply
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (m : ↑(stalk ℱ.presheaf x)) :
    ModuleCat.Hom.hom (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x).hom m =
      (show ↑(stalkNeighborhoodActualStalkModule 𝒪 ℱ x) from m) := by
  -- The chosen linear equivalence is `AddEquiv.refl`, so it preserves generators literally.
  rfl

/-- Helper for Lemma 6.14.2: the inverse actual-stalk source identification also fixes each
generator. -/
private theorem stalkNeighborhoodActualStalkModuleIso_inv_apply
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (m : stalkNeighborhoodActualStalkModule 𝒪 ℱ x) :
    ModuleCat.Hom.hom (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x).inv m =
      (show ↑(stalk ℱ.presheaf x) from m) := by
  -- The inverse linear equivalence is again the identity on the underlying additive group.
  rfl

/-- Helper for Lemma 6.14.2: the source-side actual-stalk base-change adjunction packages
stalkwise extension of scalars directly over the actual source stalk ring. -/
private noncomputable def stalkActualBaseChangeAdjunction
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x) ⋙
        ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)) ⊣
      ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom) ⋙
        PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x) :=
  (PresheafOfModules.colimitAdjunction (stalkNeighborhoodActualStalkIsColimit 𝒪 x)).comp
    (ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom))

/-- Helper for Lemma 6.14.2: on the source neighborhood module, the left functor of the actual
base-change adjunction is definitionally scalar extension of the actual-stalk colimit module. -/
private theorem stalkActualBaseChangeAdjunction_left_obj
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x) ⋙
        ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x)) =
      (ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (stalkNeighborhoodActualStalkModule 𝒪 ℱ x) := by
  -- This isolates the source object that must be compared with the ordinary stalk module before
  -- entering the `leftAdjointUniq` endgame.
  rfl

/-- Helper for Lemma 6.14.2: on each coefficient presheaf, global restriction of scalars followed
by restriction to neighborhoods is definitionally the same as neighborhood restriction of scalars
along the induced local ring map. -/
private theorem stalkNeighborhoodPushforward_obj
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)) :
    ((PresheafOfModules.pushforward
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
      PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj M) =
      (PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)).obj
        (stalkNeighborhoodModule 𝒪' M x) := by
  -- Both sides are built by the same explicit precomposition with `OpenNhds.inclusion x`
  -- followed by the same objectwise restriction-of-scalars data.
  rfl

/-- Helper for Lemma 6.14.2: the objectwise neighborhood pushforward identification assembles to
a natural isomorphism of right adjoints over the global and local ring maps. -/
private noncomputable def stalkNeighborhoodPushforwardIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X) :
    (PresheafOfModules.pushforward
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
      PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪) ≅
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪' ⋙
        PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)) :=
  NatIso.ofComponents
    (fun M ↦ eqToIso (stalkNeighborhoodPushforward_obj p x M))
    (by
      intro M N η
      ext U m
      rfl)

/-- Helper for Lemma 6.14.2: the right-adjoint comparison induces a canonical left mate between
the neighborhood pullback routes. -/
private noncomputable def stalkNeighborhoodModule_pullbackMate
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪 ⋙
        PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)) ⟶
      (PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
        PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪') :=
  -- Transfer the packaged right-adjoint square across the two pullback/pushforward adjunctions.
  (CategoryTheory.mateEquiv
      (PresheafOfModules.pullbackPushforwardAdjunction
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat)))
      (PresheafOfModules.pullbackPushforwardAdjunction (stalkNeighborhoodRingHomOverId p x))).symm
    (stalkNeighborhoodPushforwardIso p x).hom

/-- Helper for Lemma 6.14.2: the left mate satisfies the expected unit identity coming from
`CategoryTheory.unit_mateEquiv_symm`. -/
private theorem stalkNeighborhoodModule_pullbackMate_unit_app
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
        ((PresheafOfModules.pullbackPushforwardAdjunction
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) ≫
      (stalkNeighborhoodPushforwardIso p x).hom.app
        ((PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ) =
    (PresheafOfModules.pullbackPushforwardAdjunction
        (stalkNeighborhoodRingHomOverId p x)).unit.app (stalkNeighborhoodModule 𝒪 ℱ x) ≫
      (PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)).map
        ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) := by
  -- This is exactly the unit-side mate identity specialized to the packaged right-adjoint square.
  have h :=
    CategoryTheory.unit_mateEquiv_symm
      (PresheafOfModules.pullbackPushforwardAdjunction
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat)))
      (PresheafOfModules.pullbackPushforwardAdjunction (stalkNeighborhoodRingHomOverId p x))
      (stalkNeighborhoodPushforwardIso p x).hom ℱ
  simp [stalkNeighborhoodModule_pullbackMate] at h ⊢

/-- Helper for Lemma 6.14.2: the neighborhood-restriction functor is the right adjoint in the
identity change-of-rings adjunction over `OpenNhds x`. -/
private noncomputable abbrev stalkNeighborhoodRestrictionAdjunction
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
          𝟙 _) ⊣
      PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪 :=
  PresheafOfModules.pullbackPushforwardAdjunction
    (show stalkNeighborhoodRing 𝒪 x ⟶
        (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
      𝟙 _)

/-- Helper for Lemma 6.14.2: on the neighborhood category, composing the identity pullback with
the local pullback comparison collapses by the standard left-unital pullback isomorphism. -/
private theorem stalkNeighborhoodPullback_id_comp
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    PresheafOfModules.pullbackComp
        (F := 𝟭 (OpenNhds x))
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪 x from
          𝟙 _)
        (stalkNeighborhoodRingHomOverId p x) =
      Functor.isoWhiskerRight
          (PresheafOfModules.pullbackId (stalkNeighborhoodRing 𝒪 x))
          (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)) ≪≫
        Functor.leftUnitor _ := by
  -- This is the local `pullback_id_comp` rewrite that removes the source-side identity pullback.
  simpa using
    (PresheafOfModules.pullback_id_comp
      (φ := stalkNeighborhoodRingHomOverId p x))

/-- Helper for Lemma 6.14.2: on the neighborhood category, composing the local pullback with the
identity pullback collapses by the standard right-unital pullback isomorphism. -/
private theorem stalkNeighborhoodPullback_comp_id
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    PresheafOfModules.pullbackComp
        (G := 𝟭 (OpenNhds x))
        (stalkNeighborhoodRingHomOverId p x)
        (show stalkNeighborhoodRing 𝒪' x ⟶
            (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
          𝟙 _) =
      Functor.isoWhiskerLeft
          (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x))
          (PresheafOfModules.pullbackId (stalkNeighborhoodRing 𝒪' x)) ≪≫
        Functor.rightUnitor _ := by
  -- This is the local `pullback_comp_id` rewrite that removes the target-side identity pullback.
  simpa using
    (PresheafOfModules.pullback_comp_id
      (φ := stalkNeighborhoodRingHomOverId p x))

/-- Helper for Lemma 6.14.2: conjugating the identity pullback comparison gives the inverse
identity pushforward comparison for presheaves of modules. -/
private theorem presheaf_conjugateEquiv_pullbackId_hom
    {C : Type u} [Category.{u} C] (S : Cᵒᵖ ⥤ RingCat.{u}) :
    CategoryTheory.conjugateEquiv CategoryTheory.Adjunction.id
        (PresheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 C) (𝟙 S))
        (PresheafOfModules.pullbackId S).hom =
      (PresheafOfModules.pushforwardId S).inv := by
  exact CategoryTheory.Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

/-- Helper for Lemma 6.14.2: conjugating the inverse pullback-composition comparison gives the
pushforward-composition comparison for presheaves of modules. -/
private theorem presheaf_conjugateEquiv_pullbackComp_inv
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} {T : Eᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ T)
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint] :
    CategoryTheory.conjugateEquiv
        ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
          (PresheafOfModules.pullbackPushforwardAdjunction ψ))
        (PresheafOfModules.pullbackPushforwardAdjunction (F := F ⋙ G)
          (φ ≫ F.op.whiskerLeft ψ))
        (PresheafOfModules.pullbackComp φ ψ).inv =
      (PresheafOfModules.pushforwardComp φ ψ).hom := by
  exact CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- Helper for Lemma 6.14.2: mating the inverse right-adjoint comparison across the neighborhood
restriction adjunctions produces the intermediate square used in the iterated-mates analysis. -/
private noncomputable abbrev stalkNeighborhoodPushforwardInvVerticalMate
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :=
  (CategoryTheory.mateEquiv
      (stalkNeighborhoodRestrictionAdjunction 𝒪' x)
      (stalkNeighborhoodRestrictionAdjunction 𝒪 x)).symm
    (stalkNeighborhoodPushforwardIso p x).inv

/-- Helper for Lemma 6.14.2: iterating mates on the inverse neighborhood pushforward comparison
lands in the left-adjoint square that is conjugate to the original right-adjoint isomorphism. -/
private noncomputable abbrev stalkNeighborhoodPushforwardInvDoubleMate
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :=
  (CategoryTheory.mateEquiv
      (PresheafOfModules.pullbackPushforwardAdjunction (stalkNeighborhoodRingHomOverId p x))
      (PresheafOfModules.pullbackPushforwardAdjunction
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat)))).symm
    (stalkNeighborhoodPushforwardInvVerticalMate p x)

/-- Helper for Lemma 6.14.2: the iterated mate of the inverse right-adjoint comparison is the
conjugate left-adjoint square predicted by the general mates formalism. -/
private theorem stalkNeighborhoodPushforwardInvDoubleMate_eq_conjugate
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    stalkNeighborhoodPushforwardInvDoubleMate p x =
      (CategoryTheory.conjugateEquiv
          ((PresheafOfModules.pullbackPushforwardAdjunction
              (stalkNeighborhoodRingHomOverId p x)).comp
            (stalkNeighborhoodRestrictionAdjunction 𝒪' x))
          ((stalkNeighborhoodRestrictionAdjunction 𝒪 x).comp
            (PresheafOfModules.pullbackPushforwardAdjunction
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))))).symm
        (stalkNeighborhoodPushforwardIso p x).inv := by
  -- This is the iterated-mates identity specialized to the neighborhood restriction adjunctions.
  simpa [stalkNeighborhoodPushforwardInvDoubleMate, stalkNeighborhoodPushforwardInvVerticalMate]
    using
      (CategoryTheory.iterated_mateEquiv_conjugateEquiv_symm
        (PresheafOfModules.pullbackPushforwardAdjunction (stalkNeighborhoodRingHomOverId p x))
        (PresheafOfModules.pullbackPushforwardAdjunction
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat)))
        (stalkNeighborhoodRestrictionAdjunction 𝒪 x)
        (stalkNeighborhoodRestrictionAdjunction 𝒪' x)
        ((stalkNeighborhoodPushforwardIso p x).inv))

/-- Helper for Lemma 6.14.2: the conjugate of the inverse neighborhood pushforward comparison is
already a natural isomorphism between the two iterated left-adjoint routes. -/
private noncomputable def stalkNeighborhoodPushforwardInvDoubleMateIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    (PresheafOfModules.pullback
          (show stalkNeighborhoodRing 𝒪 x ⟶
              (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
            𝟙 _) ⋙
        PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))) ≅
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
        PresheafOfModules.pullback
          (show stalkNeighborhoodRing 𝒪' x ⟶
              (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            𝟙 _)) :=
  let e :=
    CategoryTheory.conjugateIsoEquiv
      ((PresheafOfModules.pullbackPushforwardAdjunction
          (stalkNeighborhoodRingHomOverId p x)).comp
        (stalkNeighborhoodRestrictionAdjunction 𝒪' x))
      ((stalkNeighborhoodRestrictionAdjunction 𝒪 x).comp
        (PresheafOfModules.pullbackPushforwardAdjunction
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))))
  e.symm ((stalkNeighborhoodPushforwardIso p x).symm)

/-- Helper for Lemma 6.14.2: the direct conjugate neighborhood comparison supplied by the
right-adjoint pushforward isomorphism. This packages the source-faithful Beck-Chevalley route
without appealing to any additional endpoint transport. -/
private noncomputable abbrev stalkNeighborhoodModule_pullbackConjugateIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    (PresheafOfModules.pullback
          (show stalkNeighborhoodRing 𝒪 x ⟶
              (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
            𝟙 _) ⋙
        PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))) ≅
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
        PresheafOfModules.pullback
          (show stalkNeighborhoodRing 𝒪' x ⟶
              (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            𝟙 _)) :=
  stalkNeighborhoodPushforwardInvDoubleMateIso p x

/-- Helper for Lemma 6.14.2: every component of the direct conjugate neighborhood comparison is an
isomorphism before the source and target endpoints are normalized. -/
private instance stalkNeighborhoodModule_pullbackConjugateIso_app_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x)) :
    IsIso ((stalkNeighborhoodModule_pullbackConjugateIso p x).hom.app M) := by
  -- The direct conjugate comparison is itself a natural isomorphism, so each component is an iso.
  infer_instance

/-- Helper for Lemma 6.14.2: each component of the direct conjugate neighborhood comparison is an
isomorphism before the source and target endpoints are normalized. -/
private instance stalkNeighborhoodPushforwardInvDoubleMateIso_app_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x)) :
    IsIso ((stalkNeighborhoodPushforwardInvDoubleMateIso p x).hom.app M) := by
  -- Route correction: the direct conjugate comparison is already a natural isomorphism, so every
  -- component isomorphism is available without revisiting the older raw-mate transport.
  infer_instance

/-- Helper for Lemma 6.14.2: the iterated mate of the inverse pushforward comparison is an
isomorphism before removing the identity pullback layers. -/
private instance stalkNeighborhoodPushforwardInvDoubleMate_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    IsIso (stalkNeighborhoodPushforwardInvDoubleMate p x) := by
  -- Repackage the conjugate square as the hom of an explicit natural isomorphism.
  rw [stalkNeighborhoodPushforwardInvDoubleMate_eq_conjugate]
  simpa [stalkNeighborhoodPushforwardInvDoubleMateIso] using
    (show IsIso (stalkNeighborhoodPushforwardInvDoubleMateIso p x).hom by infer_instance)

/-- Helper for Lemma 6.14.2: after applying the double-mate isomorphism to the neighborhood module
of `ℱ`, the two `pullbackComp` isomorphisms normalize it to a comparison between the two composite
source and target pullback routes. -/
private noncomputable def stalkNeighborhoodModule_pullbackRawIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :=
  -- Normalize the source and target of the double mate by the canonical pullback-composition
  -- isomorphisms before comparing them to the final mixed Beck-Chevalley component.
  ((PresheafOfModules.pullbackComp
      (F := OpenNhds.inclusion x)
      (show stalkNeighborhoodRing 𝒪 x ⟶
          (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
        𝟙 _)
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat))).app
      (stalkNeighborhoodModule 𝒪 ℱ x)).symm ≪≫
    (stalkNeighborhoodModule_pullbackConjugateIso p x).app
      (stalkNeighborhoodModule 𝒪 ℱ x) ≪≫
    (PresheafOfModules.pullbackComp
      (F := 𝟭 (OpenNhds x))
      (G := OpenNhds.inclusion x)
      (stalkNeighborhoodRingHomOverId p x)
      (show stalkNeighborhoodRing 𝒪' x ⟶
          (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        𝟙 _)).app
      (stalkNeighborhoodModule 𝒪 ℱ x)

/-- Helper for Lemma 6.14.2: inverse components of a natural isomorphism are isomorphisms, in the
form needed for endpoint cancellation. -/
private instance natIso_inv_app_isIso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    (X : C) :
    IsIso (e.inv.app X) := by
  -- The inverse component is the hom component of the symmetric natural isomorphism.
  change IsIso (e.symm.hom.app X)
  infer_instance

/-- Helper for Lemma 6.14.2: inverse components of the pullback-composition comparison are
isomorphisms, in the form needed for endpoint cancellation. -/
private instance presheaf_pullbackComp_inv_app_isIso
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} {T : Eᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ T)
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (M : PresheafOfModules S) :
    IsIso ((PresheafOfModules.pullbackComp φ ψ).inv.app M) := by
  -- The inverse component is the hom component of the symmetric natural isomorphism.
  change IsIso ((PresheafOfModules.pullbackComp φ ψ).symm.hom.app M)
  infer_instance

/-- Helper for Lemma 6.14.2: hom components of the pullback-composition comparison are
isomorphisms, in the form needed for endpoint cancellation. -/
private instance presheaf_pullbackComp_hom_app_isIso
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} {T : Eᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ T)
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (M : PresheafOfModules S) :
    IsIso ((PresheafOfModules.pullbackComp φ ψ).hom.app M) := by
  -- The hom component is the hom of the objectwise isomorphism supplied by the natural isomorphism.
  change IsIso ((PresheafOfModules.pullbackComp φ ψ).app M).hom
  infer_instance

/-- Helper for Lemma 6.14.2: the inverse component of a pullback-composition comparison whose
second factor is an identity pullback is an isomorphism. -/
private instance presheaf_pullbackComp_id_inv_app_isIso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    (M : PresheafOfModules S) :
    IsIso ((PresheafOfModules.pullbackComp (G := 𝟭 D) φ (𝟙 R)).inv.app M) := by
  change IsIso ((PresheafOfModules.pullbackComp (G := 𝟭 D) φ (𝟙 R)).symm.hom.app M)
  infer_instance

/-- Helper for Lemma 6.14.2: the unit of the identity change-of-rings adjunction is an
isomorphism. -/
private instance presheaf_pullbackId_unit_isIso
    {C : Type*} [Category C] (S : Cᵒᵖ ⥤ RingCat.{u}) :
    IsIso (PresheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 C) (𝟙 S)).unit := by
  exact (PresheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 C) (𝟙 S)).isIso_unit_of_iso
    (Functor.isoWhiskerRight (PresheafOfModules.pullbackId S)
        (PresheafOfModules.pushforward (F := 𝟭 C) (𝟙 S)) ≪≫
      Functor.leftUnitor _ ≪≫
      PresheafOfModules.pushforwardId S)

/-- Helper for Lemma 6.14.2: the counit of the identity change-of-rings adjunction is an
isomorphism. -/
private instance presheaf_pullbackId_counit_isIso
    {C : Type*} [Category C] (S : Cᵒᵖ ⥤ RingCat.{u}) :
    IsIso (PresheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 C) (𝟙 S)).counit := by
  exact (PresheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 C) (𝟙 S)).isIso_counit_of_iso
    (Functor.isoWhiskerRight (PresheafOfModules.pushforwardId S)
        (PresheafOfModules.pullback (F := 𝟭 C) (𝟙 S)) ≪≫
      Functor.leftUnitor _ ≪≫
      PresheafOfModules.pullbackId S)

private noncomputable def yonedaWhiskerFullyFaithfulIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (X : C) :
    F.op ⋙ yoneda.obj (F.obj X) ≅ yoneda.obj X :=
  NatIso.ofComponents
    (fun U =>
      Equiv.toIso
        ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv
          (X := U.unop) (Y := X)).symm)
    (by
      intro U V f
      ext g
      apply (Functor.FullyFaithful.ofFullyFaithful F).map_injective
      simp [Functor.FullyFaithful.homEquiv])

private noncomputable def presheaf_pushforward₀_freeYonedaIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (R : Dᵒᵖ ⥤ RingCat.{u}) (X : C) :
    (PresheafOfModules.pushforward₀.{u} F R).obj
        ((PresheafOfModules.free R).obj (yoneda.obj (F.obj X))) ≅
      (PresheafOfModules.free (F.op ⋙ R)).obj (yoneda.obj X) :=
  (PresheafOfModules.free (F.op ⋙ R)).mapIso (yonedaWhiskerFullyFaithfulIso F X)

private noncomputable def presheaf_pullback_freeYonedaIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) [(PresheafOfModules.pushforward.{u} φ).IsRightAdjoint]
    (X : C) :
    (PresheafOfModules.pullback φ).obj
        ((PresheafOfModules.free S).obj (yoneda.obj X)) ≅
      (PresheafOfModules.free R).obj (yoneda.obj (F.obj X)) :=
  CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso
    ((PresheafOfModules.pullbackPushforwardAdjunction φ).corepresentableBy
      ((PresheafOfModules.free S).obj (yoneda.obj X)))
    (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X)

private theorem presheaf_pullback_freeYonedaIso_hom_adj
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) [(PresheafOfModules.pushforward.{u} φ).IsRightAdjoint]
    (X : C) :
    (PresheafOfModules.pullbackPushforwardAdjunction φ).unit.app
        ((PresheafOfModules.free S).obj (yoneda.obj X)) ≫
      (PresheafOfModules.pushforward φ).map
        (presheaf_pullback_freeYonedaIso φ X).hom =
    (PresheafOfModules.freeYonedaEquiv
      (R := S)
      (M := (PresheafOfModules.pushforward φ).obj
        ((PresheafOfModules.free R).obj (yoneda.obj (F.obj X))))
      (X := X)).symm
      (ModuleCat.freeMk (𝟙 (F.obj X))) := by
  let e :=
    ((PresheafOfModules.pullbackPushforwardAdjunction φ).corepresentableBy
      ((PresheafOfModules.free S).obj (yoneda.obj X)))
  let e' := PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X
  change e.homEquiv (presheaf_pullback_freeYonedaIso φ X).hom =
    (PresheafOfModules.freeYonedaEquiv
      (R := S)
      (M := (PresheafOfModules.pushforward φ).obj
        ((PresheafOfModules.free R).obj (yoneda.obj (F.obj X))))
      (X := X)).symm (ModuleCat.freeMk (𝟙 (F.obj X)))
  change e.homEquiv (e.uniqueUpToIso e').hom = e'.homEquiv (𝟙 _)
  dsimp [CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso, CategoryTheory.Coyoneda.ext]
  rw [CategoryTheory.Coyoneda.fullyFaithful_preimage]
  change e.homEquiv ((e.homEquiv.trans e'.homEquiv.symm).symm (𝟙 _)) = e'.homEquiv (𝟙 _)
  have h :=
    Equiv.apply_symm_apply (e.homEquiv.trans e'.homEquiv.symm) (𝟙 _)
  change e'.homEquiv.symm
      (e.homEquiv ((e.homEquiv.trans e'.homEquiv.symm).symm (𝟙 _))) = 𝟙 _ at h
  exact (Equiv.symm_apply_eq e'.homEquiv).mp h

private theorem presheaf_restriction_unit_freeYoneda_isIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (R : Dᵒᵖ ⥤ RingCat.{u}) (X : C) :
    IsIso
      ((PresheafOfModules.pullbackPushforwardAdjunction
          (F := F) (𝟙 (F.op ⋙ R))).unit.app
        ((PresheafOfModules.free (F.op ⋙ R)).obj (yoneda.obj X))) := by
  let φ : F.op ⋙ R ⟶ F.op ⋙ R := 𝟙 _
  let e := presheaf_pullback_freeYonedaIso φ X
  let eR := presheaf_pushforward₀_freeYonedaIso F R X
  have hcomp :
      (PresheafOfModules.pullbackPushforwardAdjunction φ).unit.app
          ((PresheafOfModules.free (F.op ⋙ R)).obj (yoneda.obj X)) ≫
        (PresheafOfModules.pushforward φ).map e.hom =
      eR.inv := by
    rw [presheaf_pullback_freeYonedaIso_hom_adj]
    apply PresheafOfModules.freeYonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    change ModuleCat.freeMk (𝟙 (F.obj X)) =
      (eR.inv.app (op X)) (ModuleCat.freeMk (𝟙 X))
    dsimp [eR, presheaf_pushforward₀_freeYonedaIso, yonedaWhiskerFullyFaithfulIso,
      Functor.FullyFaithful.homEquiv]
    change ModuleCat.freeMk (𝟙 (F.obj X)) =
      ((ModuleCat.free (R.obj (op (F.obj X)))).map
        (F.map : (X ⟶ X) → (F.obj X ⟶ F.obj X))) (ModuleCat.freeMk (𝟙 X))
    rw [ModuleCat.free_map_apply, F.map_id]
  haveI : IsIso e.hom := by
    infer_instance
  haveI : IsIso ((PresheafOfModules.pushforward φ).map e.hom) := by
    exact CategoryTheory.Functor.map_isIso (PresheafOfModules.pushforward φ) e.hom
  have hcompIso :
      IsIso
        ((PresheafOfModules.pullbackPushforwardAdjunction φ).unit.app
            ((PresheafOfModules.free (F.op ⋙ R)).obj (yoneda.obj X)) ≫
          (PresheafOfModules.pushforward φ).map e.hom) := by
    rw [hcomp]
    infer_instance
  let η :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ).unit.app
      ((PresheafOfModules.free (F.op ⋙ R)).obj (yoneda.obj X))
  change IsIso η
  let h := (PresheafOfModules.pushforward φ).map e.hom
  have hIso : IsIso h := by
    dsimp [h]
    exact CategoryTheory.Functor.map_isIso (PresheafOfModules.pushforward φ) e.hom
  have hηIso :
      IsIso
        (η ≫ h) := by
    simpa [η, h] using hcompIso
  exact @CategoryTheory.IsIso.of_isIso_comp_right _ _ _ _ _ η h hIso hηIso

private theorem presheaf_restriction_unit_freeYonedaCoproduct_isIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (R : Dᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules (F.op ⋙ R)) :
    IsIso
      ((PresheafOfModules.pullbackPushforwardAdjunction
          (F := F) (𝟙 (F.op ⋙ R))).unit.app M.freeYonedaCoproduct) := by
  let φ : F.op ⋙ R ⟶ F.op ⋙ R := 𝟙 _
  let τ := (PresheafOfModules.pullbackPushforwardAdjunction φ).unit
  haveI := (PresheafOfModules.pullbackPushforwardAdjunction φ).leftAdjoint_preservesColimits
  exact isIso_natTrans_app_of_isColimit τ
    (D := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := M)))
    (c := Limits.colimit.cocone _)
    (by simpa using (Limits.colimit.isColimit
      (Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := M)))))
    (by
      let D₀ := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := M))
      have hL : Limits.IsColimit
          ((PresheafOfModules.pullback φ).mapCocone (Limits.colimit.cocone D₀)) :=
        Limits.isColimitOfPreserves (PresheafOfModules.pullback φ)
          (Limits.colimit.isColimit D₀)
      change Limits.IsColimit
        ((PresheafOfModules.pushforward₀ F R).mapCocone
          ((PresheafOfModules.pullback φ).mapCocone (Limits.colimit.cocone D₀)))
      exact Limits.isColimitOfPreserves (PresheafOfModules.pushforward₀ F R) hL)
    (fun j => by
      obtain ⟨m⟩ := j
      exact presheaf_restriction_unit_freeYoneda_isIso F R m.1.unop)

private theorem presheaf_restriction_unit_app_isIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (R : Dᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules (F.op ⋙ R)) :
    IsIso
      ((PresheafOfModules.pullbackPushforwardAdjunction
          (F := F) (𝟙 (F.op ⋙ R))).unit.app M) := by
  let φ : F.op ⋙ R ⟶ F.op ⋙ R := 𝟙 _
  let τ := (PresheafOfModules.pullbackPushforwardAdjunction φ).unit
  haveI := (PresheafOfModules.pullbackPushforwardAdjunction φ).leftAdjoint_preservesColimits
  exact isIso_natTrans_app_of_isColimit τ
    (D := Limits.parallelPair M.toFreeYonedaCoproduct 0)
    (c := M.freeYonedaCoproductsCokernelCofork)
    (by simpa using M.isColimitFreeYonedaCoproductsCokernelCofork)
    (by
      have hL : Limits.IsColimit
          ((PresheafOfModules.pullback φ).mapCocone M.freeYonedaCoproductsCokernelCofork) :=
        Limits.isColimitOfPreserves (PresheafOfModules.pullback φ)
          M.isColimitFreeYonedaCoproductsCokernelCofork
      change Limits.IsColimit
        ((PresheafOfModules.pushforward₀ F R).mapCocone
          ((PresheafOfModules.pullback φ).mapCocone M.freeYonedaCoproductsCokernelCofork))
      exact Limits.isColimitOfPreserves (PresheafOfModules.pushforward₀ F R) hL)
    (fun j => by
      match j with
      | Limits.WalkingParallelPair.zero =>
          exact presheaf_restriction_unit_freeYonedaCoproduct_isIso F R
            (Limits.kernel M.fromFreeYonedaCoproduct)
      | Limits.WalkingParallelPair.one =>
          exact presheaf_restriction_unit_freeYonedaCoproduct_isIso F R M)

private instance stalkNeighborhoodRestrictionAdjunction_unit_app_isIso
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u}) (x : X)
    (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x)) :
    IsIso ((𝒪.stalkNeighborhoodRestrictionAdjunction x).unit.app M) := by
  simpa [stalkNeighborhoodRestrictionAdjunction, stalkNeighborhoodRing] using
    (presheaf_restriction_unit_app_isIso
      (OpenNhds.inclusion x) (𝒪 ⋙ forget₂ CommRingCat RingCat) M)

private theorem isIso_of_adjunction_right_map_left_map_comp_counit
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A : C} {B : D} (f : A ⟶ R.obj B)
    [IsIso (adj.unit.app A)]
    (h : IsIso (R.map (L.map f ≫ adj.counit.app B))) :
    IsIso f := by
  have hcomp :
      adj.unit.app A ≫ R.map (L.map f ≫ adj.counit.app B) = f := by
    simp
  haveI : IsIso (adj.unit.app A) := by infer_instance
  haveI : IsIso (R.map (L.map f ≫ adj.counit.app B)) := h
  rw [← hcomp]
  exact CategoryTheory.IsIso.comp_isIso'
    (show IsIso (adj.unit.app A) by infer_instance) h

/-- Helper for Lemma 6.14.2: the normalized raw neighborhood comparison is already an
isomorphism before identifying the two composite pullback routes with the desired source and
target objects. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_hom_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso (stalkNeighborhoodModule_pullbackRawIso p ℱ x).hom := by
  -- The raw comparison is built as a composition of explicit isomorphisms.
  infer_instance

/-- Helper for Lemma 6.14.2: the target of the normalized raw pullback comparison is definitionally
the neighborhood pullback of the restricted module presheaf. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_target_eq
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
          stalkNeighborhoodRingHomOverId p x ≫
            (𝟭 (OpenNhds x)).op.whiskerLeft
              (show stalkNeighborhoodRing 𝒪' x ⟶
                  (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
                𝟙 _))).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) =
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) := by
  rfl

/-- Helper for Lemma 6.14.2: the normalized raw comparison is its own chosen inverse up to the
standard `Iso.inv_hom_id` identity on the local pullback target. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_inv_hom
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (stalkNeighborhoodModule_pullbackRawIso p ℱ x).inv ≫
        (stalkNeighborhoodModule_pullbackRawIso p ℱ x).hom =
      𝟙 _ := by
  -- Record the raw comparison's inverse-cancellation formula explicitly so later endpoint
  -- normalizations can rewrite against a concrete identity rather than reopening the iso package.
  simp

/-- Helper for Lemma 6.14.2: the normalized conjugate comparison comes with an explicit inverse
identity that can be used without reopening the natural-isomorphism package. -/
private theorem stalkNeighborhoodModule_pullbackConjugateIso_inv_hom
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    (stalkNeighborhoodModule_pullbackConjugateIso p x).inv ≫
        (stalkNeighborhoodModule_pullbackConjugateIso p x).hom =
      𝟙 _ := by
  -- Record the inverse-cancellation formula explicitly so later endpoint transport can rewrite
  -- against a concrete identity without reopening the `Iso` structure.
  simp

/-- Helper for Lemma 6.14.2: expanding the single Beck-Chevalley mate shows that its component is
the explicit `unit`/comparison/`counit` composite on neighborhood modules. -/
private theorem stalkNeighborhoodModule_pullbackMate_naturality_counit
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map
        ((𝒪.stalkNeighborhoodRestrictionAdjunction x).unit.app
          ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ)) ≫
      (stalkNeighborhoodModule_pullbackMate p x).app
        ((PresheafOfModules.pullback
          (show stalkNeighborhoodRing 𝒪 x ⟶
              (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
            𝟙 _)).obj
          ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ)) ≫
        (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').map
          ((PresheafOfModules.pullback
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).map
            ((𝒪.stalkNeighborhoodRestrictionAdjunction x).counit.app ℱ)) =
      (stalkNeighborhoodModule_pullbackMate p x).app ℱ := by
  let M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x) :=
    (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ
  let L :=
    PresheafOfModules.pullback
      (show stalkNeighborhoodRing 𝒪 x ⟶
          (OpenNhds.inclusion x).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat) from
        𝟙 _)
  let R := PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪
  let Q := PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)
  let P :=
    PresheafOfModules.pullback
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat))
  let R' := PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪'
  let ε : L.obj M ⟶ ℱ := (𝒪.stalkNeighborhoodRestrictionAdjunction x).counit.app ℱ
  have hnat := (stalkNeighborhoodModule_pullbackMate p x).naturality ε
  have htri :
      (𝒪.stalkNeighborhoodRestrictionAdjunction x).unit.app M ≫ R.map ε = 𝟙 M := by
    exact (𝒪.stalkNeighborhoodRestrictionAdjunction x).right_triangle_components ℱ
  have htriQ : Q.map ((𝒪.stalkNeighborhoodRestrictionAdjunction x).unit.app M) ≫
      Q.map (R.map ε) = 𝟙 (Q.obj M) := by
    simpa [Q, Functor.map_comp] using congrArg (fun f ↦ Q.map f) htri
  have hnat' :
      (stalkNeighborhoodModule_pullbackMate p x).app (L.obj M) ≫ R'.map (P.map ε) =
        Q.map (R.map ε) ≫ (stalkNeighborhoodModule_pullbackMate p x).app ℱ := by
    simpa [Q, P, R, R', ε] using hnat.symm
  let η := (𝒪.stalkNeighborhoodRestrictionAdjunction x).unit.app M
  have h₁ :
      Q.map η ≫ ((stalkNeighborhoodModule_pullbackMate p x).app (L.obj M) ≫ R'.map (P.map ε)) =
        Q.map η ≫ (Q.map (R.map ε) ≫ (stalkNeighborhoodModule_pullbackMate p x).app ℱ) := by
    simpa [η] using congrArg (fun k ↦ Q.map η ≫ k) hnat'
  have h₂ :
      Q.map η ≫ (Q.map (R.map ε) ≫ (stalkNeighborhoodModule_pullbackMate p x).app ℱ) =
        (stalkNeighborhoodModule_pullbackMate p x).app ℱ := by
    simpa [Category.assoc, η] using
      congrArg (fun k ↦ k ≫ (stalkNeighborhoodModule_pullbackMate p x).app ℱ) htriQ
  simpa [M, L, Q, P, R', ε, η] using h₁.trans h₂

private theorem stalkNeighborhoodModule_pullbackMate_app_eq_explicit
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (stalkNeighborhoodModule_pullbackMate p x).app ℱ =
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map
          ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
            ((PresheafOfModules.pullbackPushforwardAdjunction
                    (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                        (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                      Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
              ℱ)) ≫
        (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map
            ((stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.pullback
                  (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                      (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                    Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
                ℱ)) ≫
          (PresheafOfModules.pullbackPushforwardAdjunction
              (stalkNeighborhoodRingHomOverId p x)).counit.app
            ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').obj
              ((PresheafOfModules.pullback
                  (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                      (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                    Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
                ℱ)) := by
  -- Unfold the mate once to isolate the precise composite that must be compared with the
  -- normalized conjugate isomorphism.
  simp [stalkNeighborhoodModule_pullbackMate]

/-- Helper for Lemma 6.14.2: the target of the normalized raw pullback comparison is already the
ordinary neighborhood pullback object. -/
private noncomputable def stalkNeighborhoodModule_pullbackRawIso_targetIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
          stalkNeighborhoodRingHomOverId p x ≫
            (𝟭 (OpenNhds x)).op.whiskerLeft
              (show stalkNeighborhoodRing 𝒪' x ⟶
                  (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
                𝟙 _))).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) ≅
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) :=
  -- The target endpoint is the same pullback object after removing the explicit identity whisker.
  Iso.refl _

/-- Helper for Lemma 6.14.2: the target-endpoint normalization for the raw pullback comparison is
the identity morphism on the underlying neighborhood pullback object. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_targetIso_hom
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (stalkNeighborhoodModule_pullbackRawIso_targetIso p ℱ x).hom = 𝟙 _ := by
  -- The target transport only repackages a definitional equality, so its morphism is identity.
  rfl

/-- Helper for Lemma 6.14.2: restricting the globally pulled-back presheaf to neighborhoods of
`x` leaves the raw source ring morphism unchanged after removing the explicit identity factor on
the source side. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_source_hom_eq
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    (show stalkNeighborhoodRing 𝒪 x ⟶
        (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
      (show stalkNeighborhoodRing 𝒪 x ⟶
          (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪 x from
        𝟙 _) ≫
          (OpenNhds.inclusion x).op.whiskerLeft
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))) =
      (show stalkNeighborhoodRing 𝒪 x ⟶
          (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          (OpenNhds.inclusion x).op.whiskerLeft
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))) := by
  -- The raw source morphism only differs by a left identity factor on `OpenNhds x`.
  rfl

/-- Helper for Lemma 6.14.2: removing the explicit identity whisker does not change the source
pullback functor used in the neighborhood Beck-Chevalley comparison. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_source_functor_eq
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) :
    PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          (show stalkNeighborhoodRing 𝒪 x ⟶
              (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪 x from
            𝟙 _) ≫
              (OpenNhds.inclusion x).op.whiskerLeft
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))) =
      PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          (OpenNhds.inclusion x).op.whiskerLeft
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))) := by
  -- The two pullback functors are equal because their defining ring morphisms are equal.
  cases stalkNeighborhoodModule_pullbackRawIso_source_hom_eq p x
  rfl

/-- Helper for Lemma 6.14.2: the inverse of the target-endpoint normalization is also the identity
morphism on the underlying neighborhood pullback object. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_targetIso_inv
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (stalkNeighborhoodModule_pullbackRawIso_targetIso p ℱ x).inv = 𝟙 _ := by
  -- The target transport is an identity isomorphism, so its inverse is identity as well.
  rfl

/-- Helper for Lemma 6.14.2: the inverse target-side composition comparison with an identity
second factor is the inverse identity-pullback comparison. -/
private theorem stalkNeighborhoodPullback_comp_id_inv_app
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x)) :
    (PresheafOfModules.pullbackComp
        (G := 𝟭 (OpenNhds x))
        (stalkNeighborhoodRingHomOverId p x)
        (show stalkNeighborhoodRing 𝒪' x ⟶
            (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪' x from
          𝟙 _)).inv.app M =
      (PresheafOfModules.pullbackId (stalkNeighborhoodRing 𝒪' x)).inv.app
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj M) := by
  rw [stalkNeighborhoodPullback_comp_id p x]
  simp

/-- Helper for Lemma 6.14.2: after removing the explicit source-side identity whisker in the raw
comparison, the source object is unchanged. -/
private theorem stalkNeighborhoodModule_pullbackRawIso_source_eq
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          (show stalkNeighborhoodRing 𝒪 x ⟶
              (𝟭 (OpenNhds x)).op ⋙ stalkNeighborhoodRing 𝒪 x from
            𝟙 _) ≫
              (OpenNhds.inclusion x).op.whiskerLeft
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat)))).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) =
      (PresheafOfModules.pullback
        (show stalkNeighborhoodRing 𝒪 x ⟶
            (OpenNhds.inclusion x).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          (OpenNhds.inclusion x).op.whiskerLeft
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat)))).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) := by
  -- Rewrite the raw source functor itself first, then the claimed equality becomes reflexive on
  -- the chosen neighborhood module object.
  cases stalkNeighborhoodModule_pullbackRawIso_source_functor_eq p x
  rfl

/-- Helper for Lemma 6.14.2: expanding the neighborhood restriction of the globally pulled-back
presheaf gives the expected pushforward object before the later pullback normalization step. -/
private theorem stalkNeighborhoodModule_global_pullback_eq_pushforward_obj
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    stalkNeighborhoodModule (𝒪 := 𝒪') (ℱ := stalkBaseChangePulledBackModule p ℱ) x =
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').obj
        (stalkBaseChangePulledBackModule p ℱ) := by
  -- This is just the abbreviation `stalkNeighborhoodModule` specialized to the globally
  -- pulled-back presheaf.
  rfl

private theorem stalkNeighborhoodModule_pullbackMate_app_free_mem_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (U : Opens X) (hxU : x ∈ U) :
    IsIso ((stalkNeighborhoodModule_pullbackMate p x).app
      ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))) := by
  let Ux : OpenNhds x := ⟨U, hxU⟩
  let ℱ := ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
  let eR :
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ ≅
        (PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux) :=
    presheaf_pushforward₀_freeYonedaIso
      (OpenNhds.inclusion x) (𝒪 ⋙ forget₂ CommRingCat RingCat) Ux
  let eQ :
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
          ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux)) ≅
        (PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj (yoneda.obj Ux) :=
    presheaf_pullback_freeYonedaIso (stalkNeighborhoodRingHomOverId p x) Ux
  let eSource :
      ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪 ⋙
          PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj ℱ) ≅
        (PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj (yoneda.obj Ux) :=
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).mapIso eR ≪≫ eQ
  let eP :
      (PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ ≅
        (PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U) :=
    presheaf_pullback_freeYonedaIso
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat)) U
  let eR' :
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').obj
          ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ≅
        (PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj (yoneda.obj Ux) :=
    presheaf_pushforward₀_freeYonedaIso
      (OpenNhds.inclusion x) (𝒪' ⋙ forget₂ CommRingCat RingCat) Ux
  let eTarget :
      ((PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
        PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').obj ℱ) ≅
        (PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj (yoneda.obj Ux) :=
    (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').mapIso eP ≪≫ eR'
  let θ :=
    eSource.inv ≫ ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫ eTarget.hom
  have hθ : θ = 𝟙 _ := by
    rw [← cancel_epi eQ.hom]
    apply ((PresheafOfModules.pullbackPushforwardAdjunction
      (stalkNeighborhoodRingHomOverId p x)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have hg := presheaf_pullback_freeYonedaIso_hom_adj
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat)) U
    have hnat := (stalkNeighborhoodPushforwardIso p x).hom.naturality eP.hom
    have hl := presheaf_pullback_freeYonedaIso_hom_adj
      (stalkNeighborhoodRingHomOverId p x) Ux
    simp only [θ, eSource, eTarget, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    simp only [Iso.hom_inv_id_assoc, Functor.map_comp]
    have hunitNat :=
      (PresheafOfModules.pullbackPushforwardAdjunction
        (stalkNeighborhoodRingHomOverId p x)).unit.naturality eR.inv
    have hmate :=
      stalkNeighborhoodModule_pullbackMate_unit_app (𝒪 := 𝒪) (𝒪' := 𝒪') p ℱ x
    have hunitNat' :
        (PresheafOfModules.pullbackPushforwardAdjunction
            (stalkNeighborhoodRingHomOverId p x)).unit.app
            ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux)) ≫
          (PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)).map
            ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map eR.inv) =
        eR.inv ≫
          (PresheafOfModules.pullbackPushforwardAdjunction
            (stalkNeighborhoodRingHomOverId p x)).unit.app
            ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ) := by
      simpa [Functor.comp_map, Category.assoc] using hunitNat.symm
    let Qpush := PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)
    have hunitNat'' :
        (PresheafOfModules.pullbackPushforwardAdjunction
              (stalkNeighborhoodRingHomOverId p x)).unit.app
            ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux)) ≫
          Qpush.map
              ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map eR.inv) ≫
            Qpush.map ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫
              Qpush.map
                ((PresheafOfModules.pushforward₀OfCommRingCat
                  (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
                Qpush.map eR'.hom =
        eR.inv ≫
          (PresheafOfModules.pullbackPushforwardAdjunction
              (stalkNeighborhoodRingHomOverId p x)).unit.app
            ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ) ≫
            Qpush.map ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫
              Qpush.map
                ((PresheafOfModules.pushforward₀OfCommRingCat
                  (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
                Qpush.map eR'.hom := by
      simp [Qpush] at hunitNat' ⊢
    change
      (PresheafOfModules.pullbackPushforwardAdjunction
            (stalkNeighborhoodRingHomOverId p x)).unit.app
          ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux)) ≫
        Qpush.map
            ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map eR.inv) ≫
          Qpush.map ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫
            Qpush.map
              ((PresheafOfModules.pushforward₀OfCommRingCat
                (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
              Qpush.map eR'.hom =
        (PresheafOfModules.pullbackPushforwardAdjunction
            (stalkNeighborhoodRingHomOverId p x)).unit.app
          ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux)) ≫
        Qpush.map eQ.hom ≫
          Qpush.map
            (𝟙 ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj (yoneda.obj Ux)))
    rw [hunitNat'']
    have hmate' :
        eR.inv ≫
          (PresheafOfModules.pullbackPushforwardAdjunction
              (stalkNeighborhoodRingHomOverId p x)).unit.app
            ((PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).obj ℱ) ≫
            Qpush.map ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫
              Qpush.map
                ((PresheafOfModules.pushforward₀OfCommRingCat
                  (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
                Qpush.map eR'.hom =
        eR.inv ≫
          (PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map
            ((PresheafOfModules.pullbackPushforwardAdjunction
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) ≫
            (stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.pullback
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ) ≫
              Qpush.map
                ((PresheafOfModules.pushforward₀OfCommRingCat
                  (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
                Qpush.map eR'.hom := by
      simpa [Qpush, stalkNeighborhoodModule, Category.assoc] using
        congrArg
          (fun f ↦ eR.inv ≫ f ≫
            Qpush.map
              ((PresheafOfModules.pushforward₀OfCommRingCat
                (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
            Qpush.map eR'.hom)
          hmate.symm
    rw [hmate']
    have hnat' :
        eR.inv ≫
          (PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map
            ((PresheafOfModules.pullbackPushforwardAdjunction
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) ≫
            (stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.pullback
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ) ≫
              Qpush.map
                ((PresheafOfModules.pushforward₀OfCommRingCat
                  (OpenNhds.inclusion x) 𝒪').map eP.hom) ≫
              Qpush.map eR'.hom =
        eR.inv ≫
          (PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map
            ((PresheafOfModules.pullbackPushforwardAdjunction
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) ≫
            (PresheafOfModules.pushforward
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
              PresheafOfModules.pushforward₀OfCommRingCat
                (OpenNhds.inclusion x) 𝒪).map eP.hom ≫
              (stalkNeighborhoodPushforwardIso p x).hom.app
                ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                  (yoneda.obj U)) ≫
              Qpush.map eR'.hom := by
      simpa [Qpush, Functor.comp_map, Category.assoc] using
        congrArg
          (fun f ↦ eR.inv ≫
            (PresheafOfModules.pushforward₀OfCommRingCat
                (OpenNhds.inclusion x) 𝒪).map
              ((PresheafOfModules.pullbackPushforwardAdjunction
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) ≫
              f ≫ Qpush.map eR'.hom)
          hnat.symm
    rw [hnat']
    simp only [Functor.comp_map]
    have hglobal :
        eR.inv ≫
          (PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map
            ((PresheafOfModules.pullbackPushforwardAdjunction
                  (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                      (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                    Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) ≫
            (PresheafOfModules.pushforward₀OfCommRingCat
                (OpenNhds.inclusion x) 𝒪).map
              ((PresheafOfModules.pushforward
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))).map eP.hom) ≫
              (stalkNeighborhoodPushforwardIso p x).hom.app
                ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                  (yoneda.obj U)) ≫
              Qpush.map eR'.hom =
        eR.inv ≫
          (PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map
            ((PresheafOfModules.freeYonedaEquiv
              (R := 𝒪 ⋙ forget₂ CommRingCat RingCat)
              (M := (PresheafOfModules.pushforward
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
                  ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                    (yoneda.obj U)))
              (X := U)).symm
              (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)))) ≫
            (stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U)) ≫
            Qpush.map eR'.hom := by
      simpa [Category.assoc, Functor.map_comp] using
        congrArg
          (fun f ↦ eR.inv ≫
            (PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map f ≫
            (stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U)) ≫
            Qpush.map eR'.hom)
          hg
    refine hglobal.trans ?_
    simp only [Qpush]
    apply PresheafOfModules.freeYonedaEquiv.injective
    let ηlocal :=
      (PresheafOfModules.pullbackPushforwardAdjunction
        (stalkNeighborhoodRingHomOverId p x)).unit.app
          ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪 x)).obj (yoneda.obj Ux))
    change
      PresheafOfModules.freeYonedaEquiv
          (eR.inv ≫
            (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
              (PresheafOfModules.freeYonedaEquiv.symm
                (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)))) ≫
            (stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U)) ≫
            Qpush.map eR'.hom) =
        PresheafOfModules.freeYonedaEquiv
          (ηlocal ≫ Qpush.map eQ.hom ≫
            Qpush.map
              (𝟙 ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj
                (yoneda.obj Ux))))
    have hRhsMorph :
        ηlocal ≫ Qpush.map eQ.hom ≫
            Qpush.map
              (𝟙 ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj
                (yoneda.obj Ux))) =
          PresheafOfModules.freeYonedaEquiv.symm
            (ModuleCat.freeMk (𝟙 ((𝟭 (OpenNhds x)).obj Ux))) := by
      simpa [ηlocal, Qpush] using hl
    have hRhs :
        PresheafOfModules.freeYonedaEquiv
          (ηlocal ≫ Qpush.map eQ.hom ≫
            Qpush.map
              (𝟙 ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj
                (yoneda.obj Ux)))) =
          ModuleCat.freeMk (𝟙 ((𝟭 (OpenNhds x)).obj Ux)) := by
      exact
        (congrArg
          (fun f ↦
            (PresheafOfModules.freeYonedaEquiv
              (M := Qpush.obj
                ((PresheafOfModules.free (stalkNeighborhoodRing 𝒪' x)).obj
                  (yoneda.obj Ux)))
              (X := Ux)) f)
          hRhsMorph).trans
          (Equiv.apply_symm_apply _ _)
    rw [hRhs]
    have heRgen :
        PresheafOfModules.freeYonedaEquiv eR.inv =
          ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)) := by
      change (eR.inv.app (op Ux)) (ModuleCat.freeMk (𝟙 Ux)) =
        ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))
      dsimp [eR, presheaf_pushforward₀_freeYonedaIso, yonedaWhiskerFullyFaithfulIso,
        Functor.FullyFaithful.homEquiv]
      change (((ModuleCat.free ↑(𝒪.obj (op ((OpenNhds.inclusion x).obj Ux)))).map
        (OpenNhds.inclusion x).map) (ModuleCat.freeMk (𝟙 Ux))) =
          ModuleCat.freeMk (𝟙 U)
      rw [ModuleCat.free_map_apply]
      rfl
    rw [PresheafOfModules.freeYonedaEquiv_comp]
    rw [heRgen]
    let Mglob : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat) :=
      (PresheafOfModules.pushforward
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
        ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
    let fglob : ℱ ⟶ Mglob :=
      (PresheafOfModules.freeYonedaEquiv (M := Mglob) (X := U)).symm
        (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)))
    have hGlobalGen :
        (((PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map fglob).app (op Ux))
            (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))) =
          ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)) := by
      change (fglob.app (op U)) (ModuleCat.freeMk (𝟙 U)) =
        ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))
      simpa [fglob] using
        (PresheafOfModules.freeYonedaEquiv_symm_app
          Mglob U (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))))
    have hFirst :
        (((PresheafOfModules.pushforward₀OfCommRingCat
              (OpenNhds.inclusion x) 𝒪).map
            (show ℱ ⟶ Mglob from
              PresheafOfModules.freeYonedaEquiv.symm
                (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))))).app (op Ux))
            (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))) =
          ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)) := by
      simpa [Mglob, fglob] using hGlobalGen
    have hPushIsoGen :
        (((stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                (yoneda.obj U))).app (op Ux))
            (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U))) =
          ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)) := by
      rfl
    have heR'gen :
        (((Qpush.map eR'.hom).app (op Ux))
            (ModuleCat.freeMk (𝟙 ((𝟭 (Opens X)).obj U)))) =
          ModuleCat.freeMk (𝟙 ((𝟭 (OpenNhds x)).obj Ux)) := by
      dsimp [Qpush, eR', presheaf_pushforward₀_freeYonedaIso,
        yonedaWhiskerFullyFaithfulIso, Functor.FullyFaithful.homEquiv]
      change (((ModuleCat.free ↑(𝒪'.obj (op ((OpenNhds.inclusion x).obj Ux)))).map
        (fun f : (OpenNhds.inclusion x).obj Ux ⟶ (OpenNhds.inclusion x).obj Ux =>
          (OpenNhds.inclusion x).preimage f))
          (ModuleCat.freeMk (𝟙 U))) =
        ModuleCat.freeMk (𝟙 Ux)
      rw [ModuleCat.free_map_apply]
      change ModuleCat.freeMk
          ((OpenNhds.inclusion x).preimage (𝟙 ((OpenNhds.inclusion x).obj Ux))) =
        ModuleCat.freeMk (𝟙 Ux)
      simp
    rw [PresheafOfModules.comp_app, PresheafOfModules.comp_app]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    exact
      (congrArg
        (fun z =>
          (ConcreteCategory.hom ((Qpush.map eR'.hom).app (op Ux)))
            ((ConcreteCategory.hom
              (((stalkNeighborhoodPushforwardIso p x).hom.app
                ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
                  (yoneda.obj U))).app (op Ux))) z))
        hFirst).trans
      ((congrArg
        (fun z => (ConcreteCategory.hom ((Qpush.map eR'.hom).app (op Ux))) z)
        hPushIsoGen).trans heR'gen)
  haveI : IsIso θ := by
    rw [hθ]
    infer_instance
  have hcomp : IsIso (eSource.inv ≫
      (((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫ eTarget.hom)) := by
    simpa [θ, Category.assoc] using (show IsIso θ by infer_instance)
  have htail : IsIso (((stalkNeighborhoodModule_pullbackMate p x).app ℱ) ≫ eTarget.hom) :=
    (isIso_comp_left_iff eSource.inv _).1 hcomp
  exact (isIso_comp_right_iff ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) eTarget.hom).1
    htail

private theorem stalkNeighborhood_pushforward₀_freeYoneda_not_mem_isZero
    {X : TopCat.{u}} (𝒪 : X.Presheaf CommRingCat.{u})
    (x : X) (U : Opens X) (hxU : x ∉ U) :
    Limits.IsZero
      ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj
        ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
          (yoneda.obj U))) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  ext W m
  have hsub : Subsingleton
      (((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj
        ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj
          (yoneda.obj U))).obj W) := by
    dsimp [PresheafOfModules.free, PresheafOfModules.freeObj, ModuleCat.free,
      PresheafOfModules.pushforward₀OfCommRingCat, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀_obj]
    constructor
    intro a b
    ext i
    exact False.elim (hxU ((i ⟨x, W.unop.2⟩).2))
  exact Subsingleton.elim _ _

private theorem stalkNeighborhoodModule_pullbackMate_app_free_not_mem_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (U : Opens X) (hxU : x ∉ U) :
    IsIso ((stalkNeighborhoodModule_pullbackMate p x).app
      ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))) := by
  let ℱ := ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
  let M0 :=
    (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).obj ℱ
  have hM0 : Limits.IsZero M0 := by
    simpa [M0, ℱ] using stalkNeighborhood_pushforward₀_freeYoneda_not_mem_isZero 𝒪 x U hxU
  have hSource :
      Limits.IsZero
        ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪 ⋙
          PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj ℱ) := by
    haveI : Limits.PreservesColimit
        (Functor.empty.{0} (PresheafOfModules (stalkNeighborhoodRing 𝒪 x)))
        (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)) := by
      let hpres :=
        (PresheafOfModules.pullbackPushforwardAdjunction
          (stalkNeighborhoodRingHomOverId p x)).leftAdjoint_preservesColimits
      exact hpres.preservesColimitsOfShape.preservesColimit
    simpa [M0, ℱ] using
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).map_isZero hM0
  let eP :
      (PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ ≅
        (PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U) :=
    presheaf_pullback_freeYonedaIso
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat)) U
  have hTargetZeroBase :
      Limits.IsZero
        ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').obj
          ((PresheafOfModules.free (𝒪' ⋙ forget₂ CommRingCat RingCat)).obj
            (yoneda.obj U))) := by
    exact stalkNeighborhood_pushforward₀_freeYoneda_not_mem_isZero 𝒪' x U hxU
  have hTarget :
      Limits.IsZero
        ((PresheafOfModules.pullback
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
          PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').obj ℱ) := by
    exact hTargetZeroBase.of_iso
      ((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').mapIso eP)
  exact hSource.isIso hTarget ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)

/-- Helper for Lemma 6.14.2: the source functor in the mixed neighborhood
Beck-Chevalley mate preserves the colimits used in the free-Yoneda presentation. -/
private noncomputable def stalkNeighborhoodModule_pullbackMate_source_mapCocone_isColimit
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    {J : Type*} [SmallCategory J] [Limits.HasColimitsOfShape J AddCommGrpCat.{u}]
    {D : J ⥤ PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {c : Limits.Cocone D} (hc : Limits.IsColimit c) :
    Limits.IsColimit
      (((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪 ⋙
        PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).mapCocone c)) := by
  haveI :=
    (PresheafOfModules.pullbackPushforwardAdjunction
      (stalkNeighborhoodRingHomOverId p x)).leftAdjoint_preservesColimits
  haveI : Limits.PreservesColimit D
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪) :=
    (presheaf_pushforward₀_preservesColimitsOfShape
      (J := J) (OpenNhds.inclusion x) (𝒪 ⋙ forget₂ CommRingCat RingCat)).preservesColimit
  exact Limits.isColimitOfPreserves
    (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x))
    (Limits.isColimitOfPreserves
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪) hc)

/-- Helper for Lemma 6.14.2: the target functor in the mixed neighborhood
Beck-Chevalley mate preserves the colimits used in the free-Yoneda presentation. -/
private noncomputable def stalkNeighborhoodModule_pullbackMate_target_mapCocone_isColimit
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    {J : Type*} [SmallCategory J] [Limits.HasColimitsOfShape J AddCommGrpCat.{u}]
    {D : J ⥤ PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {c : Limits.Cocone D} (hc : Limits.IsColimit c) :
    Limits.IsColimit
      (((PresheafOfModules.pullback
          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p (forget₂ CommRingCat RingCat)) ⋙
        PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪').mapCocone c)) := by
  haveI :=
    (PresheafOfModules.pullbackPushforwardAdjunction
      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p (forget₂ CommRingCat RingCat))).leftAdjoint_preservesColimits
  haveI : Limits.PreservesColimit
      (D ⋙ PresheafOfModules.pullback
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat)))
      (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪') :=
    (presheaf_pushforward₀_preservesColimitsOfShape
      (J := J) (OpenNhds.inclusion x) (𝒪' ⋙ forget₂ CommRingCat RingCat)).preservesColimit
  exact Limits.isColimitOfPreserves
    (PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪')
    (Limits.isColimitOfPreserves
      (PresheafOfModules.pullback
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))) hc)

/-- Helper for Lemma 6.14.2: the mixed Beck-Chevalley mate is an isomorphism on every
global free-Yoneda generator. -/
private theorem stalkNeighborhoodModule_pullbackMate_app_free_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (U : Opens X) :
    IsIso ((stalkNeighborhoodModule_pullbackMate p x).app
      ((PresheafOfModules.free (𝒪 ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))) := by
  by_cases hxU : x ∈ U
  · exact stalkNeighborhoodModule_pullbackMate_app_free_mem_isIso p x U hxU
  · exact stalkNeighborhoodModule_pullbackMate_app_free_not_mem_isIso p x U hxU

/-- Helper for Lemma 6.14.2: the mixed Beck-Chevalley mate is an isomorphism on coproducts
of global free-Yoneda generators. -/
private theorem stalkNeighborhoodModule_pullbackMate_app_freeYonedaCoproduct_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (M : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    IsIso ((stalkNeighborhoodModule_pullbackMate p x).app M.freeYonedaCoproduct) := by
  exact isIso_natTrans_app_of_isColimit (stalkNeighborhoodModule_pullbackMate p x)
    (D := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := M)))
    (c := Limits.colimit.cocone _)
    (stalkNeighborhoodModule_pullbackMate_source_mapCocone_isColimit p x (Limits.colimit.isColimit _))
    (stalkNeighborhoodModule_pullbackMate_target_mapCocone_isColimit p x (Limits.colimit.isColimit _))
    (fun j => by
      obtain ⟨m⟩ := j
      exact stalkNeighborhoodModule_pullbackMate_app_free_isIso p x m.1.unop)

/-- Helper for Lemma 6.14.2: the mixed Beck-Chevalley mate on neighborhood modules is the actual
comparison map whose inverse gives the desired restriction/globalization isomorphism. -/
private instance stalkNeighborhoodModule_pullbackMate_app_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) := by
  exact isIso_natTrans_app_of_isColimit (stalkNeighborhoodModule_pullbackMate p x)
    (D := Limits.parallelPair ℱ.toFreeYonedaCoproduct 0)
    (c := ℱ.freeYonedaCoproductsCokernelCofork)
    (stalkNeighborhoodModule_pullbackMate_source_mapCocone_isColimit p x
      ℱ.isColimitFreeYonedaCoproductsCokernelCofork)
    (stalkNeighborhoodModule_pullbackMate_target_mapCocone_isColimit p x
      ℱ.isColimitFreeYonedaCoproductsCokernelCofork)
    (fun j => by
      match j with
      | Limits.WalkingParallelPair.zero =>
          exact stalkNeighborhoodModule_pullbackMate_app_freeYonedaCoproduct_isIso p x
            (Limits.kernel ℱ.fromFreeYonedaCoproduct)
      | Limits.WalkingParallelPair.one =>
          exact stalkNeighborhoodModule_pullbackMate_app_freeYonedaCoproduct_isIso p x ℱ)

/-- Helper for Lemma 6.14.2: restricting the globally pulled-back presheaf to neighborhoods of
`x` is canonically isomorphic to pulling back the neighborhood module presheaf along the induced
neighborhood ring morphism. -/
private noncomputable def stalkNeighborhoodModule_pullbackIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    stalkNeighborhoodModule (𝒪 := 𝒪') (ℱ := stalkBaseChangePulledBackModule p ℱ) x ≅
      (PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x) :=
  -- Once the mixed Beck-Chevalley mate is known to be invertible, the required comparison is just
  -- its inverse orientation.
  (asIso ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).symm

/-- Helper for Lemma 6.14.2: the target of the ordinary stalk comparison identifies with the
actual neighborhood-pullback colimit object used in `stalkActualPullbackAdjunction`. -/
private noncomputable def stalkActualPullbackTargetIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ModuleCat.of (𝒪'.stalk x)
        ↑(stalk
          ((PresheafOfModules.pullback
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ).presheaf x) ≅
      ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
          PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x)) := by
  -- Apply the actual-stalk module comparison to the globally pulled-back presheaf and rewrite the
  -- neighborhood module presheaf by the canonical neighborhood pullback isomorphism.
  exact
    (stalkNeighborhoodActualStalkModuleIso 𝒪'
      (stalkBaseChangePulledBackModule p ℱ) x) ≪≫
      (PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).mapIso
        (stalkNeighborhoodModule_pullbackIso p ℱ x)

/-- Helper for Lemma 6.14.2: once a transported comparison map has the same adjunction image as
the unit of `stalkActualPullbackAdjunction`, it is exactly the `leftAdjointUniq` component. -/
private theorem eq_leftAdjointUniq_app_of_homEquiv_eq_unit
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') (x : X)
    (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x))
    (f :
      ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x) ⋙
          ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj M) ⟶
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
            PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
          M))
    (hf :
      (stalkActualBaseChangeAdjunction p x).homEquiv _ _ f =
        (stalkActualPullbackAdjunction p x).unit.app M) :
    f =
      ((Adjunction.leftAdjointUniq
          (stalkActualBaseChangeAdjunction p x)
          (stalkActualPullbackAdjunction p x)).hom.app M) := by
  -- Compare both morphisms through the same `homEquiv`; the left-adjoint uniqueness component is
  -- characterized exactly by mapping to the unit of the second adjunction.
  apply ((stalkActualBaseChangeAdjunction p x).homEquiv _ _).injective
  simpa using hf.trans
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (stalkActualBaseChangeAdjunction p x)
      (stalkActualPullbackAdjunction p x)
      M).symm

/-- Helper for Lemma 6.14.2: the conjugated form of `stalkBaseChangeComparison` on the actual
stalk source and target objects. -/
private noncomputable abbrev stalkBaseChangeComparisonTransported
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x) ⋙
          ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x)) ⟶
      ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
          PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
        (stalkNeighborhoodModule 𝒪 ℱ x)) :=
  ((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
      (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x)).inv ≫
    stalkBaseChangeComparison p ℱ x ≫
    (stalkActualPullbackTargetIso p ℱ x).hom

/-- Helper for Lemma 6.14.2: the transported comparison map is by definition the conjugate of the
original stalk base-change comparison by the source and target transport isomorphisms. -/
private theorem stalkBaseChangeComparisonTransported_eq
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    stalkBaseChangeComparisonTransported p ℱ x =
      ((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
          (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x)).inv ≫
        stalkBaseChangeComparison p ℱ x ≫
          (stalkActualPullbackTargetIso p ℱ x).hom := by
  -- This records the exact transported morphism that remains to be identified via adjunction.
  rfl

/-- Helper for Lemma 6.14.2: transposing the transported base-change comparison through
extension/restriction removes the source and target transport isomorphisms. -/
private theorem stalkBaseChangeComparisonTransported_extendTranspose_eq
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ((ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom)).homEquiv
        ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x)).obj
          (stalkNeighborhoodModule 𝒪 ℱ x))
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
            PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
          (stalkNeighborhoodModule 𝒪 ℱ x)))
      (((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
            (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x)).inv ≫
        stalkBaseChangeComparison p ℱ x ≫
          (stalkActualPullbackTargetIso p ℱ x).hom) =
      (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x).inv ≫
        stalkModuleMapToRestrict p
          ((PresheafOfModules.pullbackPushforwardAdjunction
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) x ≫
          (ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).map
            (stalkActualPullbackTargetIso p ℱ x).hom := by
  let f := (((stalkFunctor CommRingCat x).map p).hom)
  let sourceIso := stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x
  let targetIso := stalkActualPullbackTargetIso p ℱ x
  let g :=
    stalkModuleMapToRestrict p
      ((PresheafOfModules.pullbackPushforwardAdjunction
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ) x
  rw [stalkBaseChangeComparison]
  change ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _)
      ((ModuleCat.extendScalars f).map sourceIso.inv ≫
        ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm g ≫
          targetIso.hom) =
    sourceIso.inv ≫ g ≫ (ModuleCat.restrictScalars f).map targetIso.hom
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rw [Equiv.apply_symm_apply]
  rfl

/-- Helper for Lemma 6.14.2: the actual-stalk base-change adjunction hom-equivalence is the
composite of the extension-of-scalars hom-equivalence with the neighborhood-colimit
hom-equivalence. -/
private theorem stalkActualBaseChangeAdjunction_homEquiv_apply
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (x : X) (M : PresheafOfModules (stalkNeighborhoodRing 𝒪 x))
    (N : ModuleCat (𝒪'.stalk x))
    (f :
      ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x) ⋙
          ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        M) ⟶
        N) :
    (stalkActualBaseChangeAdjunction p x).homEquiv M N f =
      (PresheafOfModules.colimitAdjunction (stalkNeighborhoodActualStalkIsColimit 𝒪 x)).homEquiv
          M
          ((ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).obj N)
          (((ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom)).homEquiv
              _ _ f)) := by
  -- Unfold the composed adjunction once so later rewrites can use the nested `homEquiv`
  -- description without rederiving the `Equiv.trans` normalization.
  let hcomp :=
    congrArg (fun e ↦ e f) <|
      congrFun
        (congrFun
          (Adjunction.comp_homEquiv
            (adj₁ := PresheafOfModules.colimitAdjunction (stalkNeighborhoodActualStalkIsColimit 𝒪 x))
            (adj₂ := ModuleCat.extendRestrictScalarsAdj
              (((stalkFunctor CommRingCat x).map p).hom)))
          M)
        N
  simpa [stalkActualBaseChangeAdjunction, Equiv.trans_apply] using hcomp

/-- Helper for Lemma 6.14.2: evaluating a colimit-adjunction unit followed by a constant
module map on a neighborhood section gives the map applied to the colimit generator. -/
private theorem colimitAdjunction_unit_map_app_apply
    {C : Type u} [Category.{u} C] [LocallySmall.{u, u, u} C]
    [IsCofiltered C] [InitiallySmall C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {cR : CategoryTheory.Limits.Cocone R}
    (hcR : CategoryTheory.Limits.IsColimit cR)
    (F : PresheafOfModules.{u} R) (G : ModuleCat.{u} cR.pt)
    (β : (PresheafOfModules.colimitFunctor hcR).obj F ⟶ G)
    (U : Cᵒᵖ) (m : F.obj U) :
    ModuleCat.Hom.hom
      ((((PresheafOfModules.colimitAdjunction hcR).unit.app F) ≫
        (PresheafOfModules.constFunctor cR).map β).app U) m =
    ModuleCat.Hom.hom β
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR)
        (hcM := CategoryTheory.Limits.colimit.isColimit F.presheaf) m) := by
  rw [PresheafOfModules.comp_app, ModuleCat.hom_comp]
  change ModuleCat.Hom.hom (((PresheafOfModules.constFunctor cR).map β).app U)
      (ModuleCat.Hom.hom (((PresheafOfModules.colimitAdjunction hcR).unit.app F).app U) m) =
    ModuleCat.Hom.hom β (PresheafOfModules.ModuleColimit.ιM m)
  rw [show ModuleCat.Hom.hom (((PresheafOfModules.colimitAdjunction hcR).unit.app F).app U) m =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR)
        (hcM := CategoryTheory.Limits.colimit.isColimit F.presheaf) m by rfl]
  rfl

/-- Helper for Lemma 6.14.2: evaluating the underlying linear map of a composite morphism in
`ModuleCat` is ordinary function composition. -/
private theorem moduleCat_hom_comp_apply
    {R : Type u} [Ring R] {M N P : ModuleCat.{u} R}
    (f : M ⟶ N) (g : N ⟶ P) (m : M) :
    ModuleCat.Hom.hom (f ≫ g) m =
      ModuleCat.Hom.hom g (ModuleCat.Hom.hom f m) := by
  rfl

/-- Helper for Lemma 6.14.2: evaluating the underlying linear map of a restricted morphism does
not change the underlying element map. -/
private theorem moduleCat_hom_restrictScalars_map_apply
    {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    {M N : ModuleCat.{u} S} (g : M ⟶ N)
    (m : (ModuleCat.restrictScalars f).obj M) :
    ModuleCat.Hom.hom ((ModuleCat.restrictScalars f).map g) m =
      ModuleCat.Hom.hom g m := by
  rfl

/-- Helper for Lemma 6.14.2: evaluating the identity morphism through `ModuleCat.Hom.hom`
fixes the element. -/
private theorem moduleCat_hom_id_apply
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (m : M) :
    ModuleCat.Hom.hom (𝟙 M) m = m := by
  rfl

/-- Helper for Lemma 6.14.2: the inverse of the colimit map induced by an isomorphism sends a
colimit generator to the generator obtained by applying the inverse componentwise. -/
private theorem colimitFunctor_map_inv_apply
    {C : Type u} [Category.{u} C] [LocallySmall.{u, u, u} C]
    [IsCofiltered C] [InitiallySmall C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {cR : CategoryTheory.Limits.Cocone R}
    (hcR : CategoryTheory.Limits.IsColimit cR)
    {F G : PresheafOfModules.{u} R} (η : F ⟶ G) [IsIso η]
    (U : Cᵒᵖ) (m : G.obj U) :
    ModuleCat.Hom.hom (inv ((PresheafOfModules.colimitFunctor hcR).map η))
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcR)
          (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR)
        (hcM := CategoryTheory.Limits.colimit.isColimit F.presheaf)
        (ModuleCat.Hom.hom ((inv η).app U) m) := by
  let ηc := (PresheafOfModules.colimitFunctor hcR).map η
  apply
    (show Function.Injective (fun z ↦ ModuleCat.Hom.hom ηc z) from by
      intro a b h
      have h' := congrArg (fun z ↦ ModuleCat.Hom.hom (inv ηc) z) h
      simpa [ηc, ModuleCat.hom_comp, Category.assoc] using h')
  have hleft :
      ModuleCat.Hom.hom ηc
          (ModuleCat.Hom.hom (inv ηc)
            (PresheafOfModules.ModuleColimit.ιM
              (hcR := hcR)
              (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m)) =
        PresheafOfModules.ModuleColimit.ιM
          (hcR := hcR)
          (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m := by
    change ModuleCat.Hom.hom (inv ηc ≫ ηc)
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcR)
          (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR)
        (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m
    rw [IsIso.inv_hom_id]
    rfl
  have hright :
      ModuleCat.Hom.hom ηc
          (PresheafOfModules.ModuleColimit.ιM
            (hcR := hcR)
            (hcM := CategoryTheory.Limits.colimit.isColimit F.presheaf)
            (ModuleCat.Hom.hom ((inv η).app U) m)) =
        PresheafOfModules.ModuleColimit.ιM
          (hcR := hcR)
          (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m := by
    change PresheafOfModules.ModuleColimit.map hcR
        (CategoryTheory.Limits.colimit.isColimit F.presheaf)
        (CategoryTheory.Limits.colimit.isColimit G.presheaf) η
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcR)
          (hcM := CategoryTheory.Limits.colimit.isColimit F.presheaf)
          (ModuleCat.Hom.hom ((inv η).app U) m)) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR)
        (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) m
    have hη : (inv η).app U ≫ η.app U = 𝟙 _ := by
      have h := congrArg (fun f ↦ f.app U) (IsIso.inv_hom_id η)
      change (inv η).app U ≫ η.app U = 𝟙 _ at h
      exact h
    rw [PresheafOfModules.ModuleColimit.map_apply]
    exact congrArg
      (fun y ↦ PresheafOfModules.ModuleColimit.ιM
        (hcR := hcR)
        (hcM := CategoryTheory.Limits.colimit.isColimit G.presheaf) y)
      (ConcreteCategory.congr_hom hη m)
  exact hleft.trans hright.symm

/-- Helper for Lemma 6.14.2: applying the extension/restriction adjunction unit and then the
restricted transpose recovers the original restricted map on elements. -/
private theorem extendRestrictScalarsAdj_unit_homEquiv_symm_apply
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj N) (m : M) :
    ModuleCat.Hom.hom
        (((ModuleCat.extendRestrictScalarsAdj f).unit.app M) ≫
          (ModuleCat.restrictScalars f).map
            (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g))
        m =
      ModuleCat.Hom.hom g m := by
  have h :
      (ModuleCat.extendRestrictScalarsAdj f).unit.app M ≫
          (ModuleCat.restrictScalars f).map
            (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g) =
        g :=
    (Adjunction.homEquiv_unit
      (adj := ModuleCat.extendRestrictScalarsAdj f)
      (f := (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm g))).symm.trans
      (Equiv.apply_symm_apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N) g)
  exact congrArg (fun k ↦ ModuleCat.Hom.hom k m) h

/-- Helper for Lemma 6.14.2: the stalk map into a restricted target sends a germ to the germ of
the sectionwise map. -/
private theorem stalkModuleMapToRestrict_germ_apply
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)}
    {𝒢 : PresheafOfModules (𝒪' ⋙ forget₂ CommRingCat RingCat)}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj 𝒢)
    (x : X) (U : Opens X) (hxU : x ∈ U) (m : ℱ.obj (op U)) :
    ModuleCat.Hom.hom (stalkModuleMapToRestrict p φ x)
        (TopCat.Presheaf.germ ℱ.presheaf U x hxU m) =
      TopCat.Presheaf.germ 𝒢.presheaf U x hxU (φ.app (op U) m) := by
  simpa [stalkModuleMapToRestrict, stalkUnderlyingMapToRestricted,
    underlyingPresheafMapToRestricted] using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      (underlyingPresheafMapToRestricted p φ) m)

/-- Helper for Lemma 6.14.2: evaluating the neighborhood mate-unit identity at a fixed
neighborhood generator gives the pointwise equality that the remaining actual-stalk transport must
match. -/
private theorem stalkNeighborhoodModule_pullbackMate_unit_app_on_sections
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : (OpenNhds x)ᵒᵖ) (m : ↑((stalkNeighborhoodModule 𝒪 ℱ x).obj U)) :
    (ModuleCat.Hom.hom
        (((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
                ((PresheafOfModules.pullbackPushforwardAdjunction
                        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
                  ℱ)).app U ≫
            ((stalkNeighborhoodPushforwardIso p x).hom.app
                  ((PresheafOfModules.pullback
                      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                        Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
                    ℱ)).app U))
      m =
      (ModuleCat.Hom.hom
        ((((PresheafOfModules.pullbackPushforwardAdjunction
                  (stalkNeighborhoodRingHomOverId p x)).unit.app
                (stalkNeighborhoodModule 𝒪 ℱ x)).app U) ≫
            (((PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)).map
                    ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).app U)))
      m := by
  -- Evaluate the natural-transformation identity at `U`, then apply the resulting module map to
  -- the chosen section `m`.
  exact congrArg (fun f ↦ ModuleCat.Hom.hom (f.app U) m)
    (stalkNeighborhoodModule_pullbackMate_unit_app (𝒪 := 𝒪) (𝒪' := 𝒪') p ℱ x)

/-- Helper for Lemma 6.14.2: after applying the neighborhood mate identity and the inverse mate,
the pointwise section is the local pullback unit section. -/
private theorem stalkNeighborhoodModule_inverse_mate_after_hpoint
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : (OpenNhds x)ᵒᵖ) (m : ↑((stalkNeighborhoodModule 𝒪 ℱ x).obj U)) :
    ModuleCat.Hom.hom
        ((inv ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).app U)
        (ModuleCat.Hom.hom
          (((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
                  ((PresheafOfModules.pullbackPushforwardAdjunction
                          (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                              (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                            Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
                    ℱ)).app U ≫
              ((stalkNeighborhoodPushforwardIso p x).hom.app
                    ((PresheafOfModules.pullback
                        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
                      ℱ)).app U)
          m) =
      ModuleCat.Hom.hom
        (((PresheafOfModules.pullbackPushforwardAdjunction
                  (stalkNeighborhoodRingHomOverId p x)).unit.app
                (stalkNeighborhoodModule 𝒪 ℱ x)).app U)
        m := by
  have hpoint :=
    stalkNeighborhoodModule_pullbackMate_unit_app_on_sections
      (𝒪 := 𝒪) (𝒪' := 𝒪') p ℱ x U m
  rw [hpoint]
  let η := (stalkNeighborhoodModule_pullbackMate p x).app ℱ
  let a :=
    ModuleCat.Hom.hom
      (((PresheafOfModules.pullbackPushforwardAdjunction
                (stalkNeighborhoodRingHomOverId p x)).unit.app
              (stalkNeighborhoodModule 𝒪 ℱ x)).app U)
      m
  have hpush :
      ModuleCat.Hom.hom
        (((PresheafOfModules.pushforward (stalkNeighborhoodRingHomOverId p x)).map η).app U)
        a =
      ModuleCat.Hom.hom (η.app U) a := by
    simpa [η, a] using
      (PresheafOfModules.pushforward_map_app_apply
        (stalkNeighborhoodRingHomOverId p x) η U a)
  rw [ModuleCat.hom_comp]
  change ModuleCat.Hom.hom ((inv η).app U)
      (ModuleCat.Hom.hom (((PresheafOfModules.pushforward
        (stalkNeighborhoodRingHomOverId p x)).map η).app U) a) = a
  rw [hpush]
  change ModuleCat.Hom.hom (η.app U ≫ (inv η).app U) a = a
  have hη : η.app U ≫ (inv η).app U = 𝟙 _ := by
    have h := congrArg (fun f ↦ f.app U) (IsIso.hom_inv_id η)
    change η.app U ≫ (inv η).app U = 𝟙 _ at h
    exact h
  rw [hη]
  rfl

/-- Helper for Lemma 6.14.2: the target transport sends an ordinary target stalk germ to the
corresponding inverse-mate generator in the actual target colimit. -/
private theorem stalkActualPullbackTargetIso_restrictScalars_hom_germ_apply
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : OpenNhds x)
    (s : ↑((stalkNeighborhoodModule (𝒪 := 𝒪')
        (ℱ := stalkBaseChangePulledBackModule p ℱ) x).obj (op U))) :
    ModuleCat.Hom.hom
      ((ModuleCat.restrictScalars (CommRingCat.Hom.hom ((stalkFunctor CommRingCat x).map p))).map
        (stalkActualPullbackTargetIso p ℱ x).hom)
      (TopCat.Presheaf.germ (stalkBaseChangePulledBackModule p ℱ).presheaf U.1 x U.2 s) =
    PresheafOfModules.ModuleColimit.ιM
      (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪' x)
      (hcM := CategoryTheory.Limits.colimit.isColimit
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
          (stalkNeighborhoodModule 𝒪 ℱ x)).presheaf)
      (ModuleCat.Hom.hom ((inv ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).app (op U)) s) := by
  rw [moduleCat_hom_restrictScalars_map_apply]
  dsimp [stalkActualPullbackTargetIso]
  change ModuleCat.Hom.hom
      ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).map
        (stalkNeighborhoodModule_pullbackIso p ℱ x).hom)
      (ModuleCat.Hom.hom
        (stalkNeighborhoodActualStalkModuleIso 𝒪'
          (stalkBaseChangePulledBackModule p ℱ) x).hom
        (TopCat.Presheaf.germ (stalkBaseChangePulledBackModule p ℱ).presheaf U.1 x U.2 s)) =
    PresheafOfModules.ModuleColimit.ιM
      (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪' x)
      (hcM := CategoryTheory.Limits.colimit.isColimit
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
          (stalkNeighborhoodModule 𝒪 ℱ x)).presheaf)
      (ModuleCat.Hom.hom ((inv ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).app (op U)) s)
  rw [stalkNeighborhoodActualStalkModuleIso_hom_apply]
  rw [show
      (show ↑(stalkNeighborhoodActualStalkModule 𝒪'
          (stalkBaseChangePulledBackModule p ℱ) x) from
        TopCat.Presheaf.germ (stalkBaseChangePulledBackModule p ℱ).presheaf U.1 x U.2 s) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪' x)
        (hcM := CategoryTheory.Limits.colimit.isColimit
          (stalkNeighborhoodModule 𝒪'
            (stalkBaseChangePulledBackModule p ℱ) x).presheaf)
        s by
    simpa using
      (stalkNeighborhoodModule_colimit_ι_eq_germ 𝒪'
        (stalkBaseChangePulledBackModule p ℱ) x U.1 U.2 s).symm]
  simpa [stalkActualPullbackTargetIso, stalkNeighborhoodModule_pullbackIso] using
    (colimitFunctor_map_inv_apply
      (stalkNeighborhoodActualStalkIsColimit 𝒪' x)
      ((stalkNeighborhoodModule_pullbackMate p x).app ℱ) (op U) s)

/-- Helper for Lemma 6.14.2: the transported ordinary stalk comparison sends a neighborhood
generator to the inverse-mate generator in the actual target stalk. -/
private theorem stalkActualTransportedComparison_source_generator
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : (OpenNhds x)ᵒᵖ) (m : ↑((stalkNeighborhoodModule 𝒪 ℱ x).obj U)) :
    (ModuleCat.Hom.hom
        ((stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x).inv ≫
          stalkModuleMapToRestrict p
              ((PresheafOfModules.pullbackPushforwardAdjunction
                      (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                          (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                        Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
                ℱ)
              x ≫
            (ModuleCat.restrictScalars (CommRingCat.Hom.hom ((stalkFunctor CommRingCat x).map p))).map
              (stalkActualPullbackTargetIso p ℱ x).hom))
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪 x)
        (hcM := CategoryTheory.Limits.colimit.isColimit
          (stalkNeighborhoodModule 𝒪 ℱ x).presheaf)
        m) =
    PresheafOfModules.ModuleColimit.ιM
      (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪' x)
      (hcM := CategoryTheory.Limits.colimit.isColimit
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
          (stalkNeighborhoodModule 𝒪 ℱ x)).presheaf)
      ((ModuleCat.Hom.hom ((inv ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).app U))
        ((ModuleCat.Hom.hom
            (((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
                    ((PresheafOfModules.pullbackPushforwardAdjunction
                            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
                      ℱ)).app
                U ≫
              ((stalkNeighborhoodPushforwardIso p x).hom.app
                    ((PresheafOfModules.pullback
                        (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                            (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                          Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj
                      ℱ)).app
                U))
          m)) := by
  cases U with
  | op U =>
  let φ :=
    ((PresheafOfModules.pullbackPushforwardAdjunction
            (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ)
  have hstalk :
      ModuleCat.Hom.hom (stalkModuleMapToRestrict p φ x)
          (PresheafOfModules.ModuleColimit.ιM
            (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪 x)
            (hcM := CategoryTheory.Limits.colimit.isColimit
              (stalkNeighborhoodModule 𝒪 ℱ x).presheaf)
            m) =
        TopCat.Presheaf.germ (stalkBaseChangePulledBackModule p ℱ).presheaf
          U.1 x U.2 (ModuleCat.Hom.hom (φ.app (op U.1)) m) := by
    simpa [φ, stalkNeighborhoodModule_colimit_ι_eq_germ] using
      (stalkModuleMapToRestrict_germ_apply (𝒪 := 𝒪) (𝒪' := 𝒪') p
        (φ := φ) x U.1 U.2 m)
  rw [moduleCat_hom_comp_apply, moduleCat_hom_comp_apply]
  rw [stalkNeighborhoodActualStalkModuleIso_inv_apply]
  change ModuleCat.Hom.hom
      ((ModuleCat.restrictScalars
          (CommRingCat.Hom.hom ((stalkFunctor CommRingCat x).map p))).map
        (stalkActualPullbackTargetIso p ℱ x).hom)
      (ModuleCat.Hom.hom
        (stalkModuleMapToRestrict p
          ((PresheafOfModules.pullbackPushforwardAdjunction
                  (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                      (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                    Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
            ℱ)
          x)
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪 x)
          (hcM := CategoryTheory.Limits.colimit.isColimit
            (stalkNeighborhoodModule 𝒪 ℱ x).presheaf)
          m)) =
    PresheafOfModules.ModuleColimit.ιM
      (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪' x)
      (hcM := CategoryTheory.Limits.colimit.isColimit
        ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
          (stalkNeighborhoodModule 𝒪 ℱ x)).presheaf)
      (ModuleCat.Hom.hom ((inv ((stalkNeighborhoodModule_pullbackMate p x).app ℱ)).app (op U))
        (ModuleCat.Hom.hom
          (((PresheafOfModules.pushforward₀OfCommRingCat (OpenNhds.inclusion x) 𝒪).map
                ((PresheafOfModules.pullbackPushforwardAdjunction
                    (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                        (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                      Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ)).app
              (op U) ≫
            ((stalkNeighborhoodPushforwardIso p x).hom.app
              ((PresheafOfModules.pullback
                (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ)).app (op U))
          m))
  rw [show
      ModuleCat.Hom.hom
        (stalkModuleMapToRestrict p
          ((PresheafOfModules.pullbackPushforwardAdjunction
                  (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                      (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                    Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
            ℱ)
          x)
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪 x)
          (hcM := CategoryTheory.Limits.colimit.isColimit
            (stalkNeighborhoodModule 𝒪 ℱ x).presheaf)
          m) =
      TopCat.Presheaf.germ (stalkBaseChangePulledBackModule p ℱ).presheaf
        U.1 x U.2
          (ModuleCat.Hom.hom
            (((PresheafOfModules.pullbackPushforwardAdjunction
                    (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                        (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                      Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app
              ℱ).app (op U.1))
            m) by
      simpa [φ] using hstalk]
  simpa [φ, stalkNeighborhoodPushforwardIso] using
    (stalkActualPullbackTargetIso_restrictScalars_hom_germ_apply p ℱ x U
      (ModuleCat.Hom.hom
        (((PresheafOfModules.pullbackPushforwardAdjunction
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).unit.app ℱ).app
          (op U.1))
        m))

/-- Helper for Lemma 6.14.2: after expanding the transported actual-stalk comparison on a fixed
neighborhood generator, the remaining source and target transports should rewrite to the same
pointwise identity as the neighborhood mate-unit formula. -/
private theorem stalkActualTransportedComparison_pointwise_eq_hpoint
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X)
    (U : (OpenNhds x)ᵒᵖ) (m : ↑((stalkNeighborhoodModule 𝒪 ℱ x).obj U)) :
    (ModuleCat.Hom.hom
          (((PresheafOfModules.colimitAdjunction (stalkNeighborhoodActualStalkIsColimit 𝒪 x)).unit.app
                  (stalkNeighborhoodModule 𝒪 ℱ x) ≫
                (PresheafOfModules.constFunctor (stalkNeighborhoodActualStalkCocone 𝒪 x)).map
                  (((ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom)).homEquiv
                      ((PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪 x)).obj
                        (stalkNeighborhoodModule 𝒪 ℱ x))
                      ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
                            PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
                        (stalkNeighborhoodModule 𝒪 ℱ x)))
                    (((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
                          (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x)).inv ≫
                      stalkBaseChangeComparison p ℱ x ≫
                        (stalkActualPullbackTargetIso p ℱ x).hom))).app
            U))
        m =
      (ModuleCat.Hom.hom
          (((stalkActualPullbackAdjunctionRaw p x).unit.app (stalkNeighborhoodModule 𝒪 ℱ x) ≫
                (stalkActualRestrictScalarsConstIso p x).symm.hom.app
                  ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x) ⋙
                        PresheafOfModules.colimitFunctor (stalkNeighborhoodActualStalkIsColimit 𝒪' x)).obj
                    (stalkNeighborhoodModule 𝒪 ℱ x))).app
            U))
        m := by
  simp only [stalkActualPullbackAdjunctionRaw, Adjunction.comp_unit_app]
  rw [colimitAdjunction_unit_map_app_apply]
  have hpoint :=
    congrArg
      (fun y ↦
        PresheafOfModules.ModuleColimit.ιM
          (hcR := stalkNeighborhoodActualStalkIsColimit 𝒪' x)
          (hcM := CategoryTheory.Limits.colimit.isColimit
            ((PresheafOfModules.pullback (stalkNeighborhoodRingHomOverId p x)).obj
              (stalkNeighborhoodModule 𝒪 ℱ x)).presheaf)
          y)
      (stalkNeighborhoodModule_inverse_mate_after_hpoint p ℱ x U m)
  rw [stalkBaseChangeComparisonTransported_extendTranspose_eq]
  convert hpoint using 1
  · exact stalkActualTransportedComparison_source_generator p ℱ x U m

/-- Helper for Lemma 6.14.2: after transporting the ordinary stalk comparison to the actual-stalk
adjunctions, its image under the adjunction hom-equivalence is the unit of
`stalkActualPullbackAdjunction`. -/
private theorem stalkBaseChangeComparison_transport_homEquiv_eq_unit
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    (stalkActualBaseChangeAdjunction p x).homEquiv _ _
      (stalkBaseChangeComparisonTransported p ℱ x) =
        (stalkActualPullbackAdjunction p x).unit.app (stalkNeighborhoodModule 𝒪 ℱ x) := by
  -- Expand the transported adjunction formulas once so the remaining goal is the explicit
  -- comparison between the ordinary stalk unit and the neighborhood mate unit.
  rw [stalkActualBaseChangeAdjunction_homEquiv_apply, stalkBaseChangeComparisonTransported_eq,
    stalkActualPullbackAdjunction_unit_app]
  rw [Adjunction.homEquiv_unit]
  -- Evaluate the constant-presheaf comparison at a neighborhood generator so only the normalized
  -- mate-unit identity remains.
  ext U m
  -- The remaining blocker is the explicit transport from the actual-stalk comparison formulas
  -- down to the pointwise neighborhood mate-unit identity proved just above.
  have hpoint :=
    stalkNeighborhoodModule_pullbackMate_unit_app_on_sections
      (𝒪 := 𝒪) (𝒪' := 𝒪') p ℱ x U m
  -- The remaining blocker is only to package the already-proved pointwise identity lemmas for the
  -- source and target transports so that the goal rewrites to `hpoint`.
  have _ := stalkNeighborhoodActualStalkModuleIso_hom_apply 𝒪 ℱ x
  have _ := stalkNeighborhoodActualStalkModuleIso_inv_apply 𝒪 ℱ x
  have _ := stalkActualRestrictScalarsConstIsoApp_hom_apply p x
  have _ := stalkActualRestrictScalarsConstIsoApp_inv_apply p x
  -- Reduce the transported pointwise comparison to the isolated actual-stalk transport lemma.
  exact stalkActualTransportedComparison_pointwise_eq_hpoint p ℱ x U m

/-- Helper for Lemma 6.14.2: after transporting both source and target to the actual-stalk
adjunctions, the stalk base-change map is the `leftAdjointUniq` component. -/
private theorem stalkBaseChangeComparison_eq_actual_leftAdjointUniq_app
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    stalkBaseChangeComparison p ℱ x =
      ((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
          (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x)).hom ≫
        ((Adjunction.leftAdjointUniq
            (stalkActualBaseChangeAdjunction p x)
            (stalkActualPullbackAdjunction p x)).hom.app
          (stalkNeighborhoodModule 𝒪 ℱ x)) ≫
        (stalkActualPullbackTargetIso p ℱ x).inv := by
  -- First identify the transported comparison with the `leftAdjointUniq` component via the
  -- previously isolated hom-equivalence computation.
  have htransport :
      stalkBaseChangeComparisonTransported p ℱ x =
        ((Adjunction.leftAdjointUniq
            (stalkActualBaseChangeAdjunction p x)
            (stalkActualPullbackAdjunction p x)).hom.app
          (stalkNeighborhoodModule 𝒪 ℱ x)) :=
    eq_leftAdjointUniq_app_of_homEquiv_eq_unit p x
      (stalkNeighborhoodModule 𝒪 ℱ x)
      (stalkBaseChangeComparisonTransported p ℱ x)
      (stalkBaseChangeComparison_transport_homEquiv_eq_unit p ℱ x)
  -- Then conjugate back by the source and target transport isomorphisms.
  let sourceIso :=
    ((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
      (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x))
  let targetIso := stalkActualPullbackTargetIso p ℱ x
  rw [stalkBaseChangeComparisonTransported_eq] at htransport
  -- Conjugate the transported equality by the source and target transport isomorphisms.
  have hcancel :
      sourceIso.hom ≫ (sourceIso.inv ≫ stalkBaseChangeComparison p ℱ x ≫ targetIso.hom) ≫
          targetIso.inv =
        stalkBaseChangeComparison p ℱ x := by
    calc
      sourceIso.hom ≫ (sourceIso.inv ≫ stalkBaseChangeComparison p ℱ x ≫ targetIso.hom) ≫
          targetIso.inv =
        stalkBaseChangeComparison p ℱ x ≫ targetIso.hom ≫ targetIso.inv := by
            apply
              (Iso.cancel_iso_inv_right_assoc sourceIso.hom
                (sourceIso.inv ≫ stalkBaseChangeComparison p ℱ x ≫ targetIso.hom)
                (stalkBaseChangeComparison p ℱ x) targetIso.hom targetIso).2
            simp
      _ = stalkBaseChangeComparison p ℱ x := by
            have htarget :
                stalkBaseChangeComparison p ℱ x ≫ (targetIso.hom ≫ targetIso.inv) =
                  stalkBaseChangeComparison p ℱ x ≫ 𝟙 _ :=
              congrArg (fun k ↦ stalkBaseChangeComparison p ℱ x ≫ k) targetIso.hom_inv_id
            simpa [Category.assoc] using htarget
  have hconj :=
    congrArg (fun k ↦ sourceIso.hom ≫ k ≫ targetIso.inv) htransport
  have hconj' :
      sourceIso.hom ≫ (sourceIso.inv ≫ stalkBaseChangeComparison p ℱ x ≫ targetIso.hom) ≫
          targetIso.inv =
        sourceIso.hom ≫
          ((Adjunction.leftAdjointUniq
              (stalkActualBaseChangeAdjunction p x)
              (stalkActualPullbackAdjunction p x)).hom.app
            (stalkNeighborhoodModule 𝒪 ℱ x)) ≫
          targetIso.inv := by
    simpa [sourceIso, targetIso, Category.assoc] using hconj
  exact hcancel.symm.trans hconj'

/-- Lemma 6.14.2 (Tag 007K): for a morphism `p : 𝒪 ⟶ 𝒪'` of presheaves of commutative rings on
`X`, an `𝒪`-module presheaf `ℱ`, and `x : X`, the canonical comparison
`ℱ_x ⊗[𝒪_x] 𝒪'_x ⟶ (ℱ ⊗_{p, 𝒪} 𝒪')_x` is an isomorphism. -/
instance stalkBaseChangeComparison_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    IsIso (stalkBaseChangeComparison p ℱ x) :=
by
  -- Route correction: the remaining work is now isolated in two target-faithful helpers. First,
  -- `stalkActualPullbackTargetIso` compares the ordinary pulled-back stalk with the actual
  -- neighborhood pullback colimit object. Then the next helper identifies the transported
  -- comparison map with the `leftAdjointUniq` component.
  let actualIso :
      (ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
          (ModuleCat.of (𝒪.stalk x) ↑(stalk ℱ.presheaf x)) ≅
        ModuleCat.of (𝒪'.stalk x)
          ↑(stalk
            ((PresheafOfModules.pullback
              (show (𝒪 ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p (forget₂ CommRingCat RingCat))).obj ℱ).presheaf x) :=
    ((ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).mapIso
      (stalkNeighborhoodActualStalkModuleIso 𝒪 ℱ x)) ≪≫
      ((Adjunction.leftAdjointUniq
        (stalkActualBaseChangeAdjunction p x)
        (stalkActualPullbackAdjunction p x)).app
          (stalkNeighborhoodModule 𝒪 ℱ x)) ≪≫
      (stalkActualPullbackTargetIso p ℱ x).symm
  rw [stalkBaseChangeComparison_eq_actual_leftAdjointUniq_app p ℱ x]
  change IsIso actualIso.hom
  infer_instance

end TopCat.Presheaf
