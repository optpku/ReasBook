module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import stacks_project.Chap06.Lemma_6_14_2

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopCat.Presheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}} {𝒪 𝒪' : X.Sheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
variable
  (ℱ : SheafOfModules
    ((CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
      (CategoryTheory.forget₂ CommRingCat RingCat)).obj 𝒪))
variable (x : X)

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.20.3:
- primary domain: stalkwise base change for pullback of sheaves of modules over sheaves of
  commutative rings on a topological space;
- sampled owner API:
  `TopCat.Presheaf.stalkBaseChangeComparison`,
  `TopCat.Presheaf.stalkBaseChangeComparison_isIso`,
  `SheafOfModules.pullbackIso`,
  `PresheafOfModules.sheafificationAdjunction`,
  `TopCat.Sheaf.stalkPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the textbook stalkwise base-change isomorphism for sheaf pullback;
  `core/canonical`: the presheaf-level base-change owner
    `TopCat.Presheaf.stalkBaseChangeComparison`;
  `bridge/view`: the comparison from the sheaf pullback to the sheafification of the presheaf
    pullback, plus the resulting stalk comparison.

Primitive data are the morphism of sheaves of commutative rings `p : 𝒪 ⟶ 𝒪'` and the
`𝒪`-module sheaf `ℱ`. The presheaf-level stalk base-change map is already owned upstream, so this
file should reuse that owner directly and keep only the sheafification/pullback bridge local.
-/

/-- The underlying sheaf of rings obtained by forgetting commutativity. -/
abbrev ringSheafOfComm (𝒪 : X.Sheaf CommRingCat.{u}) : X.Sheaf RingCat.{u} :=
  CategoryTheory.sheafCompose J (CategoryTheory.forget₂ CommRingCat RingCat) |>.obj 𝒪

/-- The forgotten ring-sheaf morphism induced by `p`, in the identity-on-opens shape consumed by
`SheafOfModules.pullback`. -/
noncomputable abbrev ringSheafHomOverId :
    ringSheafOfComm 𝒪 ⟶
      (Functor.sheafPushforwardContinuous (𝟭 (Opens X)) RingCat J J).obj
        (ringSheafOfComm 𝒪') :=
  (CategoryTheory.sheafCompose J (CategoryTheory.forget₂ CommRingCat RingCat)).map p ≫
    (Functor.sheafPushforwardContinuousId RingCat J).inv.app (ringSheafOfComm 𝒪')

/-- The forgotten ring-presheaf morphism induced by `p`, in the shape consumed by
`PresheafOfModules.pullback`. -/
public abbrev ringPresheafHomOverId :
    (ringSheafOfComm 𝒪).obj ⟶ (𝟭 (Opens X)).op ⋙ (ringSheafOfComm 𝒪').obj :=
  show (ringSheafOfComm 𝒪).obj ⟶ (𝟭 (Opens X)).op ⋙ (ringSheafOfComm 𝒪').obj from
    Functor.whiskerRight p.hom (CategoryTheory.forget₂ CommRingCat RingCat)

local notation "sheafModulePullback" =>
  SheafOfModules.pullback (ringSheafHomOverId p)
local notation "presheafModulePullback" =>
  PresheafOfModules.pullback (ringPresheafHomOverId p)

public noncomputable abbrev presheafPullbackObj :=
  (presheafModulePullback).obj ℱ.val

public noncomputable abbrev commRingStalkToRingStalkIso (x : X) (𝒪 : X.Sheaf CommRingCat.{u}) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk 𝒪.obj x) ≅
      (ringSheafOfComm 𝒪).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ 𝒪.obj)

public noncomputable instance :
    Module ↑(TopCat.Presheaf.stalk 𝒪.obj x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ℱ.val x

public noncomputable instance
    : Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) := by
  let restricted : ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x) :=
    (ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom).obj
      (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x))
  change Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x) ↑restricted
  infer_instance

noncomputable instance sheafOfModules_pullbackStalkModule
    : Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  let restricted : ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x) :=
    (ModuleCat.restrictScalars (commRingStalkToRingStalkIso x 𝒪').hom.hom).obj
      (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x))
  change Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x) ↑restricted
  infer_instance

/-- The stalk map induced by a morphism of module presheaves over a fixed ring sheaf. -/
public noncomputable abbrev stalkUnderlyingMap
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    TopCat.Presheaf.stalk ℱ.presheaf x ⟶ TopCat.Presheaf.stalk 𝒢.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf R.obj).map φ)

/-- The stalk map induced by a morphism of module presheaves is linear over the stalk ring. -/
public theorem stalkUnderlyingMap_smul
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    ∀ (r : R.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)),
      stalkUnderlyingMap x φ (r • m) = r • stalkUnderlyingMap x φ m := by
  -- Compare both stalk elements on a common neighborhood representative and use sectionwise
  -- linearity of `φ`.
  intro r m
  obtain ⟨U, hxU, rU, hr⟩ := TopCat.Presheaf.germ_exist R.presheaf x r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist ℱ.presheaf x m
  let W : Opens X := U ⊓ V
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : R.presheaf.obj (Opposite.op W) := R.presheaf.map iWU.op rU
  let mW : ℱ.presheaf.obj (Opposite.op W) := ℱ.presheaf.map iWV.op mV
  have hrW : R.presheaf.germ W x hxW rW = r := by
    simpa [W, iWU, hxW, rW] using (R.presheaf.germ_res_apply iWU x hxW rU).trans hr
  have hmW : TopCat.Presheaf.germ ℱ.presheaf W x hxW mW = m := by
    simpa [W, iWV, hxW, mW] using
      (TopCat.Presheaf.germ_res_apply ℱ.presheaf iWV x hxW mV).trans hm
  have hsmulW :
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) = r • m := by
    calc
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) =
          R.presheaf.germ W x hxW rW • TopCat.Presheaf.germ ℱ.presheaf W x hxW mW := by
            simpa using
              (PresheafOfModules.germ_ringCat_smul (R := R.obj) (M := ℱ) x W hxW rW mW)
      _ = r • m := by rw [hrW, hmW]
  have hmφW :
      (show ↑(TopCat.Presheaf.stalk 𝒢.presheaf x) from
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf R.obj).map φ)) m) =
        TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) mW) := by
    rw [← hmW]
    simpa [W, hxW, mW] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        ((PresheafOfModules.toPresheaf R.obj).map φ) mW)
  calc
    stalkUnderlyingMap x φ (r • m) =
        TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) (rW • mW)) := by
          rw [← hsmulW]
          simpa [W, hxW, rW, mW] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
              ((PresheafOfModules.toPresheaf R.obj).map φ) (rW • mW))
    _ = TopCat.Presheaf.germ 𝒢.presheaf W x hxW (rW • φ.app (Opposite.op W) mW) := by
          congr 1
          exact (φ.app (Opposite.op W)).hom.map_smul rW mW
    _ = R.presheaf.germ W x hxW rW •
          TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) mW) := by
          simpa using
            (PresheafOfModules.germ_ringCat_smul (R := R.obj) (M := 𝒢) x W hxW rW
              (φ.app (Opposite.op W) mW))
    _ = r • stalkUnderlyingMap x φ m := by
          rw [hrW]
          simpa [stalkUnderlyingMap] using (congrArg (fun z ↦ r • z) hmφW).symm

/-- The stalk map induced by a morphism of module presheaves, packaged as a module homomorphism. -/
public noncomputable def stalkModuleMap
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢) :
    ModuleCat.of (R.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.presheaf x) ⟶
      ModuleCat.of (R.presheaf.stalk x) ↑(TopCat.Presheaf.stalk 𝒢.presheaf x) :=
  ModuleCat.ofHom
    { toFun := stalkUnderlyingMap x φ
      map_add' := by
        intro m n
        exact (stalkUnderlyingMap x φ).hom.map_add m n
      map_smul' := stalkUnderlyingMap_smul x φ }

/-- If the underlying additive stalk map is an isomorphism, then the corresponding packaged
module-valued stalk map is also an isomorphism. -/
public theorem stalkModuleMap_isIso
    {R : X.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj} (x : X) (φ : ℱ ⟶ 𝒢)
    [IsIso (stalkUnderlyingMap x φ)] :
    IsIso (stalkModuleMap x φ) := by
  let F := forget₂ (ModuleCat (R.presheaf.stalk x)) AddCommGrpCat
  haveI : IsIso (F.map (stalkModuleMap x φ)) := by
    change IsIso (stalkUnderlyingMap x φ)
    infer_instance
  exact isIso_of_reflects_iso (stalkModuleMap x φ) F

/-- The stalk map on the unit of module sheafification for the presheaf pullback. -/
public noncomputable def presheafPullbackSheafificationUnitStalkHom :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) ⟶
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
            (presheafPullbackObj p ℱ)).val.presheaf) x) := by
  simpa using
    stalkModuleMap x
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
        (presheafPullbackObj p ℱ))

public instance presheafPullbackSheafificationUnitStalkHom_isIso :
    IsIso (presheafPullbackSheafificationUnitStalkHom p ℱ x) := by
  let φ :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafOfComm 𝒪').obj)).unit.app
      (presheafPullbackObj p ℱ))
  haveI : IsIso (stalkUnderlyingMap x φ) := by
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (CategoryTheory.toSheafify J (presheafPullbackObj p ℱ).presheaf))
    simpa [φ, stalkUnderlyingMap] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (presheafPullbackObj p ℱ).presheaf)
  simpa [presheafPullbackSheafificationUnitStalkHom, φ] using stalkModuleMap_isIso x φ

/-- The stalk map on the canonical identification between sheaf pullback and sheafified presheaf
pullback. -/
public noncomputable def sheafPullbackIsoStalkHom :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) ⟶
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (ringSheafOfComm 𝒪').obj)).obj
            (presheafPullbackObj p ℱ)).val.presheaf) x) := by
  simpa using
    stalkModuleMap x (((SheafOfModules.pullbackIso
      (ringSheafHomOverId p)).app ℱ).hom.val)

public instance sheafPullbackIsoStalkHom_isIso :
    IsIso (sheafPullbackIsoStalkHom p ℱ x) := by
  -- First transport the owner isomorphism `SheafOfModules.pullbackIso` through the forgetful
  -- functors down to the stalk additive map, then repackage it as a module isomorphism.
  let e := ((SheafOfModules.pullbackIso (ringSheafHomOverId p)).app ℱ)
  let φ := e.hom.val
  haveI : IsIso e.hom := by
    infer_instance
  haveI : IsIso φ := by
    simpa [φ] using (Functor.map_isIso (SheafOfModules.forget _) e.hom)
  have hφ : IsIso (stalkUnderlyingMap x φ) := by
    simpa [stalkUnderlyingMap, φ] using
      (Functor.map_isIso
        (SheafOfModules.forget _ ⋙
          PresheafOfModules.toPresheaf (ringSheafOfComm 𝒪').obj ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
        e.hom)
  simpa [sheafPullbackIsoStalkHom, φ] using (stalkModuleMap_isIso x φ)

/-- The stalk isomorphism identifying the stalk of the underlying presheaf pullback with the stalk
of the sheaf pullback. This is the private comparison used in the sheaf-level base-change
statement. -/
public noncomputable abbrev sheafOfModules_pullbackPresheafStalkIso :
    ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (presheafPullbackObj p ℱ).presheaf x) ≅
      ModuleCat.of ((ringSheafOfComm 𝒪').presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) :=
  asIso (presheafPullbackSheafificationUnitStalkHom p ℱ x) ≪≫
    (asIso (sheafPullbackIsoStalkHom p ℱ x)).symm

/-- Helper for Lemma 6.20.3: the preserved-colimit comparison from the forgotten commutative
stalk to the ring-valued stalk sends a commutative-ring germ to the same ring-valued germ. -/
public theorem commRingStalkToRingStalkIso_hom_germ_apply
    (U : Opens X) (hxU : x ∈ U) (r : 𝒪'.obj.obj (Opposite.op U)) :
    ((commRingStalkToRingStalkIso x 𝒪').hom.hom)
        (TopCat.Presheaf.germ 𝒪'.obj U x hxU r) =
      TopCat.Presheaf.germ (ringSheafOfComm 𝒪').presheaf U x hxU r := by
  -- This is exactly the `hom` computation rule for the preserved-colimit comparison.
  let j : (OpenNhds x)ᵒᵖ := Opposite.op ⟨U, hxU⟩
  have h :=
    CategoryTheory.ι_preservesColimitIso_hom
      (G := forget₂ CommRingCat RingCat)
      (F := (OpenNhds.inclusion x).op ⋙ 𝒪'.obj) j
  exact congrArg (fun f ↦ f.hom r) h

/-- Helper for Lemma 6.20.3: the identity map between the two pullback-stalk carriers preserves
addition. -/
public theorem presheafPullbackStalkRestrictedHom_map_add
    (m n :
      ↑(TopCat.Presheaf.stalk
        ((PresheafOfModules.pullback
          (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
          ℱ.val).presheaf x)) :
    (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from
        m + n) =
      (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from m) +
        (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from n) := by
  -- The additive structures are inherited from the same underlying additive stalk.
  rfl

/-- Helper for Lemma 6.20.3: the identity map from the commutative-ring pullback stalk to the
restricted ring-valued pullback stalk is linear. -/
public theorem presheafPullbackStalkRestrictedHom_map_smul
    (r : ↑(TopCat.Presheaf.stalk 𝒪'.obj x))
    (m :
      ↑(TopCat.Presheaf.stalk
        ((PresheafOfModules.pullback
          (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
          ℱ.val).presheaf x)) :
    (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from
        r • m) =
      (show ↑((ringSheafOfComm 𝒪').presheaf.stalk x) from
          ((commRingStalkToRingStalkIso x 𝒪').hom.hom) r) •
        (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from m) := by
  -- Choose common representatives for the scalar and the module section, as in the presheaf-level
  -- stalk-base-change proof, so the two scalar actions can be compared sectionwise.
  let M₀ :=
    ((PresheafOfModules.pullback
      (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
          (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
        Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
      ℱ.val)
  obtain ⟨U, hxU, rU, hr⟩ := TopCat.Presheaf.germ_exist 𝒪'.obj x r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist M₀.presheaf x m
  let W : Opens X := U ⊓ V
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : 𝒪'.obj.obj (Opposite.op W) := 𝒪'.obj.map iWU.op rU
  let mW : M₀.obj (Opposite.op W) := M₀.map iWV.op mV
  have hrW : TopCat.Presheaf.germ 𝒪'.obj W x hxW rW = r := by
    simpa [W, iWU, hxW, rW] using
      (TopCat.Presheaf.germ_res_apply 𝒪'.obj iWU x hxW rU).trans hr
  have hmW : TopCat.Presheaf.germ M₀.presheaf W x hxW mW = m := by
    simpa [W, iWV, hxW, mW] using
      (TopCat.Presheaf.germ_res_apply M₀.presheaf iWV x hxW mV).trans hm
  have hcomm :
      TopCat.Presheaf.germ M₀.presheaf W x hxW (rW • mW) = r • m := by
    calc
      TopCat.Presheaf.germ M₀.presheaf W x hxW (rW • mW) =
          TopCat.Presheaf.germ 𝒪'.obj W x hxW rW •
            TopCat.Presheaf.germ M₀.presheaf W x hxW mW := by
            simpa [M₀] using
              (PresheafOfModules.germ_smul (M := M₀) x W hxW rW mW)
      _ = r • m := by
            rw [hrW, hmW]
  have hring_scalar :
      ((commRingStalkToRingStalkIso x 𝒪').hom.hom) r =
        TopCat.Presheaf.germ (ringSheafOfComm 𝒪').presheaf W x hxW rW := by
    rw [← hrW]
    exact commRingStalkToRingStalkIso_hom_germ_apply (𝒪' := 𝒪') (x := x) W hxW rW
  have hring :
      TopCat.Presheaf.germ ((presheafPullbackObj p ℱ).presheaf) W x hxW
          (show (presheafPullbackObj p ℱ).obj (Opposite.op W) from rW • mW) =
        (TopCat.Presheaf.germ (ringSheafOfComm 𝒪').presheaf W x hxW rW) •
          TopCat.Presheaf.germ ((presheafPullbackObj p ℱ).presheaf) W x hxW
            (show (presheafPullbackObj p ℱ).obj (Opposite.op W) from mW) := by
    -- The target scalar action is the ring-valued stalk action from `germ_ringCat_smul`.
    exact
      (PresheafOfModules.germ_ringCat_smul (R := (ringSheafOfComm 𝒪').obj)
        (M := presheafPullbackObj p ℱ) x W hxW rW
        (show (presheafPullbackObj p ℱ).obj (Opposite.op W) from mW))
  have hmW₁ :
      TopCat.Presheaf.germ ((presheafPullbackObj p ℱ).presheaf) W x hxW
          (show (presheafPullbackObj p ℱ).obj (Opposite.op W) from mW) =
        (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from m) := by
    simpa [M₀, presheafPullbackObj, ringPresheafHomOverId, ringSheafOfComm] using hmW
  calc
    (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from r • m)
        = TopCat.Presheaf.germ ((presheafPullbackObj p ℱ).presheaf) W x hxW
            (show (presheafPullbackObj p ℱ).obj (Opposite.op W) from rW • mW) := by
          simpa [M₀, presheafPullbackObj, ringPresheafHomOverId, ringSheafOfComm] using
            hcomm.symm
    _ = (show ↑((ringSheafOfComm 𝒪').presheaf.stalk x) from
          ((commRingStalkToRingStalkIso x 𝒪').hom.hom) r) •
        (show ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x) from m) := by
          rw [hring, hring_scalar, hmW₁]

public noncomputable def presheafPullbackStalkRestrictedHom :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ⟶
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x)) :=
  ModuleCat.ofHom
    { toFun := fun m ↦ m
      map_add' := presheafPullbackStalkRestrictedHom_map_add p ℱ x
      map_smul' := presheafPullbackStalkRestrictedHom_map_smul p ℱ x }

public instance presheafPullbackStalkRestrictedHom_isIso :
    IsIso (presheafPullbackStalkRestrictedHom p ℱ x) := by
  -- The underlying additive map is the identity, so the forgetful functor reflects its isomorphism.
  let F := forget₂ (ModuleCat ↑(TopCat.Presheaf.stalk 𝒪'.obj x)) AddCommGrpCat
  haveI : IsIso (F.map (presheafPullbackStalkRestrictedHom p ℱ x)) := by
    change IsIso (𝟙 (AddCommGrpCat.of
      ↑(TopCat.Presheaf.stalk
        ((PresheafOfModules.pullback
          (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
              (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
            Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
          ℱ.val).presheaf x)))
    infer_instance
  exact isIso_of_reflects_iso (presheafPullbackStalkRestrictedHom p ℱ x) F

public noncomputable abbrev presheafPullbackStalkRestrictedIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ≅
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((presheafPullbackObj p ℱ).presheaf) x)) :=
  asIso (presheafPullbackStalkRestrictedHom p ℱ x)

public noncomputable abbrev sheafPullbackStalkRestrictedIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) ≅
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
        (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x)) := by
  exact Iso.refl _

/-- The stalk of the presheaf pullback identifies canonically with the stalk of the sheaf pullback.
-/
public noncomputable abbrev pullbackStalkComparisonIso :
    ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) ≅
      ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
        ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  letI :
      Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
        ↑(TopCat.Presheaf.stalk
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val).presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((PresheafOfModules.pullback
        (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
            (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
          Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
        ℱ.val) x
  have hsource :
      ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
          ↑(TopCat.Presheaf.stalk
            ((PresheafOfModules.pullback
              (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                  (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
                Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
              ℱ.val).presheaf x) ≅
        (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).obj
          (ModuleCat.of ↑((ringSheafOfComm 𝒪').presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (((presheafModulePullback).obj ℱ.val).presheaf) x)) := by
    simpa [ringPresheafHomOverId, ringSheafOfComm] using
      presheafPullbackStalkRestrictedIso p ℱ x
  exact
    hsource ≪≫
      (ModuleCat.restrictScalars ((commRingStalkToRingStalkIso x 𝒪').hom.hom)).mapIso
        (sheafOfModules_pullbackPresheafStalkIso p ℱ x) ≪≫
      (sheafPullbackStalkRestrictedIso p ℱ x).symm

/-- Lemma 6.20.3 (Tag 008B): for a morphism `p : 𝒪 ⟶ 𝒪'` of sheaves of commutative rings on `X`,
an `𝒪`-module sheaf `ℱ`, and `x : X`, the canonical base-change map on stalks
`ℱ_x ⊗[𝒪_x] 𝒪'_x ≅ (ℱ ⊗_𝒪 𝒪')_x` is an isomorphism. -/
noncomputable abbrev sheafOfModules_pullback_stalkIso :
      (ModuleCat.extendScalars (((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom)).obj
      (ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪.obj) x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) ≅
        ModuleCat.of ↑(TopCat.Presheaf.stalk (𝒪'.obj) x)
          ↑(TopCat.Presheaf.stalk ((sheafModulePullback).obj ℱ).val.presheaf x) := by
  exact
    (by
      letI :
          Module ↑(TopCat.Presheaf.stalk 𝒪'.obj x)
            ↑(TopCat.Presheaf.stalk
              ((PresheafOfModules.pullback
                (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                    (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
                  Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
                ℱ.val).presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          ((PresheafOfModules.pullback
            (show (𝒪.obj ⋙ forget₂ CommRingCat RingCat) ⟶
                (𝟭 (Opens X)).op ⋙ (𝒪'.obj ⋙ forget₂ CommRingCat RingCat) from
              Functor.whiskerRight p.hom (forget₂ CommRingCat RingCat))).obj
            ℱ.val) x
      simpa [ringPresheafHomOverId, ringSheafOfComm] using
        asIso (TopCat.Presheaf.stalkBaseChangeComparison p.hom ℱ.val x)) ≪≫
      pullbackStalkComparisonIso p ℱ x

end
