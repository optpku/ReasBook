module

import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_26_1
public import stacks_project.Chap06.Lemma_6_20_3
public import stacks_project.Chap06.Lemma_6_22_1
@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

/-- Helper for Lemma 6.26.4: a natural transformation between two functors which both preserve a
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
      (Limits.IsColimit.coconePointsIsoOfNatIso hP hQ (asIso (Functor.whiskerLeft D τ))).hom := by
    apply hP.hom_ext
    intro j
    have hr := Limits.IsColimit.comp_coconePointsIsoOfNatIso_hom hP hQ
      (asIso (Functor.whiskerLeft D τ)) j
    refine Eq.trans ?_ hr.symm
    simp only [Functor.mapCocone_ι_app, asIso_hom, Functor.whiskerLeft_app]
    exact τ.naturality (c.ι.app j)
  rw [heq]
  exact (Limits.IsColimit.coconePointsIsoOfNatIso hP hQ (asIso (Functor.whiskerLeft D τ))).isIso_hom


universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 6.26.4:
- primary domain: stalkwise base change for pullback of sheaves of modules along a morphism of
  ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `sheafOfModules_pullback_stalkIso`,
  `TopCat.Sheaf.stalkPullbackIso`;
- best owner abstraction: no single upstream declaration already packages the ringed-space
  specialization, so the public owner here should be the morphism-attached stalk comparison for
  `f^*`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y`, an `\mathcal O_Y`-module sheaf `𝒢`,
  and a point `x : X`;
- derived API: the canonical stalk isomorphism expressing `((f^*).obj 𝒢)_x` as extension of
  scalars of `𝒢_{f(x)}` along the induced stalk map `f.hom.stalkMap x`.

Source/core/bridge triage:
- `source-facing`: the textbook stalk formula for `f^*`;
- `core/canonical`: `RingedSpace.Hom.pullback`, `sheafOfModules_pullback_stalkIso`, and
  `f.hom.stalkMap x`;
- `bridge/view`: `TopCat.Sheaf.stalkPullbackIso`, used only to identify the stalk of the inverse
  image sheaf with the stalk at the image point.

This file therefore must not stop at the two ingredient owners. It exposes the composed
ringed-space statement itself and keeps the ingredients only as proof-route data.
-/

/- Core owner ingredients used in the proof route. -/
recall sheafOfModules_pullback_stalkIso
recall TopCat.Sheaf.stalkPullbackIso

namespace RingedSpace.Hom

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

public abbrev inverseImageCommRingSheaf (f : X ⟶ Y) : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf

public abbrev inverseImageRingSheaf (f : X ⟶ Y) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj
    (inverseImageCommRingSheaf f)

public noncomputable abbrev inverseImageRingUnit (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (inverseImageRingSheaf f) := by
  simpa [RingedSpace.ringCatSheaf, inverseImageCommRingSheaf, inverseImageRingSheaf] using
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app Y.sheaf)

private abbrev topCommRingPresheaf (f : X ⟶ Y) :
    X.carrier.Presheaf CommRingCat.{u} :=
  (TopCat.Presheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf.obj

private abbrev topRingPresheafFromComm (f : X ⟶ Y) :
    X.carrier.Presheaf RingCat.{u} :=
  topCommRingPresheaf f ⋙ forget₂ CommRingCat RingCat

private noncomputable abbrev topUnitFromComm (f : X ⟶ Y) :
    Y.ringCatSheaf.obj ⟶
      (TopCat.Presheaf.pushforward RingCat.{u} f.hom.base).obj
        (topRingPresheafFromComm f) := by
  simpa [topRingPresheafFromComm, RingedSpace.ringCatSheaf] using
    Functor.whiskerRight
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf.obj)
      (forget₂ CommRingCat RingCat)

private noncomputable abbrev topToInvComm (f : X ⟶ Y) :
    topCommRingPresheaf f ⟶
      (𝟭 (Opens X.carrier)).op ⋙ (inverseImageCommRingSheaf f).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X.carrier) (topCommRingPresheaf f) ≫
    ((TopCat.Sheaf.pullbackIso CommRingCat.{u} f.hom.base).inv.app Y.sheaf).hom

private noncomputable abbrev topToInvRing (f : X ⟶ Y) :
    topRingPresheafFromComm f ⟶
      (𝟭 (Opens X.carrier)).op ⋙ (inverseImageRingSheaf f).obj := by
  simpa [topRingPresheafFromComm, inverseImageRingSheaf] using
    Functor.whiskerRight (topToInvComm f) (forget₂ CommRingCat RingCat)

public noncomputable abbrev inverseImageModule (f : X ⟶ Y) :
    Y.Modules ⥤ SheafOfModules (inverseImageRingSheaf f) :=
  SheafOfModules.pullback (inverseImageRingUnit f)

public noncomputable abbrev inverseImageStructureSheafHom (f : X ⟶ Y) :
    inverseImageRingSheaf f ⟶
      (Functor.sheafPushforwardContinuous (𝟭 (Opens X)) RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  by
    simpa [RingedSpace.ringCatSheaf, inverseImageCommRingSheaf, inverseImageRingSheaf] using
      ringSheafHomOverId (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

private noncomputable abbrev commRingStalkToRingStalkIso {T : TopCat.{u}}
    (x : T) (𝒪 : T.Sheaf CommRingCat.{u}) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk 𝒪.obj x) ≅
      (ringSheafOfComm 𝒪).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ 𝒪.obj)

private theorem commRingStalkToRingStalkIso_hom_germ_apply {T : TopCat.{u}}
    (x : T) (𝒪 : T.Sheaf CommRingCat.{u})
    (U : Opens T) (hxU : x ∈ U) (r : 𝒪.obj.obj (op U)) :
    ((commRingStalkToRingStalkIso x 𝒪).hom.hom)
        (TopCat.Presheaf.germ 𝒪.obj U x hxU r) =
      TopCat.Presheaf.germ (ringSheafOfComm 𝒪).presheaf U x hxU r := by
  let j : (OpenNhds x)ᵒᵖ := op ⟨U, hxU⟩
  have h :=
    CategoryTheory.ι_preservesColimitIso_hom
      (G := forget₂ CommRingCat RingCat)
      (F := (OpenNhds.inclusion x).op ⋙ 𝒪.obj) j
  exact congrArg (fun k ↦ k.hom r) h

private theorem toSheafify_stalk_map_germ_apply_commRing {T : TopCat.{u}}
    (ℱ : T.Presheaf CommRingCat.{u}) (U : Opens T) (x : T) (hxU : x ∈ U)
    (r : ℱ.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology T) ℱ))
      (TopCat.Presheaf.germ ℱ U x hxU r) =
      TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology T) ℱ) U x hxU
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology T) ℱ).app (op U) r) := by
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      (CategoryTheory.toSheafify (Opens.grothendieckTopology T) ℱ) r)

private theorem pullbackIso_inv_stalk_map_germ_apply_commRing {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf CommRingCat.{u}) (U : Opens T) (x : T)
    (hxU : x ∈ U)
    (r :
      (CategoryTheory.sheafify (Opens.grothendieckTopology T)
        ((TopCat.Sheaf.forget CommRingCat.{u} S ⋙
          TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪)).obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        ((TopCat.Sheaf.forget CommRingCat.{u} T).map
          ((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).inv.app 𝒪)))
      (TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget CommRingCat.{u} S ⋙
            TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪)) U x hxU r) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} g).obj 𝒪).presheaf).germ U x hxU
        ((((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).inv.app 𝒪).1.app (op U)) r) := by
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      ((TopCat.Sheaf.forget CommRingCat.{u} T).map
        ((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).inv.app 𝒪)) r)

private theorem pullbackIso_inv_toSheafify_unit_section_eq_commRing {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf CommRingCat.{u}) (U : Opens S)
    (r : 𝒪.1.obj (op U)) :
    (((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).inv.app 𝒪).1.app
        (op ((Opens.map g).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget CommRingCat.{u} S ⋙
            TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪)).app
          (op ((Opens.map g).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
          𝒪.1).app (op U)) r)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app 𝒪).1.app
        (op U)) r) := by
  have h :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g)
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g) CommRingCat.{u} (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology T))
      𝒪
  have happ := congrArg (fun k ↦ (k.1.app (op U)) r) h
  have happ' :
      (((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).hom.app 𝒪).1.app
          (op ((Opens.map g).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app 𝒪).1.app
          (op U)) r) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget CommRingCat.{u} S ⋙
            TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪)).app
          (op ((Opens.map g).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
          𝒪.1).app (op U)) r) := by
    simpa using happ
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (op ((Opens.map g).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app 𝒪).1.app
          (op U)) r))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso CommRingCat.{u} g) 𝒪)

private theorem pullbackIso_inv_toSheafify_unit_stalk_germ_eq_commRing {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf CommRingCat.{u}) (U : Opens S) (x : T)
    (hxU : x ∈ (Opens.map g).obj U) (r : 𝒪.1.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        ((TopCat.Sheaf.forget CommRingCat.{u} T).map
          ((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).inv.app 𝒪)))
      (TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget CommRingCat.{u} S ⋙
            TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪))
        ((Opens.map g).obj U) x hxU
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget CommRingCat.{u} S ⋙
            TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪)).app
          (op ((Opens.map g).obj U))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
            𝒪.1).app (op U)) r))) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} g).obj 𝒪).presheaf).germ
        ((Opens.map g).obj U) x hxU
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app 𝒪).1.app
          (op U)) r) := by
  rw [pullbackIso_inv_stalk_map_germ_apply_commRing]
  rw [pullbackIso_inv_toSheafify_unit_section_eq_commRing]

private theorem sheaf_stalkPullbackIso_germ_apply_commRing {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf CommRingCat.{u}) (U : Opens S) (x : T)
    (hxU : x ∈ (Opens.map g).obj U) (r : 𝒪.1.obj (op U)) :
    ((TopCat.Sheaf.stalkPullbackIso g 𝒪 x).hom)
      (𝒪.presheaf.germ U (g x) (by simpa using hxU) r) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} g).obj 𝒪).presheaf).germ
        ((Opens.map g).obj U) x hxU
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app 𝒪).1.app
          (op U)) r) := by
  have hxU' : g x ∈ U := by simpa using hxU
  rw [TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom]
  change
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        ((TopCat.Sheaf.forget CommRingCat.{u} T).map
          ((TopCat.Sheaf.pullbackIso CommRingCat.{u} g).inv.app 𝒪)))
      (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology T)
            ((TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪.obj)))
        ((TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} g 𝒪.presheaf x).hom
          (𝒪.presheaf.germ U (g x) hxU' r))) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} g).obj 𝒪).presheaf).germ
        ((Opens.map g).obj U) x hxU
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app 𝒪).1.app
          (op U)) r)
  set_option backward.isDefEq.respectTransparency false in
  have hpresheaf :
      (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} g 𝒪.presheaf x).hom
          (𝒪.presheaf.germ U (g x) hxU' r) =
        (((TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪.1).germ
          ((Opens.map g).obj U) x hxU
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
            𝒪.1).app (op U)) r)) := by
    let a := 𝒪.presheaf.germ U (g x) hxU'
    let b := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} g 𝒪.1 x
    let c := (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
      𝒪.1).app (op U))
    let d := ((TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪.1).germ
      ((Opens.map g).obj U) x hxU
    have h := TopCat.Presheaf.germ_stalkPullbackHom CommRingCat.{u} g 𝒪.1 x U hxU
    have h' : (ConcreteCategory.hom (a ≫ b)) r =
        (ConcreteCategory.hom (c ≫ d)) r := by
      exact congrArg (fun k ↦ (ConcreteCategory.hom k) r) h
    change (ConcreteCategory.hom b) ((ConcreteCategory.hom a) r) =
      (ConcreteCategory.hom d) ((ConcreteCategory.hom c) r)
    convert h' using 1
  rw [hpresheaf]
  rw [toSheafify_stalk_map_germ_apply_commRing
    (ℱ := ((TopCat.Presheaf.pullback CommRingCat.{u} g).obj 𝒪.obj))
    (U := (Opens.map g).obj U) (x := x) (hxU := hxU)
    (r := ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} g).unit.app
      𝒪.1).app (op U)) r))]
  exact pullbackIso_inv_toSheafify_unit_stalk_germ_eq_commRing
    (g := g) (𝒪 := 𝒪) (U := U) (x := x) (hxU := hxU) (r := r)

private theorem toSheafify_stalk_map_germ_apply_add {T : TopCat.{u}}
    (ℱ : T.Presheaf AddCommGrpCat.{u}) (U : Opens T) (x : T) (hxU : x ∈ U)
    (r : ℱ.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology T) ℱ))
      (TopCat.Presheaf.germ ℱ U x hxU r) =
      TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology T) ℱ) U x hxU
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology T) ℱ).app (op U) r) := by
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      (CategoryTheory.toSheafify (Opens.grothendieckTopology T) ℱ) r)

private theorem pullbackIso_inv_stalk_map_germ_apply_add {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf AddCommGrpCat.{u}) (U : Opens T) (x : T)
    (hxU : x ∈ U)
    (r :
      (CategoryTheory.sheafify (Opens.grothendieckTopology T)
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} S ⋙
          TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪)).obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} T).map
          ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).inv.app 𝒪)))
      (TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} S ⋙
            TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪)) U x hxU r) =
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj 𝒪).presheaf).germ U x hxU
        ((((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).inv.app 𝒪).1.app (op U)) r) := by
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} T).map
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).inv.app 𝒪)) r)

private theorem pullbackIso_inv_toSheafify_unit_section_eq_add {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf AddCommGrpCat.{u}) (U : Opens S)
    (r : 𝒪.1.obj (op U)) :
    (((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).inv.app 𝒪).1.app
        (op ((Opens.map g).obj U)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} S ⋙
            TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪)).app
          (op ((Opens.map g).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
          𝒪.1).app (op U)) r)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app 𝒪).1.app
        (op U)) r) := by
  have h :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g)
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g) AddCommGrpCat.{u} (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology T))
      𝒪
  have happ := congrArg (fun k ↦ (k.1.app (op U)) r) h
  have happ' :
      (((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).hom.app 𝒪).1.app
          (op ((Opens.map g).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app 𝒪).1.app
          (op U)) r) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} S ⋙
            TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪)).app
          (op ((Opens.map g).obj U)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
          𝒪.1).app (op U)) r) := by
    simpa using happ
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (op ((Opens.map g).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app 𝒪).1.app
          (op U)) r))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g) 𝒪)

private theorem pullbackIso_inv_toSheafify_unit_stalk_germ_eq_add {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf AddCommGrpCat.{u}) (U : Opens S) (x : T)
    (hxU : x ∈ (Opens.map g).obj U) (r : 𝒪.1.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} T).map
          ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).inv.app 𝒪)))
      (TopCat.Presheaf.germ
        (CategoryTheory.sheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} S ⋙
            TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪))
        ((Opens.map g).obj U) x hxU
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology T)
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} S ⋙
            TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪)).app
          (op ((Opens.map g).obj U))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
            𝒪.1).app (op U)) r))) =
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj 𝒪).presheaf).germ
        ((Opens.map g).obj U) x hxU
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app 𝒪).1.app
          (op U)) r) := by
  rw [pullbackIso_inv_stalk_map_germ_apply_add]
  rw [pullbackIso_inv_toSheafify_unit_section_eq_add]

private theorem inverseImageRingUnit_hom_eq_top_factor (f : X ⟶ Y) :
    (inverseImageRingUnit f).hom =
      topUnitFromComm f ≫
        (Opens.map f.hom.base).op.whiskerLeft (topToInvRing f) := by
  ext Uop r
  cases Uop with
  | op U =>
      simpa [inverseImageRingUnit, topUnitFromComm, topToInvRing, topToInvComm,
        inverseImageRingSheaf, inverseImageCommRingSheaf, topRingPresheafFromComm,
        topCommRingPresheaf, RingedSpace.ringCatSheaf] using
        (pullbackIso_inv_toSheafify_unit_section_eq_commRing
          (g := f.hom.base) (𝒪 := Y.sheaf) (U := U) (r := r)).symm

private theorem sheaf_stalkPullbackIso_germ_apply_add {T S : TopCat.{u}}
    (g : T ⟶ S) (𝒪 : S.Sheaf AddCommGrpCat.{u}) (U : Opens S) (x : T)
    (hxU : x ∈ (Opens.map g).obj U) (r : 𝒪.1.obj (op U)) :
    ((TopCat.Sheaf.stalkPullbackIso g 𝒪 x).hom)
      (𝒪.presheaf.germ U (g x) (by simpa using hxU) r) =
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj 𝒪).presheaf).germ
        ((Opens.map g).obj U) x hxU
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app 𝒪).1.app
          (op U)) r) := by
  have hxU' : g x ∈ U := by simpa using hxU
  rw [TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom]
  change
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} T).map
          ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} g).inv.app 𝒪)))
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology T)
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪.obj)))
        ((TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} g 𝒪.presheaf x).hom
          (𝒪.presheaf.germ U (g x) hxU' r))) =
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} g).obj 𝒪).presheaf).germ
        ((Opens.map g).obj U) x hxU
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app 𝒪).1.app
          (op U)) r)
  have hpresheaf :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} g 𝒪.presheaf x).hom
          (𝒪.presheaf.germ U (g x) hxU' r) =
        (((TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪.1).germ
          ((Opens.map g).obj U) x hxU
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
            𝒪.1).app (op U)) r)) := by
    let a := 𝒪.presheaf.germ U (g x) hxU'
    let b := TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} g 𝒪.1 x
    let c := (((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
      𝒪.1).app (op U))
    let d := ((TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪.1).germ
      ((Opens.map g).obj U) x hxU
    have h := TopCat.Presheaf.germ_stalkPullbackHom AddCommGrpCat.{u} g 𝒪.1 x U hxU
    have h' : (ConcreteCategory.hom (a ≫ b)) r =
        (ConcreteCategory.hom (c ≫ d)) r := by
      exact congrArg (fun k ↦ (ConcreteCategory.hom k) r) h
    change (ConcreteCategory.hom b) ((ConcreteCategory.hom a) r) =
      (ConcreteCategory.hom d) ((ConcreteCategory.hom c) r)
    convert h' using 1
  rw [hpresheaf]
  rw [toSheafify_stalk_map_germ_apply_add
    (ℱ := ((TopCat.Presheaf.pullback AddCommGrpCat.{u} g).obj 𝒪.obj))
    (U := (Opens.map g).obj U) (x := x) (hxU := hxU)
    (r := ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).unit.app
      𝒪.1).app (op U)) r))]
  exact pullbackIso_inv_toSheafify_unit_stalk_germ_eq_add
    (g := g) (𝒪 := 𝒪) (U := U) (x := x) (hxU := hxU) (r := r)

public theorem inverseImageStructureSheafHomComm_stalkMap_eq (x : X) :
    (TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).hom ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom =
    f.hom.stalkMap x := by
  apply TopCat.Presheaf.stalk_hom_ext Y.presheaf
  intro U hxU
  ext r
  have hxMap : x ∈ (Opens.map f.hom.base).obj U := by
    simpa using hxU
  have hsection :
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom.app (op ((Opens.map f.hom.base).obj U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          Y.sheaf).1.app (op U)) r) =
      f.hom.c.app (op U) r := by
    have hcomm :
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _)
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f) =
          RingedSpace.Hom.commRingSheafPushforwardMap f := by
      exact Equiv.apply_symm_apply
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _)
        (RingedSpace.Hom.commRingSheafPushforwardMap f)
    have hcomp := congrArg (fun η ↦ η.hom.app (op U)) hcomm
    exact ConcreteCategory.congr_hom hcomp r
  calc
    (ConcreteCategory.hom
        ((Y.presheaf.germ U (f.hom.base x) hxU) ≫
          ((TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).hom ≫
            (TopCat.Presheaf.stalkFunctor CommRingCat x).map
              (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom))) r =
      (CommRingCat.Hom.hom
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom))
        ((TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).hom
          (Y.presheaf.germ U (f.hom.base x) hxU r)) := rfl
    _ =
      (CommRingCat.Hom.hom
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom))
        (TopCat.Presheaf.germ (inverseImageCommRingSheaf f).obj
          ((Opens.map f.hom.base).obj U) x hxMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
            Y.sheaf).1.app (op U)) r)) := by
        have hpb :=
          sheaf_stalkPullbackIso_germ_apply_commRing
            (g := f.hom.base) (𝒪 := Y.sheaf) (U := U) (x := x) (hxU := hxMap) (r := r)
        simpa using
          congrArg
            (fun z ↦
              (CommRingCat.Hom.hom
                ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
                  (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom)) z)
            hpb
    _ =
      X.presheaf.germ ((Opens.map f.hom.base).obj U) x hxMap
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom.app
          (op ((Opens.map f.hom.base).obj U))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
            Y.sheaf).1.app (op U)) r)) := by
        simpa [inverseImageCommRingSheaf] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply
            ((Opens.map f.hom.base).obj U) x hxMap
            (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
              Y.sheaf).1.app (op U)) r))
    _ =
      X.presheaf.germ ((Opens.map f.hom.base).obj U) x hxMap (f.hom.c.app (op U) r) := by
        rw [hsection]
    _ =
      (ConcreteCategory.hom
        ((Y.presheaf.germ U (f.hom.base x) hxU) ≫ f.hom.stalkMap x)) r := by
        simpa using
          (congrArg (fun k ↦ (ConcreteCategory.hom k) r)
            (PresheafedSpace.stalkMap_germ f.hom U x hxU)).symm

/-- Helper for Lemma 6.26.4: the topological inverse-image unit followed by the adjoint
structure-sheaf map recovers the original ringed-space structure-sheaf morphism after forgetting
commutativity. -/
public theorem inverseImageRingUnit_comp_inverseImageStructureSheafHom (f : X ⟶ Y) :
    inverseImageRingUnit f ≫
        ((Opens.map f.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map
          (inverseImageStructureSheafHom f) =
      RingedSpace.Hom.toRingCatSheafHom f := by
  have hcomm :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _)
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f) =
        RingedSpace.Hom.commRingSheafPushforwardMap f := by
    -- This is the defining adjunction equation for the adjoint structure-sheaf morphism.
    exact Equiv.apply_symm_apply
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _)
      (RingedSpace.Hom.commRingSheafPushforwardMap f)
  -- Forget commutativity and unfold the identity-pushforward wrapper used by same-space pullback.
  change
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _)
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f)) =
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      (RingedSpace.Hom.commRingSheafPushforwardMap f)
  exact congrArg
    (fun α ↦ (sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat.{u})).map α) hcomm

/-- Helper for Lemma 6.26.4: every module sheaf on a ringed space has the expected module
structure on its stalk over the commutative stalk of the structure sheaf. -/
private instance ringedSpaceModuleStalkModule (ℱ : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) := by
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := ℱ.val
  change Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x)
  infer_instance

/-- Helper for Lemma 6.26.4: the same stalk module structure, with the structure sheaf written as
`(SheafedSpace.sheaf X).obj`. -/
public instance ringedSpaceModuleStalkModule_sheaf_obj (ℱ : X.Modules) (x : X) :
    Module ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
      ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) := by
  change Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)
  infer_instance

/-- Helper for Lemma 6.26.4: two packaged module objects with the same underlying additive group
and sectionwise identical scalar action are canonically isomorphic. -/
public noncomputable def moduleCatOfIsoOfSMulEq
    (R : Type u) [instR : Ring R] (M : Type u) [instM : AddCommGroup M]
    (I J : Module R M)
    (hsmul : ∀ (r : R) (m : M),
      @SMul.smul R M I.toSMul r m = @SMul.smul R M J.toSMul r m) :
    @ModuleCat.of R instR M instM I ≅ @ModuleCat.of R instR M instM J := by
  have hIJ : I = J := by
    cases I
    cases J
    congr
    ext r m
    exact hsmul r m
  subst hIJ
  exact Iso.refl _

public noncomputable def transportedExtendIso
    {R R' S M M' : Type u} [CommRing R] [CommRing R'] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
    (e : R ≃+* R') (p : R' →+* S) (q : R →+* S)
    (hq : q = p.comp e.toRingHom)
    (φ : @LinearEquiv R R' _ _ (e : R →+* R') (e.symm : R' →+* R)
      (RingHomInvPair.of_ringEquiv e) (RingHomInvPair.of_ringEquiv_symm e)
      M M' _ _ _ _) :
    (ModuleCat.extendScalars p).obj (ModuleCat.of R' M') ≅
      (ModuleCat.extendScalars q).obj (ModuleCat.of R M) := by
  subst q
  letI : Algebra R' S := p.toAlgebra
  letI : Algebra R S := (p.comp e.toRingHom).toAlgebra
  letI : RingHomInvPair (e : R →+* R') (e.symm : R' →+* R) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R' →+* R) (e : R →+* R') :=
    RingHomInvPair.of_ringEquiv_symm e
  let idS : @LinearEquiv R' R _ _ (e.symm : R' →+* R) (e : R →+* R') _ _
      S S _ _ _ _ :=
    { toFun := fun s ↦ s
      invFun := fun s ↦ s
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r' s
        change p r' * s = p (e (e.symm r')) * s
        simp }
  let ψ₀ : @LinearEquiv R' R _ _ (e.symm : R' →+* R) (e : R →+* R') _ _
      (S ⊗[R'] M') (S ⊗[R] M) _ _ _ _ :=
    TensorProduct.congr idS φ.symm
  let ψ : S ⊗[R'] M' ≃ₗ[S] S ⊗[R] M :=
    { toFun := ψ₀
      invFun := ψ₀.symm
      left_inv := ψ₀.left_inv
      right_inv := ψ₀.right_inv
      map_add' := ψ₀.map_add
      map_smul' := by
        intro s z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul t m =>
            change ψ₀ (s • (t ⊗ₜ[R'] m)) = s • ψ₀ (t ⊗ₜ[R'] m)
            change (TensorProduct.map idS.toLinearMap φ.symm.toLinearMap)
                (s • t ⊗ₜ[R'] m) = s • (t ⊗ₜ[R] φ.symm m)
            exact
              (TensorProduct.map_tmul (f := idS.toLinearMap) (g := φ.symm.toLinearMap)
                (s • t) m)
        | add z w hz hw => simp [hz, hw] }
  exact LinearEquiv.toModuleIso ψ

private instance pullbackStalkModule (𝒢 : Y.Modules) (x : X) :
    Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk ((f^*).obj 𝒢).val.presheaf x) := by
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := ((f^*).obj 𝒢).val
  change Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x)
  infer_instance

/-- Helper for Lemma 6.26.4: a sheaf isomorphism of modules induces an isomorphism on the
corresponding stalk modules. -/
public noncomputable abbrev stalkModuleIsoOfIso {ℱ 𝒢 : X.Modules} (η : ℱ ≅ 𝒢) (x : X) :
    RingedSpace.stalkModuleCat ℱ x ≅ RingedSpace.stalkModuleCat 𝒢 x := by
  let φ : ℱ.val.presheaf ⟶ 𝒢.val.presheaf :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map η.hom).hom
  -- Take stalks of the underlying presheaf map and prove once that it respects the stalk scalar
  -- action, so it becomes a linear equivalence over `\mathcal O_{X, x}`.
  refine LinearEquiv.toModuleIso
    { toFun := fun t ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ) t
      invFun := fun t ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (((SheafOfModules.toSheaf X.ringCatSheaf).map η.inv).hom : 𝒢.val.presheaf ⟶ ℱ.val.presheaf)) t
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro a b
    exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ).hom.map_add a b
  · intro r m
    obtain ⟨U, hxU, rU, rfl⟩ := X.presheaf.germ_exist x r
    obtain ⟨V, hxV, mV, rfl⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x m
    let W : Opens X := U ⊓ V
    let hxW : x ∈ W := ⟨hxU, hxV⟩
    let iWU : W ⟶ U := homOfLE inf_le_left
    let iWV : W ⟶ V := homOfLE inf_le_right
    let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
    let mW : ℱ.val.obj (op W) := ℱ.val.map iWV.op mV
    have hr : X.presheaf.germ W x hxW rW = X.presheaf.germ U x hxU rU := by
      exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res X.presheaf iWU x hxW) rU
    have hm : TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW =
        TopCat.Presheaf.germ ℱ.val.presheaf V x hxV mV := by
      exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res ℱ.val.presheaf iWV x hxW) mV
    have hsmul₁ :
        X.presheaf.germ W x hxW rW • TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW =
          TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (rW • mW) := by
      symm
      simpa using (PresheafOfModules.germ_smul ℱ.val x W hxW rW mW)
    have hsmul₂ :
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW (rW • (η.hom.val.app (op W)) mW) =
          X.presheaf.germ W x hxW rW •
            TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((η.hom.val.app (op W)) mW) := by
      simpa using (PresheafOfModules.germ_smul 𝒢.val x W hxW rW ((η.hom.val.app (op W)) mW))
    -- Move both stalk representatives to a common neighborhood and use semilinearity there.
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ)
        (X.presheaf.germ U x hxU rU • TopCat.Presheaf.germ ℱ.val.presheaf V x hxV mV) = _
    rw [← hr, ← hm, hsmul₁]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW φ (rW • mW)]
    rw [show (φ.app (op W)) (rW • mW) = rW • (η.hom.val.app (op W)) mW by
      simpa [φ] using (η.hom.val.app (op W)).hom.map_smul rW mW]
    rw [hsmul₂]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW φ mW, hr]
    change X.presheaf.germ U x hxU rU •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((η.hom.val.app (op W)) mW) =
      X.presheaf.germ U x hxU rU •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((η.hom.val.app (op W)) mW)
    rfl
  · intro t
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x t
    let ψ : 𝒢.val.presheaf ⟶ ℱ.val.presheaf :=
      ((SheafOfModules.toSheaf X.ringCatSheaf).map η.inv).hom
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψ)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ)
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hU s)) =
      TopCat.Presheaf.germ ℱ.val.presheaf U x hU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU φ s]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU ψ ((φ.app (op U)) s)]
    have hcomp : (η.hom.val.app (op U)) ≫ (η.inv.val.app (op U)) = 𝟙 _ := by
      exact congrArg (fun k ↦ k.val.app (op U)) η.hom_inv_id
    simpa [φ, ψ] using
      congrArg (fun z ↦ TopCat.Presheaf.germ ℱ.val.presheaf U x hU z)
        (ConcreteCategory.congr_hom hcomp s)
  · intro t
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist 𝒢.val.presheaf x t
    let ψ : 𝒢.val.presheaf ⟶ ℱ.val.presheaf :=
      ((SheafOfModules.toSheaf X.ringCatSheaf).map η.inv).hom
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψ)
          (TopCat.Presheaf.germ 𝒢.val.presheaf U x hU s)) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU ψ s]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU φ ((ψ.app (op U)) s)]
    have hcomp : (η.inv.val.app (op U)) ≫ (η.hom.val.app (op U)) = 𝟙 _ := by
      exact congrArg (fun k ↦ k.val.app (op U)) η.inv_hom_id
    simpa [φ, ψ] using
      congrArg (fun z ↦ TopCat.Presheaf.germ 𝒢.val.presheaf U x hU z)
        (ConcreteCategory.congr_hom hcomp s)

/-- Helper for Lemma 6.26.4: the inverse-image module stalk is naturally a module over the
inverse-image structure-sheaf stalk. -/
private instance inverseImageModuleStalkModule (𝒢 : Y.Modules) (x : X) :
    Module ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
      ↑(TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x) := by
  let M : PresheafOfModules ((inverseImageCommRingSheaf f).obj ⋙ forget₂ CommRingCat RingCat) :=
    ((inverseImageModule f).obj 𝒢).val
  change Module ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
    ↑(TopCat.Presheaf.stalk M.presheaf x)
  infer_instance

public noncomputable abbrev inverseImageModuleStalkHom (𝒢 : Y.Modules) (x : X) :
    TopCat.Presheaf.stalk 𝒢.val.presheaf (f.hom.base x) ⟶
      TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app 𝒢)).hom ≫
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      ((inverseImageModule f).obj 𝒢).val.presheaf x

private theorem inverseImageModuleStalkHom_germ_apply
    (𝒢 : Y.Modules) (U : Opens Y) (x : X)
    (hxU : f.hom.base x ∈ U) (m : 𝒢.val.presheaf.obj (op U)) :
    inverseImageModuleStalkHom f 𝒢 x
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
        ((Opens.map f.hom.base).obj U) x (by simpa using hxU)
        ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
          𝒢).val.app (op U)) m) := by
  dsimp [inverseImageModuleStalkHom]
  change
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
        ((inverseImageModule f).obj 𝒢).val.presheaf x)
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
        (((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
            𝒢)).hom))
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m)) =
    TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
      ((Opens.map f.hom.base).obj U) x (by simpa using hxU)
      ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
        𝒢).val.app (op U)) m)
  have hmap :
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
        (((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
            𝒢)).hom))
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m)) =
      TopCat.Presheaf.germ
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj
          ((SheafOfModules.toSheaf (inverseImageRingSheaf f)).obj
            ((inverseImageModule f).obj 𝒢))).presheaf
        U (f.hom.base x) hxU
        ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
          𝒢).val.app (op U)) m) := by
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f.hom.base x) hxU
        (((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
            𝒢)).hom) m)
  rw [hmap]
  exact ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.hom.base
      ((inverseImageModule f).obj 𝒢).val.presheaf U x hxU)
    ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
      𝒢).val.app (op U)) m)

private theorem inverseImageModuleStalkHom_smul
    (𝒢 : Y.Modules) (x : X)
    (r : ↑(TopCat.Presheaf.stalk Y.presheaf (f.hom.base x)))
    (m : ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf (f.hom.base x))) :
    inverseImageModuleStalkHom f 𝒢 x (r • m) =
      (TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).hom r •
        inverseImageModuleStalkHom f 𝒢 x m := by
  obtain ⟨U, hxU, rU, rfl⟩ := Y.presheaf.germ_exist (f.hom.base x) r
  obtain ⟨V, hxV, mV, rfl⟩ :=
    TopCat.Presheaf.germ_exist 𝒢.val.presheaf (f.hom.base x) m
  let W : Opens Y := U ⊓ V
  let hxW : f.hom.base x ∈ W := ⟨hxU, hxV⟩
  let hxMap : x ∈ (Opens.map f.hom.base).obj W := by
    simpa using hxW
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : Y.presheaf.obj (op W) := Y.presheaf.map iWU.op rU
  let mW : 𝒢.val.obj (op W) := 𝒢.val.map iWV.op mV
  have hr :
      Y.presheaf.germ W (f.hom.base x) hxW rW =
        Y.presheaf.germ U (f.hom.base x) hxU rU := by
    exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res Y.presheaf iWU
      (f.hom.base x) hxW) rU
  have hm :
      TopCat.Presheaf.germ 𝒢.val.presheaf W (f.hom.base x) hxW mW =
        TopCat.Presheaf.germ 𝒢.val.presheaf V (f.hom.base x) hxV mV := by
    exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res 𝒢.val.presheaf iWV
      (f.hom.base x) hxW) mV
  rw [← hr, ← hm]
  let η := (SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app 𝒢
  let ringSec :
      (inverseImageCommRingSheaf f).obj.obj (op ((Opens.map f.hom.base).obj W)) :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
      Y.sheaf).1.app (op W)) rW
  have hdomain :
      Y.presheaf.germ W (f.hom.base x) hxW rW •
          TopCat.Presheaf.germ 𝒢.val.presheaf W (f.hom.base x) hxW mW =
        TopCat.Presheaf.germ 𝒢.val.presheaf W (f.hom.base x) hxW (rW • mW) := by
    symm
    simpa using (PresheafOfModules.germ_smul (M := 𝒢.val)
      (f.hom.base x) W hxW rW mW)
  have hring :
      (TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).hom
          (Y.presheaf.germ W (f.hom.base x) hxW rW) =
        TopCat.Presheaf.germ (inverseImageCommRingSheaf f).obj
          ((Opens.map f.hom.base).obj W) x hxMap ringSec := by
    simpa [ringSec] using
      (sheaf_stalkPullbackIso_germ_apply_commRing
        (g := f.hom.base) (𝒪 := Y.sheaf) (U := W) (x := x)
        (hxU := hxMap) (r := rW))
  have hsection :
      (show ↑(((inverseImageModule f).obj 𝒢).val.obj
          (op ((Opens.map f.hom.base).obj W))) from
        (η.val.app (op W)) (rW • mW)) =
        ringSec •
          (show ↑(((inverseImageModule f).obj 𝒢).val.obj
            (op ((Opens.map f.hom.base).obj W))) from
            (η.val.app (op W)) mW) := by
    simpa [η, ringSec, inverseImageRingUnit, inverseImageRingSheaf,
      inverseImageCommRingSheaf, RingedSpace.ringCatSheaf] using
      (η.val.app (op W)).hom.map_smul rW mW
  calc
    inverseImageModuleStalkHom f 𝒢 x
        (Y.presheaf.germ W (f.hom.base x) hxW rW •
          TopCat.Presheaf.germ 𝒢.val.presheaf W (f.hom.base x) hxW mW)
        =
      inverseImageModuleStalkHom f 𝒢 x
        (TopCat.Presheaf.germ 𝒢.val.presheaf W (f.hom.base x) hxW (rW • mW)) := by
        rw [hdomain]
    _ =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
        ((Opens.map f.hom.base).obj W) x hxMap
        ((η.val.app (op W)) (rW • mW)) := by
        simpa [η] using
          inverseImageModuleStalkHom_germ_apply f 𝒢 W x hxW (rW • mW)
    _ =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
        ((Opens.map f.hom.base).obj W) x hxMap
        (ringSec •
          (show ↑(((inverseImageModule f).obj 𝒢).val.obj
            (op ((Opens.map f.hom.base).obj W))) from
            (η.val.app (op W)) mW)) := by
        simpa using
          congrArg
            (fun z ↦
              TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
                ((Opens.map f.hom.base).obj W) x hxMap z)
            hsection
    _ =
      TopCat.Presheaf.germ (inverseImageCommRingSheaf f).obj
          ((Opens.map f.hom.base).obj W) x hxMap ringSec •
        TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
          ((Opens.map f.hom.base).obj W) x hxMap ((η.val.app (op W)) mW) := by
        simpa using (PresheafOfModules.germ_smul
          (M := ((inverseImageModule f).obj 𝒢).val) x
          ((Opens.map f.hom.base).obj W) hxMap ringSec ((η.val.app (op W)) mW))
    _ =
      (TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).hom
          (Y.presheaf.germ W (f.hom.base x) hxW rW) •
        inverseImageModuleStalkHom f 𝒢 x
          (TopCat.Presheaf.germ 𝒢.val.presheaf W (f.hom.base x) hxW mW) := by
        rw [hring]
        congr 1
        symm
        simpa [η] using
          inverseImageModuleStalkHom_germ_apply f 𝒢 W x hxW mW

private noncomputable abbrev inverseImageModuleUnderlyingPullbackHom (𝒢 : Y.Modules) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.hom.base).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) ⟶
      (SheafOfModules.toSheaf (inverseImageRingSheaf f)).obj ((inverseImageModule f).obj 𝒢) := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).homEquiv _ _).symm ?_
  simpa [inverseImageModule, inverseImageRingUnit, inverseImageRingSheaf,
    inverseImageCommRingSheaf, RingedSpace.ringCatSheaf, SheafOfModules.toSheaf] using
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map
      ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app 𝒢))

private theorem inverseImageModuleUnderlyingPullbackHom_stalk_comp
    (𝒢 : Y.Modules) (x : X) :
    (TopCat.Sheaf.stalkPullbackIso f.hom.base
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom =
    inverseImageModuleStalkHom f 𝒢 x := by
  apply TopCat.Presheaf.stalk_hom_ext 𝒢.val.presheaf
  intro U hxU
  ext m
  let 𝒜 : Y.carrier.Sheaf AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢
  let ℬ : X.carrier.Sheaf AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf (inverseImageRingSheaf f)).obj ((inverseImageModule f).obj 𝒢)
  let β : 𝒜 ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj ℬ := by
    simpa [𝒜, ℬ, inverseImageModule, inverseImageRingUnit, inverseImageRingSheaf,
      inverseImageCommRingSheaf, RingedSpace.ringCatSheaf, SheafOfModules.toSheaf] using
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app 𝒢))
  have hAdj :
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app 𝒜 ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).map
            (inverseImageModuleUnderlyingPullbackHom f 𝒢) =
        β := by
    change
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).homEquiv _ _
        (inverseImageModuleUnderlyingPullbackHom f 𝒢) = β
    simp [inverseImageModuleUnderlyingPullbackHom, β, 𝒜, ℬ]
  have hxMap : x ∈ (Opens.map f.hom.base).obj U := by
    simpa using hxU
  have hsection :
      ((inverseImageModuleUnderlyingPullbackHom f 𝒢).hom.app
          (op ((Opens.map f.hom.base).obj U)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
          𝒜).1.app (op U)) m) =
        (β.hom.app (op U)) m := by
    have hcomp := congrArg (fun η ↦ η.hom.app (op U)) hAdj
    exact ConcreteCategory.congr_hom hcomp m
  calc
    (ConcreteCategory.hom
        ((TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU) ≫
          ((TopCat.Sheaf.stalkPullbackIso f.hom.base
              ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) x).hom ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom))) m =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom)
        ((TopCat.Sheaf.stalkPullbackIso f.hom.base 𝒜 x).hom
          (𝒜.presheaf.germ U (f.hom.base x) hxU m)) := rfl
    _ =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom)
        (TopCat.Presheaf.germ
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.hom.base).obj 𝒜).presheaf)
          ((Opens.map f.hom.base).obj U) x hxMap
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
            𝒜).1.app (op U)) m)) := by
        have hpb := sheaf_stalkPullbackIso_germ_apply_add
          (g := f.hom.base) (𝒪 := 𝒜) (U := U) (x := x) (hxU := hxMap) (r := m)
        simpa [𝒜] using
          congrArg
            (fun z ↦
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom) z)
            hpb
    _ =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
        ((Opens.map f.hom.base).obj U) x hxMap
        (((inverseImageModuleUnderlyingPullbackHom f 𝒢).hom.app
          (op ((Opens.map f.hom.base).obj U)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
            𝒜).1.app (op U)) m)) := by
        simpa [ℬ] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply
            ((Opens.map f.hom.base).obj U) x hxMap
            (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
              𝒜).1.app (op U)) m))
    _ =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
        ((Opens.map f.hom.base).obj U) x hxMap
        ((β.hom.app (op U)) m) := by
        rw [hsection]
    _ =
      (ConcreteCategory.hom
        ((TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU) ≫
          inverseImageModuleStalkHom f 𝒢 x)) m := by
        symm
        change
          (inverseImageModuleStalkHom f 𝒢 x)
            (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
          TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
            ((Opens.map f.hom.base).obj U) x hxMap ((β.hom.app (op U)) m)
        rw [inverseImageModuleStalkHom]
        change
          (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
              ((inverseImageModule f).obj 𝒢).val.presheaf x)
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map β.hom)
              (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m)) =
          TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
            ((Opens.map f.hom.base).obj U) x hxMap ((β.hom.app (op U)) m)
        have hmap :
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map β.hom)
              (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
            TopCat.Presheaf.germ
              ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj ℬ).presheaf
              U (f.hom.base x) hxU ((β.hom.app (op U)) m) := by
          simpa [𝒜] using
            (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f.hom.base x) hxU β.hom m)
        rw [hmap]
        simpa [β, ℬ] using
          congrArg (fun k ↦ (ConcreteCategory.hom k) ((β.hom.app (op U)) m))
          (TopCat.Presheaf.stalkPushforward_germ
              (C := AddCommGrpCat.{u}) f.hom.base
              ((inverseImageModule f).obj 𝒢).val.presheaf U x hxU)

private noncomputable abbrev topUnitModuleStalkHom (𝒢 : Y.Modules) (x : X) :
    TopCat.Presheaf.stalk 𝒢.val.presheaf (f.hom.base x) ⟶
      TopCat.Presheaf.stalk
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf) x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
          𝒢.val)) ≫
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf) x

/-- Helper for Lemma 6.26.4: the topological presheaf inverse-image stalk map sends germs to the
corresponding pulled-back germs. -/
private theorem topUnitModuleStalkHom_germ_apply
    (𝒢 : Y.Modules) (U : Opens Y) (x : X)
    (hxU : f.hom.base x ∈ U) (m : 𝒢.val.presheaf.obj (op U)) :
    topUnitModuleStalkHom f 𝒢 x
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
      TopCat.Presheaf.germ
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf)
        ((Opens.map f.hom.base).obj U) x (by simpa using hxU)
        ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
          𝒢.val).app (op U)) m) := by
  dsimp [topUnitModuleStalkHom]
  change
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf) x)
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
            𝒢.val)))
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m)) =
    TopCat.Presheaf.germ
      (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf)
      ((Opens.map f.hom.base).obj U) x (by simpa using hxU)
      ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
        𝒢.val).app (op U)) m)
  have hmap :
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
            𝒢.val)))
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m)) =
      TopCat.Presheaf.germ
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj
          (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf))
        U (f.hom.base x) hxU
        ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
          𝒢.val).app (op U)) m) := by
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f.hom.base x) hxU
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
            𝒢.val)) m)
  rw [hmap]
  exact ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.hom.base
      (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf) U x hxU)
    ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
      𝒢.val).app (op U)) m)

/-- Helper for Lemma 6.26.4: the underlying abelian presheaf of the topological inverse image,
as a functor of the module. -/
private noncomputable abbrev bcSource :
    PresheafOfModules Y.ringCatSheaf.obj ⥤ ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    TopCat.Presheaf.pullback AddCommGrpCat.{u} f.hom.base

/-- Helper for Lemma 6.26.4: the underlying abelian presheaf of the presheaf module pullback. -/
private noncomputable abbrev bcTarget :
    PresheafOfModules Y.ringCatSheaf.obj ⥤ ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  PresheafOfModules.pullback (topUnitFromComm f) ⋙
    PresheafOfModules.toPresheaf (topRingPresheafFromComm f)

/-- Helper for Lemma 6.26.4: the presheaf-level Beck-Chevalley comparison, defined as the mate of
the (strict) commutation of pushforwards with the underlying-presheaf functor. -/
private noncomputable abbrev bcRho : bcSource f ⟶ bcTarget f :=
  ((CategoryTheory.mateEquiv
    (PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f))
    (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base)).symm
    (CategoryTheory.TwoSquare.mk
      (PresheafOfModules.pushforward (topUnitFromComm f))
      (PresheafOfModules.toPresheaf (topRingPresheafFromComm f))
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base) (𝟙 _))).natTrans

private noncomputable def pullbackTopUnit_freeYonedaIso (Z : Opens Y) :
    (PresheafOfModules.pullback (topUnitFromComm f)).obj
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z)) ≅
      (PresheafOfModules.free (topRingPresheafFromComm f)).obj
        (yoneda.obj ((Opens.map f.hom.base).obj Z)) := by
  exact CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso
    ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).corepresentableBy
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z)))
    (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy
      (topUnitFromComm f) Z)

/-- Helper for Lemma 6.26.4: under the pullback-pushforward adjunction, the free-Yoneda comparison
is the morphism classified by the generator over the pulled-back open. -/
private theorem pullbackTopUnit_freeYonedaIso_hom_adj (Z : Opens Y) :
    ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z))) ≫
      (PresheafOfModules.pushforward (topUnitFromComm f)).map
        (pullbackTopUnit_freeYonedaIso f Z).hom =
    (PresheafOfModules.freeYonedaEquiv
      (R := Y.ringCatSheaf.obj)
      (M := (PresheafOfModules.pushforward (topUnitFromComm f)).obj
        ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
          (yoneda.obj ((Opens.map f.hom.base).obj Z))))
      (X := Z)).symm
      (ModuleCat.freeMk (𝟙 ((Opens.map f.hom.base).obj Z))) := by
  let e :=
    ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).corepresentableBy
      ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z)))
  let e' := PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy
      (topUnitFromComm f) Z
  change e.homEquiv (pullbackTopUnit_freeYonedaIso f Z).hom =
    (PresheafOfModules.freeYonedaEquiv
      (R := Y.ringCatSheaf.obj)
      (M := (PresheafOfModules.pushforward (topUnitFromComm f)).obj
        ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
          (yoneda.obj ((Opens.map f.hom.base).obj Z))))
      (X := Z)).symm (ModuleCat.freeMk (𝟙 ((Opens.map f.hom.base).obj Z)))
  change e.homEquiv (e.uniqueUpToIso e').hom = e'.homEquiv (𝟙 _)
  dsimp [CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso, CategoryTheory.Coyoneda.ext]
  rw [CategoryTheory.Coyoneda.fullyFaithful_preimage]
  change e.homEquiv ((e.homEquiv.trans e'.homEquiv.symm).symm (𝟙 _)) = e'.homEquiv (𝟙 _)
  refine (Equiv.eq_symm_apply e'.homEquiv.symm).2 ?_
  simpa using Equiv.apply_symm_apply (e.homEquiv.trans e'.homEquiv.symm) (𝟙 _)

private theorem bcRho_unit_app (M : PresheafOfModules Y.ringCatSheaf.obj) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app M) =
      (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
          ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj M) ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base).map ((bcRho f).app M) := by
  have h :=
    CategoryTheory.unit_mateEquiv_symm
      (PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f))
      (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base)
      (CategoryTheory.TwoSquare.mk
        (PresheafOfModules.pushforward (topUnitFromComm f))
        (PresheafOfModules.toPresheaf (topRingPresheafFromComm f))
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base) (𝟙 _)) M
  simpa [bcRho, bcSource, bcTarget] using h

/-- Helper for Lemma 6.26.4: the topological presheaf inverse-image stalk map factors through the
stalk pullback isomorphism and the presheaf Beck-Chevalley comparison. -/
private theorem topUnitModuleStalkHom_stalkPullback_comp
    (𝒢 : Y.Modules) (x : X) :
    (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f.hom.base
        𝒢.val.presheaf x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((bcRho f).app 𝒢.val) =
    topUnitModuleStalkHom f 𝒢 x := by
  apply TopCat.Presheaf.stalk_hom_ext 𝒢.val.presheaf
  intro U hxU
  ext m
  have hxMap : x ∈ (Opens.map f.hom.base).obj U := by
    simpa using hxU
  calc
    (ConcreteCategory.hom
        ((TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU) ≫
          ((TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f.hom.base
              𝒢.val.presheaf x).hom ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((bcRho f).app 𝒢.val)))) m =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((bcRho f).app 𝒢.val))
        ((TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f.hom.base
          𝒢.val.presheaf x).hom
          (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m)) := rfl
    _ =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((bcRho f).app 𝒢.val))
        (TopCat.Presheaf.germ
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f.hom.base).obj 𝒢.val.presheaf)
          ((Opens.map f.hom.base).obj U) x hxMap
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
            𝒢.val.presheaf).app (op U)) m)) := by
        have hpb := TopCat.Presheaf.germ_stalkPullbackHom
          AddCommGrpCat.{u} f.hom.base 𝒢.val.presheaf x U hxMap
        have hpb' :
            (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f.hom.base
                𝒢.val.presheaf x).hom
              (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
            TopCat.Presheaf.germ
              ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f.hom.base).obj
                𝒢.val.presheaf)
              ((Opens.map f.hom.base).obj U) x hxMap
              ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
                f.hom.base).unit.app 𝒢.val.presheaf).app (op U)) m) := by
          let a := TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU
          let b := TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u}
            f.hom.base 𝒢.val.presheaf x
          let c := (((TopCat.Presheaf.pullbackPushforwardAdjunction
            AddCommGrpCat.{u} f.hom.base).unit.app 𝒢.val.presheaf).app (op U))
          let d :=
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f.hom.base).obj
              𝒢.val.presheaf).germ ((Opens.map f.hom.base).obj U) x hxMap
          have h' : (ConcreteCategory.hom (a ≫ b)) m =
              (ConcreteCategory.hom (c ≫ d)) m := by
            exact congrArg (fun k ↦ (ConcreteCategory.hom k) m) hpb
          change (ConcreteCategory.hom b) ((ConcreteCategory.hom a) m) =
            (ConcreteCategory.hom d) ((ConcreteCategory.hom c) m)
          convert h' using 1
        simpa using
          congrArg
            (fun z ↦
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                ((bcRho f).app 𝒢.val)) z)
            hpb'
    _ =
      TopCat.Presheaf.germ
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf)
        ((Opens.map f.hom.base).obj U) x hxMap
        ((((bcRho f).app 𝒢.val).app (op ((Opens.map f.hom.base).obj U))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).unit.app
            𝒢.val.presheaf).app (op U)) m))) := by
        simpa using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply
            ((Opens.map f.hom.base).obj U) x hxMap
            ((bcRho f).app 𝒢.val)
            ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
              f.hom.base).unit.app 𝒢.val.presheaf).app (op U)) m))
    _ =
      TopCat.Presheaf.germ
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf)
        ((Opens.map f.hom.base).obj U) x hxMap
        ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
          𝒢.val).app (op U)) m) := by
        have hunit := bcRho_unit_app f 𝒢.val
        have happ := congrArg (fun η ↦ η.app (op U)) hunit
        have hsection :
            (((bcRho f).app 𝒢.val).app (op ((Opens.map f.hom.base).obj U))
              ((((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
                f.hom.base).unit.app 𝒢.val.presheaf).app (op U)) m)) =
            ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
              𝒢.val).app (op U)) m) := by
          exact (ConcreteCategory.congr_hom happ m).symm
        rw [hsection]
    _ =
      (ConcreteCategory.hom
        ((TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU) ≫
          topUnitModuleStalkHom f 𝒢 x)) m := by
        symm
        change
          topUnitModuleStalkHom f 𝒢 x
            (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
          TopCat.Presheaf.germ
            (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf)
            ((Opens.map f.hom.base).obj U) x hxMap
            ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
              𝒢.val).app (op U)) m)
        simpa using topUnitModuleStalkHom_germ_apply f 𝒢 U x hxU m

/-- Helper for Lemma 6.26.4: a nonempty subsingleton Yoneda value is canonically `PUnit`. -/
private noncomputable def homToPUnitIso {T : TopCat.{u}} {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) :
    (yoneda.obj Z).obj V ≅ PUnit := by
  letI : Nonempty ((yoneda.obj Z).obj V) := h
  letI : Subsingleton ((yoneda.obj Z).obj V) := by
    change Subsingleton (V.unop ⟶ Z)
    infer_instance
  exact Equiv.toIso
    (Equiv.punitOfNonemptyOfSubsingleton : ((yoneda.obj Z).obj V) ≃ PUnit)

/-- Helper for Lemma 6.26.4: over a nonempty Yoneda value, the free Yoneda module is the rank-one
free module. -/
private noncomputable def freeYonedaValueModuleIso {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) :
    ((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj
        (yoneda.obj Z)).obj V ≅
      ModuleCat.of.{u} (R.obj V) (R.obj V) :=
  ((ModuleCat.free (R.obj V)).mapIso (homToPUnitIso h)) ≪≫
    (ModuleCat.FreeMonoidal.εIso (R.obj V)).symm

/-- Helper for Lemma 6.26.4: the underlying additive group of a nonempty free-Yoneda value is the
underlying additive group of the coefficient ring. -/
private noncomputable def freeYonedaValueIsoRing {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) :
    (((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj
        ((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj
          (yoneda.obj Z))).obj V) ≅
      ((R ⋙ forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat AddCommGrpCat).obj V := by
  exact (forget₂ (ModuleCat.{u} (R.obj V)) AddCommGrpCat.{u}).mapIso
    (freeYonedaValueModuleIso R h)

/-- Helper for Lemma 6.26.4: the generator of the free Yoneda value maps to `1` in the coefficient
ring. -/
@[simp] private theorem freeYonedaValueModuleIso_hom_freeMk {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) (i : V.unop ⟶ Z) :
    (freeYonedaValueModuleIso R h).hom (ModuleCat.freeMk i) =
      (1 : R.obj V) := by
  letI : Nonempty ((yoneda.obj Z).obj V) := h
  letI : Subsingleton ((yoneda.obj Z).obj V) := by
    change Subsingleton (V.unop ⟶ Z)
    infer_instance
  dsimp [freeYonedaValueIsoRing, homToPUnitIso]
  change ((ModuleCat.FreeMonoidal.εIso (R.obj V)).inv
      (((ModuleCat.free (R.obj V)).map
        ((Equiv.punitOfNonemptyOfSubsingleton : ((yoneda.obj Z).obj V) ≃ PUnit) :
          ((yoneda.obj Z).obj V) → PUnit)) (ModuleCat.freeMk i))) = (1 : R.obj V)
  rw [ModuleCat.free_map_apply, ModuleCat.FreeMonoidal.εIso_inv_freeMk]

/-- Helper for Lemma 6.26.4: the additive version of the previous generator computation. -/
@[simp] private theorem freeYonedaValueIsoRing_hom_freeMk {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) (i : V.unop ⟶ Z) :
    (freeYonedaValueIsoRing R h).hom (ModuleCat.freeMk i) =
      (1 : R.obj V) := by
  exact freeYonedaValueModuleIso_hom_freeMk R h i

/-- Helper for Lemma 6.26.4: the rank-one free-Yoneda module identification sends a single
coefficient to that coefficient. -/
@[simp] private theorem freeYonedaValueModuleIso_hom_single {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) (i : V.unop ⟶ Z) (r : R.obj V) :
    (freeYonedaValueModuleIso R h).hom (Finsupp.single i r) = r := by
  letI : Nonempty ((yoneda.obj Z).obj V) := h
  letI : Subsingleton ((yoneda.obj Z).obj V) := by
    change Subsingleton (V.unop ⟶ Z)
    infer_instance
  dsimp [freeYonedaValueModuleIso, homToPUnitIso, ModuleCat.FreeMonoidal.εIso,
    ModuleCat.free]
  change
      ((Finsupp.lapply PUnit.unit :
          (PUnit →₀ R.obj V) →ₗ[R.obj V] R.obj V)
        (((Finsupp.lmapDomain (R.obj V) (R.obj V)
          (⇑(Equiv.punitOfNonemptyOfSubsingleton : ((yoneda.obj Z).obj V) ≃ PUnit))) :
            (((yoneda.obj Z).obj V) →₀ R.obj V) →ₗ[R.obj V] (PUnit →₀ R.obj V))
          (Finsupp.single i r))) = r
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.lapply_apply,
    Finsupp.single_eq_same]

/-- Helper for Lemma 6.26.4: the additive rank-one free-Yoneda value identification sends a
single coefficient to that coefficient. -/
@[simp] private theorem freeYonedaValueIsoRing_hom_single {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V : (Opens T)ᵒᵖ}
    (h : Nonempty (V.unop ⟶ Z)) (i : V.unop ⟶ Z) (r : R.obj V) :
    (freeYonedaValueIsoRing R h).hom (Finsupp.single i r) = r := by
  exact freeYonedaValueModuleIso_hom_single R h i r

/-- Helper for Lemma 6.26.4: a morphism classified by a free-Yoneda section sends a single
generator to the corresponding restricted section with its coefficient. -/
private theorem freeYonedaEquiv_symm_app_single
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M : PresheafOfModules.{u} R} {X V : C}
    (x : M.obj (op X)) (a : V ⟶ X) (r : R.obj (op V)) :
    (PresheafOfModules.freeYonedaEquiv.symm x).app (op V) (Finsupp.single a r) =
      r • (M.map a.op x) := by
  change ((PresheafOfModules.freeHomEquiv.symm (yonedaEquiv.symm x)).app (op V))
    (Finsupp.single a r) = r • (M.map a.op x)
  dsimp [PresheafOfModules.freeHomEquiv, yonedaEquiv, PresheafOfModules.freeObjDesc]
  let φ := ModuleCat.freeDesc (fun a : V ⟶ X => M.map a.op x)
  change φ.hom (Finsupp.single a r) = r • (M.map a.op x)
  have hs : Finsupp.single a r = r • ModuleCat.freeMk a := by
    exact (Finsupp.smul_single_one a r).symm
  calc
    φ.hom (Finsupp.single a r) = φ.hom (r • ModuleCat.freeMk a) := by
      rw [hs]
      rfl
    _ = r • φ.hom (ModuleCat.freeMk a) := φ.hom.map_smul r (ModuleCat.freeMk a)
    _ = r • (M.map a.op x) := by
      rw [ModuleCat.freeDesc_apply]
      rfl

/-- Helper for Lemma 6.26.4: maps of free-Yoneda modules send free generators to restricted
free generators. -/
@[simp] private theorem freeYoneda_map_freeMk {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ RingCat.{u}) {Z : Opens T} {V W : (Opens T)ᵒᵖ}
    (i : V ⟶ W) (a : V.unop ⟶ Z) :
    (((PresheafOfModules.free R).obj (yoneda.obj Z)).map i) (ModuleCat.freeMk a) =
      ModuleCat.freeMk (i.unop ≫ a) := by
  dsimp [PresheafOfModules.free, PresheafOfModules.freeObj]
  simpa using
    (ModuleCat.freeDesc_apply
      (M := (ModuleCat.restrictScalars (R.map i).hom).obj
        (((PresheafOfModules.free R).obj (yoneda.obj Z)).obj W))
      (fun x => ModuleCat.freeMk (i.unop ≫ x)) a)

/-- Helper for Lemma 6.26.4: maps of free-Yoneda modules send a single generator to the restricted
single generator. -/
@[simp] private theorem freeYoneda_map_single {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ RingCat.{u}) {Z : Opens T} {V W : (Opens T)ᵒᵖ}
    (i : V ⟶ W) (a : V.unop ⟶ Z) (r : R.obj V) :
    (((PresheafOfModules.free R).obj (yoneda.obj Z)).map i) (Finsupp.single a r) =
      Finsupp.single (i.unop ≫ a) ((R.map i).hom r) := by
  let F := (PresheafOfModules.free R).obj (yoneda.obj Z)
  let φ := F.map i
  have hs : Finsupp.single a r = r • ModuleCat.freeMk a := by
    exact (Finsupp.smul_single_one a r).symm
  calc
    φ.hom (Finsupp.single a r) = φ.hom (r • ModuleCat.freeMk a) := by
      exact congrArg φ.hom hs
    _ = (R.map i).hom r • φ.hom (ModuleCat.freeMk a) := φ.hom.map_smul r
      (ModuleCat.freeMk a)
    _ = Finsupp.single (i.unop ≫ a) ((R.map i).hom r) := by
      rw [freeYoneda_map_freeMk]
      exact Finsupp.smul_single_one (i.unop ≫ a) ((R.map i).hom r)

/-- Helper for Lemma 6.26.4: restricted scalar multiplication on a pulled-back free-Yoneda
generator is multiplication by the pulled coefficient. -/
private theorem topUnit_smul_freeYoneda_freeMk
    (Z : Opens Y) {V : (Opens Y)ᵒᵖ} (a : V.unop ⟶ Z) (b : Y.ringCatSheaf.obj.obj V) :
    let N := ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
      (yoneda.obj ((Opens.map f.hom.base).obj Z)))
    b • (show ((PresheafOfModules.pushforward (topUnitFromComm f)).obj N).obj V from
      ModuleCat.freeMk (((Opens.map f.hom.base).map a) ≫ 𝟙 _)) =
    (show ((PresheafOfModules.pushforward (topUnitFromComm f)).obj N).obj V from
      Finsupp.single (((Opens.map f.hom.base).map a) ≫ 𝟙 _)
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          Y.sheaf.obj).app V) b)) := by
  intro N
  dsimp [N, PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀_obj, PresheafOfModules.restrictScalarsObj,
    PresheafOfModules.free, PresheafOfModules.freeObj, ModuleCat.free]
  change (show ↑((topCommRingPresheaf f).obj ((Opens.map f.hom.base).op.obj V)) from
      (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf.obj).app V) b) •
      Finsupp.single (((Opens.map f.hom.base).map a) ≫ 𝟙 _)
        (1 : ↑((topCommRingPresheaf f).obj ((Opens.map f.hom.base).op.obj V))) =
    Finsupp.single (((Opens.map f.hom.base).map a) ≫ 𝟙 _)
      ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf.obj).app V) b)
  exact Finsupp.smul_single_one (((Opens.map f.hom.base).map a) ≫ 𝟙 _)
    ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
      Y.sheaf.obj).app V) b)

/-- Helper for Lemma 6.26.4: the pullback free-Yoneda comparison carries one generator to the
restricted coefficient. -/
private theorem pullbackTopUnit_freeYonedaIso_hom_single
    (Z : Opens Y) {V : (Opens Y)ᵒᵖ} {U : (Opens X)ᵒᵖ}
    (i : (Opens.map f.hom.base).op.obj V ⟶ U)
    (hUZ : Nonempty (U.unop ⟶ (Opens.map f.hom.base).obj Z))
    (a : V.unop ⟶ Z) (b : Y.ringCatSheaf.obj.obj V) :
    (freeYonedaValueIsoRing (topCommRingPresheaf f) hUZ).hom
      ((((PresheafOfModules.free (topRingPresheafFromComm f)).obj
          (yoneda.obj ((Opens.map f.hom.base).obj Z))).map i)
        (((pullbackTopUnit_freeYonedaIso f Z).hom.app ((Opens.map f.hom.base).op.obj V))
          ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
             ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z))).app V)
             (Finsupp.single a b)))) =
    ((topCommRingPresheaf f).map i).hom
      ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf.obj).app V) b) := by
  let M := ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z))
  let N := ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
    (yoneda.obj ((Opens.map f.hom.base).obj Z)))
  have hAdj := congrArg
    (fun τ : M ⟶ (PresheafOfModules.pushforward (topUnitFromComm f)).obj N ↦
      τ.app V (Finsupp.single a b))
    (pullbackTopUnit_freeYonedaIso_hom_adj f Z)
  have hInner :
      ((pullbackTopUnit_freeYonedaIso f Z).hom.app ((Opens.map f.hom.base).op.obj V))
          ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
             ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z))).app V)
             (Finsupp.single a b)) =
        (show N.obj ((Opens.map f.hom.base).op.obj V) from
          ((PresheafOfModules.freeYonedaEquiv
            (M := (PresheafOfModules.pushforward (topUnitFromComm f)).obj N)
            (X := Z)).symm (ModuleCat.freeMk (𝟙 ((Opens.map f.hom.base).obj Z)))).app V
            (Finsupp.single a b)) := by
    simpa [M, N] using hAdj
  rw [hInner]
  rw [freeYonedaEquiv_symm_app_single]
  have hMapA :
      (((PresheafOfModules.pushforward (topUnitFromComm f)).obj N).map a.op)
        (ModuleCat.freeMk (𝟙 ((Opens.map f.hom.base).obj Z))) =
      (show N.obj ((Opens.map f.hom.base).op.obj V) from
        ModuleCat.freeMk (((Opens.map f.hom.base).map a) ≫ 𝟙 _)) := by
    dsimp [N, PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀_obj, PresheafOfModules.restrictScalarsObj]
    simpa using
      (ModuleCat.freeDesc_apply
        (M := (ModuleCat.restrictScalars
          ((topRingPresheafFromComm f).map ((Opens.map f.hom.base).map a).op).hom).obj
          (N.obj ((Opens.map f.hom.base).op.obj V)))
        (fun x => ModuleCat.freeMk (((Opens.map f.hom.base).map a) ≫ x))
        (𝟙 ((Opens.map f.hom.base).obj Z)))
  rw [hMapA]
  have hSmul :
      (show N.obj ((Opens.map f.hom.base).op.obj V) from
        b • (show ((PresheafOfModules.pushforward (topUnitFromComm f)).obj N).obj V from
          ModuleCat.freeMk (((Opens.map f.hom.base).map a) ≫ 𝟙 _))) =
      (Finsupp.single (((Opens.map f.hom.base).map a) ≫ 𝟙 _)
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          Y.sheaf.obj).app V) b) : N.obj ((Opens.map f.hom.base).op.obj V)) := by
    simpa [N] using topUnit_smul_freeYoneda_freeMk f Z a b
  have hSmulMap := congrArg
    (fun x : N.obj ((Opens.map f.hom.base).op.obj V) ↦
      (((PresheafOfModules.free (topRingPresheafFromComm f)).obj
        (yoneda.obj ((Opens.map f.hom.base).obj Z))).map i) x) hSmul
  have hSmulMapPt := congrArg
    (fun x ↦ (freeYonedaValueIsoRing (topCommRingPresheaf f) hUZ).hom x) hSmulMap
  refine hSmulMapPt.trans ?_
  have hMapI := freeYoneda_map_single (topRingPresheafFromComm f) i
    (((Opens.map f.hom.base).map a) ≫ 𝟙 _)
    (show (topRingPresheafFromComm f).obj ((Opens.map f.hom.base).op.obj V) from
      (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf.obj).app V) b)
  have hMapIPt := congrArg
    (fun x ↦ (freeYonedaValueIsoRing (topCommRingPresheaf f) hUZ).hom x) hMapI
  refine hMapIPt.trans ?_
  simpa [topRingPresheafFromComm] using
    freeYonedaValueIsoRing_hom_single (topCommRingPresheaf f) hUZ
      (i.unop ≫ (Opens.map f.hom.base).map a ≫ 𝟙 _)
      (((topCommRingPresheaf f).map i).hom
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          Y.sheaf.obj).app V) b))

/-- Helper for Lemma 6.26.4: a coefficient restriction map viewed as a semilinear module map. -/
private noncomputable def ringMapModule {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {V W : (Opens T)ᵒᵖ} (i : V ⟶ W) :
    ModuleCat.of.{u} (R.obj V) (R.obj V) ⟶
      (ModuleCat.restrictScalars (R.map i).hom).obj
        (ModuleCat.of.{u} (R.obj W) (R.obj W)) :=
  (ModuleCat.semilinearMapAddEquiv (R.map i).hom
    (ModuleCat.of.{u} (R.obj V) (R.obj V))
    (ModuleCat.of.{u} (R.obj W) (R.obj W)))
    (RingHom.toSemilinearMap (R.map i).hom)

/-- Helper for Lemma 6.26.4: the semilinear coefficient restriction map is the underlying ring
map on elements. -/
@[simp] private theorem ringMapModule_apply {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {V W : (Opens T)ᵒᵖ} (i : V ⟶ W)
    (r : R.obj V) :
    ringMapModule R i r = (R.map i).hom r := by
  rfl

/-- Helper for Lemma 6.26.4: the rank-one identifications of nonempty free-Yoneda values are
natural in the indexing open. -/
private theorem freeYonedaValueModuleIso_naturality {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V W : (Opens T)ᵒᵖ}
    (i : V ⟶ W) (hV : Nonempty (V.unop ⟶ Z)) (hW : Nonempty (W.unop ⟶ Z)) :
    ((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj
        (yoneda.obj Z)).map i ≫
      (ModuleCat.restrictScalars (R.map i).hom).map
        (freeYonedaValueModuleIso R hW).hom =
    (freeYonedaValueModuleIso R hV).hom ≫
      ringMapModule R i := by
  apply ModuleCat.free_hom_ext
  intro a
  let F := (PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj Z)
  let m : F.obj V ⟶ (ModuleCat.restrictScalars (R.map i).hom).obj (F.obj W) := F.map i
  let eW :
      (ModuleCat.restrictScalars (R.map i).hom).obj (F.obj W) ⟶
        (ModuleCat.restrictScalars (R.map i).hom).obj
          (ModuleCat.of.{u} (R.obj W) (R.obj W)) :=
    (ModuleCat.restrictScalars (R.map i).hom).map
      (freeYonedaValueModuleIso R hW).hom
  let eV := (freeYonedaValueModuleIso R hV).hom
  change (ConcreteCategory.hom (m ≫ eW)) (ModuleCat.freeMk a) =
    (ConcreteCategory.hom (eV ≫ ringMapModule R i)) (ModuleCat.freeMk a)
  rw [ConcreteCategory.comp_apply (f := m) (g := eW),
    ConcreteCategory.comp_apply (f := eV) (g := ringMapModule R i)]
  dsimp [m, eW, eV, F, PresheafOfModules.free, PresheafOfModules.freeObj]
  have hm :
      (ConcreteCategory.hom
        (ModuleCat.freeDesc
          (M := (ModuleCat.restrictScalars (R.map i).hom).obj
            (((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj
              (yoneda.obj Z)).obj W))
          (fun x => ModuleCat.freeMk (i.unop ≫ x)))) (ModuleCat.freeMk a) =
        ModuleCat.freeMk (i.unop ≫ a) := by
    simpa using
      (ModuleCat.freeDesc_apply
        (M := (ModuleCat.restrictScalars (R.map i).hom).obj
          (((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj
            (yoneda.obj Z)).obj W))
        (fun x => ModuleCat.freeMk (i.unop ≫ x)) a)
  erw [hm]
  change (freeYonedaValueModuleIso R hW).hom (ModuleCat.freeMk (i.unop ≫ a)) =
    ringMapModule R i ((freeYonedaValueModuleIso R hV).hom (ModuleCat.freeMk a))
  rw [freeYonedaValueModuleIso_hom_freeMk R hW (i.unop ≫ a),
    freeYonedaValueModuleIso_hom_freeMk R hV a]
  change (1 : R.obj W) = (R.map i).hom (1 : R.obj V)
  simp

/-- Helper for Lemma 6.26.4: the additive rank-one identifications of nonempty free-Yoneda values
are natural in the indexing open. -/
private theorem freeYonedaValueIsoRing_naturality {T : TopCat.{u}}
    (R : (Opens T)ᵒᵖ ⥤ CommRingCat.{u}) {Z : Opens T} {V W : (Opens T)ᵒᵖ}
    (i : V ⟶ W) (hV : Nonempty (V.unop ⟶ Z)) (hW : Nonempty (W.unop ⟶ Z)) :
    (((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj
        ((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj
          (yoneda.obj Z))).map i) ≫
      (freeYonedaValueIsoRing R hW).hom =
    (freeYonedaValueIsoRing R hV).hom ≫
      (((R ⋙ forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat AddCommGrpCat).map i) := by
  ext x
  have h := congrArg (fun φ => (ConcreteCategory.hom φ) x)
    (freeYonedaValueModuleIso_naturality R i hV hW)
  simpa [freeYonedaValueIsoRing, ringMapModule, PresheafOfModules.toPresheaf,
    PresheafOfModules.presheaf] using h

/-- Helper for Lemma 6.26.4: the costructured-arrow index category for a topological inverse
image. -/
private abbrev lkeIndex {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2) (U : (Opens T1)ᵒᵖ) :=
  CostructuredArrow (Opens.map g).op U

/-- Helper for Lemma 6.26.4: the full subcategory where the indexing open maps to the chosen
Yoneda open. -/
private def lkeIndexToYonedaProp {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    (U : (Opens T1)ᵒᵖ) (Z : Opens T2) : ObjectProperty (lkeIndex g U) :=
  fun A => Nonempty (A.left.unop ⟶ Z)

/-- Helper for Lemma 6.26.4: the nonempty part of the costructured-arrow index category. -/
private abbrev lkeYonedaIndex {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    (U : (Opens T1)ᵒᵖ) (Z : Opens T2) :=
  (lkeIndexToYonedaProp g U Z).FullSubcategory

/-- Helper for Lemma 6.26.4: inclusion of the nonempty Yoneda part of the pointwise LKE index
category. -/
private abbrev lkeYonedaIncl {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    (U : (Opens T1)ᵒᵖ) (Z : Opens T2) : lkeYonedaIndex g U Z ⥤ lkeIndex g U :=
  ObjectProperty.ι (lkeIndexToYonedaProp g U Z)

/-- Helper for Lemma 6.26.4: an index open can be cut by the chosen Yoneda open while remaining
over the target point of the LKE cocone. -/
private theorem lke_le_preimage_inf {T1 T2 : TopCat.{u}} {g : T1 ⟶ T2}
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2} (A : lkeIndex g U)
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) :
    U.unop ≤ (Opens.map g).obj (A.left.unop ⊓ Z) := by
  intro x hx
  exact ⟨A.hom.unop.le hx, hUZ.some.le hx⟩

/-- Helper for Lemma 6.26.4: the cut object used to prove finality of the nonempty Yoneda
subcategory. -/
private noncomputable def lkeCut {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2}
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) (A : lkeIndex g U) :
    lkeYonedaIndex g U Z where
  obj :=
    CostructuredArrow.mk
      (S := (Opens.map g).op) (T := U) (Y := op (A.left.unop ⊓ Z))
      (homOfLE (lke_le_preimage_inf A hUZ)).op
  property := ⟨homOfLE inf_le_right⟩

/-- Helper for Lemma 6.26.4: the canonical map from an index object to its cut. -/
private noncomputable def lkeToCut {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2}
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) (A : lkeIndex g U) :
    A ⟶ (lkeCut g hUZ A).obj :=
  CostructuredArrow.homMk
    (S := (Opens.map g).op) (T := U)
    (homOfLE inf_le_left).op
    (by apply Subsingleton.elim)

/-- Helper for Lemma 6.26.4: the cut object as a structured arrow. -/
private noncomputable def lkeCutStructured {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2}
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) (A : lkeIndex g U) :
    StructuredArrow A (lkeYonedaIncl g U Z) :=
  StructuredArrow.mk (show A ⟶ (lkeYonedaIncl g U Z).obj (lkeCut g hUZ A) from
    lkeToCut g hUZ A)

/-- Helper for Lemma 6.26.4: every structured arrow from an index object receives a unique map
from the cut object. -/
private noncomputable def lkeCutTo {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2}
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) (A : lkeIndex g U)
    (T : StructuredArrow A (lkeYonedaIncl g U Z)) :
    lkeCutStructured g hUZ A ⟶ T := by
  refine StructuredArrow.homMk (ObjectProperty.homMk ?_) ?_
  · refine CostructuredArrow.homMk ?_ (by apply Subsingleton.elim)
    refine (homOfLE ?_).op
    intro y hy
    exact ⟨T.hom.left.unop.le hy, T.right.property.some.le hy⟩
  · apply CostructuredArrow.ext
    apply Subsingleton.elim

/-- Helper for Lemma 6.26.4: the cut structured arrow is initial. -/
private noncomputable def lkeCutStructured_isInitial {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2}
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) (A : lkeIndex g U) :
    Limits.IsInitial (lkeCutStructured g hUZ A) :=
  Limits.IsInitial.ofUniqueHom (lkeCutTo g hUZ A) (by
    intro T m
    apply StructuredArrow.ext
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.ext
    apply Subsingleton.elim)

/-- Helper for Lemma 6.26.4: the nonempty Yoneda subcategory is final when the LKE point maps to
the pulled-back Yoneda open. -/
private theorem lkeYonedaIncl_final_of_le {T1 T2 : TopCat.{u}} (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} {Z : Opens T2}
    (hUZ : Nonempty (U.unop ⟶ (Opens.map g).obj Z)) :
    Functor.Final (lkeYonedaIncl g U Z) where
  out A := CategoryTheory.isConnected_of_isInitial _
    (lkeCutStructured_isInitial g hUZ A)

/-- Helper for Lemma 6.26.4: the free-Yoneda diagram restricted to the nonempty pointwise-LKE
subcategory. -/
private abbrev restrictedFreeYonedaDiagram {T1 T2 : TopCat.{u}}
    (R : (Opens T2)ᵒᵖ ⥤ CommRingCat.{u}) (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} (Z : Opens T2) :
    lkeYonedaIndex g U Z ⥤ AddCommGrpCat.{u} :=
  lkeYonedaIncl g U Z ⋙ CostructuredArrow.proj (Opens.map g).op U ⋙
    (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj
      ((PresheafOfModules.free (R ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj Z))

/-- Helper for Lemma 6.26.4: the coefficient-ring diagram restricted to the nonempty pointwise-LKE
subcategory. -/
private abbrev restrictedRingDiagram {T1 T2 : TopCat.{u}}
    (R : (Opens T2)ᵒᵖ ⥤ CommRingCat.{u}) (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} (Z : Opens T2) :
    lkeYonedaIndex g U Z ⥤ AddCommGrpCat.{u} :=
  lkeYonedaIncl g U Z ⋙ CostructuredArrow.proj (Opens.map g).op U ⋙
    ((R ⋙ forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat AddCommGrpCat)

/-- Helper for Lemma 6.26.4: on the nonempty part of the pointwise-LKE index category, the free
Yoneda diagram is naturally the coefficient-ring diagram. -/
private noncomputable def restrictedFreeYonedaRingNatIso {T1 T2 : TopCat.{u}}
    (R : (Opens T2)ᵒᵖ ⥤ CommRingCat.{u}) (g : T1 ⟶ T2)
    {U : (Opens T1)ᵒᵖ} (Z : Opens T2) :
    restrictedFreeYonedaDiagram R g (U := U) Z ≅
      restrictedRingDiagram R g (U := U) Z :=
  NatIso.ofComponents
    (fun A => freeYonedaValueIsoRing R A.property)
    (by
      intro A B φ
      simpa [restrictedFreeYonedaDiagram, restrictedRingDiagram, lkeYonedaIncl] using
        freeYonedaValueIsoRing_naturality R φ.hom.left A.property B.property)

/-- Helper for Lemma 6.26.4: the additive structure-ring presheaf is the pointwise left Kan
extension of the additive structure ring along the underlying continuous map. -/
private theorem ring_add_lke :
    (topRingPresheafFromComm f ⋙ forget₂ RingCat AddCommGrpCat.{u}).IsLeftKanExtension
      (Functor.whiskerRight (topUnitFromComm f) (forget₂ RingCat AddCommGrpCat.{u})) := by
  let L := (Opens.map f.hom.base).op
  let R : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u} := Y.sheaf.obj
  let G : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  letI : ∀ F : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u}, L.HasLeftKanExtension F := by
    intro F
    infer_instance
  have hComm : (L.lan.obj R).IsLeftKanExtension (L.lanUnit.app R) := by
    infer_instance
  letI : (L.lan.obj R).IsLeftKanExtension (L.lanUnit.app R) := hComm
  haveI : G.PreservesLeftKanExtension R L := by infer_instance
  have h := @Functor.PreservesLeftKanExtension.preserves _ _ _ _ _ _ _ _ G R L
    (by infer_instance) (L.lan.obj R) (L.lanUnit.app R) hComm
  change ((L.lan.obj R) ⋙ G).IsLeftKanExtension
      (Functor.whiskerRight (L.lanUnit.app R) G ≫ (Functor.associator _ _ _).hom)
  exact h

/-- Helper for Lemma 6.26.4: `bcSource` preserves a colimit that the underlying-presheaf functor
preserves (since the topological presheaf pullback is a left adjoint). -/
private noncomputable def bcSourceMapCocone_isColimit
    {J : Type*} [SmallCategory J] {D : J ⥤ PresheafOfModules Y.ringCatSheaf.obj}
    {c : Limits.Cocone D} (hc : Limits.IsColimit c)
    [Limits.PreservesColimit D (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)] :
    Limits.IsColimit ((bcSource f).mapCocone c) := by
  haveI := (TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).leftAdjoint_preservesColimits
  exact Limits.isColimitOfPreserves (TopCat.Presheaf.pullback AddCommGrpCat.{u} f.hom.base)
    (Limits.isColimitOfPreserves (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj) hc)

/-- Helper for Lemma 6.26.4: `bcTarget` preserves a colimit (since the presheaf module pullback is a
left adjoint, and the underlying-presheaf functor preserves what remains). -/
private noncomputable def bcTargetMapCocone_isColimit
    {J : Type*} [SmallCategory J] {D : J ⥤ PresheafOfModules Y.ringCatSheaf.obj}
    {c : Limits.Cocone D} (hc : Limits.IsColimit c)
    [Limits.PreservesColimit (D ⋙ PresheafOfModules.pullback (topUnitFromComm f))
      (PresheafOfModules.toPresheaf (topRingPresheafFromComm f))] :
    Limits.IsColimit ((bcTarget f).mapCocone c) := by
  haveI := (PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).leftAdjoint_preservesColimits
  exact Limits.isColimitOfPreserves (PresheafOfModules.toPresheaf (topRingPresheafFromComm f))
    (Limits.isColimitOfPreserves (PresheafOfModules.pullback (topUnitFromComm f)) hc)

/-- Helper for Lemma 6.26.4: the presheaf Beck-Chevalley comparison is an isomorphism on a free
Yoneda generator. (The crux: a pointwise left Kan extension cofinality computation.) -/
private theorem bcRho_app_free_yoneda_isIso (Z : Opens Y) :
    IsIso ((bcRho f).app ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z))) := by
  let M := ((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z))
  let α :
      (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj M ⟶
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj ((bcTarget f).obj M) :=
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
      ((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app M)
  have hρ : (bcRho f).app M =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).homEquiv
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj M)
        ((bcTarget f).obj M)).symm α := by
    exact
      (Equiv.eq_symm_apply
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.hom.base).homEquiv
          ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj M)
          ((bcTarget f).obj M))).2
        (by
          simpa [α, CategoryTheory.Adjunction.homEquiv_unit] using
            (bcRho_unit_app f M).symm)
  change IsIso ((bcRho f).app M)
  rw [hρ]
  change IsIso
    (((((Opens.map f.hom.base).op).lanAdjunction AddCommGrpCat.{u}).homEquiv
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj M)
      ((bcTarget f).obj M)).symm α)
  rw [CategoryTheory.Functor.isIso_lanAdjunction_homEquiv_symm_iff]
  let eQ :
      (bcTarget f).obj M ≅
        (PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).obj
          ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
            (yoneda.obj ((Opens.map f.hom.base).obj Z))) :=
    (PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).mapIso
      (pullbackTopUnit_freeYonedaIso f Z)
  have hLKE :
      ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).obj
          ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
            (yoneda.obj ((Opens.map f.hom.base).obj Z)))).IsLeftKanExtension
        (α ≫ (Opens.map f.hom.base).op.whiskerLeft eQ.hom) := by
    refine (show (CategoryTheory.Functor.LeftExtension.mk
      ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).obj
          ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
            (yoneda.obj ((Opens.map f.hom.base).obj Z))))
        (α ≫ (Opens.map f.hom.base).op.whiskerLeft eQ.hom)).IsPointwiseLeftKanExtension from ?_).isLeftKanExtension
    intro U
    by_cases hUZ : Nonempty (U.unop ⟶ (Opens.map f.hom.base).obj Z)
    · let freeE : CategoryTheory.Functor.LeftExtension (Opens.map f.hom.base).op
          ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj M) :=
        CategoryTheory.Functor.LeftExtension.mk
          ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).obj
            ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
              (yoneda.obj ((Opens.map f.hom.base).obj Z))))
          (α ≫ (Opens.map f.hom.base).op.whiskerLeft eQ.hom)
      change Limits.IsColimit (freeE.coconeAt U)
      let ringE : CategoryTheory.Functor.LeftExtension (Opens.map f.hom.base).op
          (Y.ringCatSheaf.obj ⋙ forget₂ RingCat AddCommGrpCat.{u}) :=
        CategoryTheory.Functor.LeftExtension.mk
          (topRingPresheafFromComm f ⋙ forget₂ RingCat AddCommGrpCat.{u})
          (Functor.whiskerRight (topUnitFromComm f) (forget₂ RingCat AddCommGrpCat.{u}))
      have hRingLKE :
          (topRingPresheafFromComm f ⋙ forget₂ RingCat AddCommGrpCat.{u}).IsLeftKanExtension
            (Functor.whiskerRight (topUnitFromComm f) (forget₂ RingCat AddCommGrpCat.{u})) :=
        ring_add_lke f
      letI : (topRingPresheafFromComm f ⋙ forget₂ RingCat AddCommGrpCat.{u}).IsLeftKanExtension
          (Functor.whiskerRight (topUnitFromComm f) (forget₂ RingCat AddCommGrpCat.{u})) :=
        hRingLKE
      have hRingFull : Limits.IsColimit (ringE.coconeAt U) := by
        simpa [ringE] using
          (CategoryTheory.Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
            (topRingPresheafFromComm f ⋙ forget₂ RingCat AddCommGrpCat.{u})
            (Functor.whiskerRight (topUnitFromComm f) (forget₂ RingCat AddCommGrpCat.{u})) U)
      let incl := lkeYonedaIncl f.hom.base U Z
      letI : Functor.Final incl := lkeYonedaIncl_final_of_le f.hom.base hUZ
      have hRingJ : Limits.IsColimit ((ringE.coconeAt U).whisker incl) :=
        (Functor.Final.isColimitWhiskerEquiv incl (ringE.coconeAt U)).symm hRingFull
      let eDiag := restrictedFreeYonedaRingNatIso Y.sheaf.obj f.hom.base (U := U) Z
      have hPre : Limits.IsColimit
          ((Limits.Cocone.precompose eDiag.hom).obj ((ringE.coconeAt U).whisker incl)) :=
        (Limits.IsColimit.precomposeHomEquiv eDiag ((ringE.coconeAt U).whisker incl)).symm
          hRingJ
      let ePt := freeYonedaValueIsoRing (topCommRingPresheaf f)
        (Z := (Opens.map f.hom.base).obj Z) (V := U) hUZ
      have eCocone :
          (freeE.coconeAt U).whisker incl ≅
            (Limits.Cocone.precompose eDiag.hom).obj ((ringE.coconeAt U).whisker incl) := by
        refine Limits.Cocone.ext ePt ?_
        intro A
        ext x
        let L := AddCommGrpCat.Hom.hom
          (((freeE.coconeAt U).whisker incl).ι.app A ≫ ePt.hom)
        let R := AddCommGrpCat.Hom.hom
          (((Limits.Cocone.precompose eDiag.hom).obj ((ringE.coconeAt U).whisker incl)).ι.app A)
        change L x = R x
        induction x using Finsupp.induction_linear with
        | zero =>
            exact L.map_zero.trans R.map_zero.symm
        | add x y hx hy =>
            calc
              L (x + y) = L x + L y := L.map_add x y
              _ = R x + R y := by
                rw [hx, hy]
                rfl
              _ = R (x + y) := (R.map_add x y).symm
        | single a b =>
            have hL : L (Finsupp.single a b) =
                ((topCommRingPresheaf f).map (incl.obj A).hom).hom
                  ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                    f.hom.base).unit.app Y.sheaf.obj).app (incl.obj A).left) b) := by
              dsimp [L, freeE, ePt, α, M, eQ]
              erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
                AddMonoidHom.comp_apply]
              change (freeYonedaValueIsoRing (topCommRingPresheaf f) hUZ).hom
                  ((((PresheafOfModules.free (topRingPresheafFromComm f)).obj
                      (yoneda.obj ((Opens.map f.hom.base).obj Z))).map (incl.obj A).hom)
                    (((pullbackTopUnit_freeYonedaIso f Z).hom.app
                      ((Opens.map f.hom.base).op.obj (incl.obj A).left))
                      ((((PresheafOfModules.pullbackPushforwardAdjunction
                         (topUnitFromComm f)).unit.app
                        ((PresheafOfModules.free Y.ringCatSheaf.obj).obj
                          (yoneda.obj Z))).app (incl.obj A).left)
                        (Finsupp.single a b)))) =
                ((topCommRingPresheaf f).map (incl.obj A).hom).hom
                  ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                    f.hom.base).unit.app Y.sheaf.obj).app (incl.obj A).left) b)
              exact pullbackTopUnit_freeYonedaIso_hom_single f Z (incl.obj A).hom hUZ a b
            have hR : R (Finsupp.single a b) =
                ((topCommRingPresheaf f).map (incl.obj A).hom).hom
                  ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                    f.hom.base).unit.app Y.sheaf.obj).app (incl.obj A).left) b) := by
              dsimp [R, ringE, eDiag, restrictedFreeYonedaDiagram,
                restrictedRingDiagram, restrictedFreeYonedaRingNatIso, lkeYonedaIncl]
              erw [AddMonoidHom.comp_apply]
              change (AddCommGrpCat.Hom.hom
                  ((forget₂ RingCat AddCommGrpCat).map
                      ((forget₂ CommRingCat RingCat).map
                        (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                              f.hom.base).unit.app Y.sheaf.obj).app (incl.obj A).left)) ≫
                    (forget₂ RingCat AddCommGrpCat).map
                      ((forget₂ CommRingCat RingCat).map
                        ((topCommRingPresheaf f).map (incl.obj A).hom))))
                  ((freeYonedaValueIsoRing Y.sheaf.obj A.property).hom
                    (Finsupp.single a b)) =
                ((topCommRingPresheaf f).map (incl.obj A).hom).hom
                  ((((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                    f.hom.base).unit.app Y.sheaf.obj).app (incl.obj A).left) b)
              rw [freeYonedaValueIsoRing_hom_single]
              exact AddCommGrpCat.comp_apply
                ((forget₂ RingCat AddCommGrpCat).map
                  ((forget₂ CommRingCat RingCat).map
                    (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                      f.hom.base).unit.app Y.sheaf.obj).app (incl.obj A).left)))
                ((forget₂ RingCat AddCommGrpCat).map
                  ((forget₂ CommRingCat RingCat).map
                    ((topCommRingPresheaf f).map (incl.obj A).hom)))
                b
            exact hL.trans hR.symm
      have hFreeJ : Limits.IsColimit ((freeE.coconeAt U).whisker incl) :=
        hPre.ofIsoColimit eCocone.symm
      exact (Functor.Final.isColimitWhiskerEquiv incl (freeE.coconeAt U)) hFreeJ
    · change Limits.IsColimit ((CategoryTheory.Functor.LeftExtension.mk
        ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).obj
          ((PresheafOfModules.free (topRingPresheafFromComm f)).obj
            (yoneda.obj ((Opens.map f.hom.base).obj Z))))
        (α ≫ (Opens.map f.hom.base).op.whiskerLeft eQ.hom)).coconeAt U)
      refine Limits.IsColimit.ofIsZero _ ?_ ?_
      · refine Functor.isZero _ ?_
        intro A
        have hEmpty : IsEmpty (A.left.unop ⟶ Z) := by
          refine ⟨?_⟩
          intro i
          apply hUZ
          refine ⟨homOfLE ?_⟩
          intro x hx
          exact i.le (A.hom.unop.le hx)
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        change Subsingleton
          (((PresheafOfModules.free Y.ringCatSheaf.obj).obj (yoneda.obj Z)).obj A.left)
        dsimp [PresheafOfModules.free, PresheafOfModules.freeObj, ModuleCat.free]
        constructor
        intro a b
        ext i
        exact isEmptyElim i
      · have hEmpty : IsEmpty (U.unop ⟶ (Opens.map f.hom.base).obj Z) := by
          refine ⟨?_⟩
          intro i
          exact hUZ ⟨i⟩
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        change Subsingleton
          (((PresheafOfModules.free (topRingPresheafFromComm f)).obj
            (yoneda.obj ((Opens.map f.hom.base).obj Z))).obj U)
        dsimp [PresheafOfModules.free, PresheafOfModules.freeObj, ModuleCat.free]
        constructor
        intro a b
        ext i
        exact isEmptyElim i
  exact CategoryTheory.Functor.isLeftKanExtension_of_iso eQ.symm
    (α ≫ (Opens.map f.hom.base).op.whiskerLeft eQ.hom) α
    (by
      have hcomp :
          (Opens.map f.hom.base).op.whiskerLeft eQ.hom ≫
              (Opens.map f.hom.base).op.whiskerLeft eQ.symm.hom =
            𝟙 _ := by
        ext U
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
        simpa using congrArg (fun η ↦ η.app ((Opens.map f.hom.base).op.obj U))
          eQ.hom_inv_id
      simpa using congrArg (fun η ↦ α ≫ η) hcomp)

/-- Helper for Lemma 6.26.4: the presheaf Beck-Chevalley comparison is an isomorphism on a
coproduct of free Yoneda generators. -/
private theorem bcRho_app_freeYonedaCoproduct_isIso
    (M : PresheafOfModules Y.ringCatSheaf.obj) :
    IsIso ((bcRho f).app M.freeYonedaCoproduct) := by
  exact isIso_natTrans_app_of_isColimit (bcRho f)
    (D := Discrete.functor (PresheafOfModules.Elements.freeYoneda (M := M)))
    (c := Limits.colimit.cocone _)
    (bcSourceMapCocone_isColimit f (Limits.colimit.isColimit _))
    (bcTargetMapCocone_isColimit f (Limits.colimit.isColimit _))
    (fun j => by
      obtain ⟨m⟩ := j
      exact bcRho_app_free_yoneda_isIso f m.1.unop)

/-- Helper for Lemma 6.26.4: the presheaf Beck-Chevalley comparison is a natural isomorphism (it is
an isomorphism on every presheaf of modules), via the free-Yoneda cokernel presentation. -/
private theorem bcRho_app_isIso (M : PresheafOfModules Y.ringCatSheaf.obj) :
    IsIso ((bcRho f).app M) := by
  exact isIso_natTrans_app_of_isColimit (bcRho f)
    (D := Limits.parallelPair M.toFreeYonedaCoproduct 0)
    (c := M.freeYonedaCoproductsCokernelCofork)
    (bcSourceMapCocone_isColimit f M.isColimitFreeYonedaCoproductsCokernelCofork)
    (bcTargetMapCocone_isColimit f M.isColimitFreeYonedaCoproductsCokernelCofork)
    (fun j => by
      match j with
      | Limits.WalkingParallelPair.zero =>
          exact bcRho_app_freeYonedaCoproduct_isIso f (Limits.kernel M.fromFreeYonedaCoproduct)
      | Limits.WalkingParallelPair.one =>
          exact bcRho_app_freeYonedaCoproduct_isIso f M)

/-- Helper for Lemma 6.26.4: the topological inverse-image unit on stalks is an isomorphism. -/
private theorem topUnitModuleStalkHom_isIso (𝒢 : Y.Modules) (x : X) :
    IsIso (topUnitModuleStalkHom f 𝒢 x) := by
  have hbc : IsIso ((bcRho f).app 𝒢.val) := bcRho_app_isIso f 𝒢.val
  haveI hbcStalk :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((bcRho f).app 𝒢.val)) := by
    letI : IsIso ((bcRho f).app 𝒢.val) := hbc
    exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      (@asIso _ _ _ _ ((bcRho f).app 𝒢.val) hbc)).isIso_hom
  rw [← topUnitModuleStalkHom_stalkPullback_comp f 𝒢 x]
  exact IsIso.comp_isIso'
    (inferInstance : IsIso (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u}
      f.hom.base 𝒢.val.presheaf x).hom)
    hbcStalk

/-- Helper for Lemma 6.26.4: the comparison from the presheaf inverse-image structure sheaf to the
true inverse-image structure sheaf is an isomorphism on stalks. -/
private theorem topToInvComm_stalk_map_isIso (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (topToInvComm f)) := by
  dsimp [topToInvComm]
  haveI : IsIso (((TopCat.Sheaf.pullbackIso CommRingCat.{u} f.hom.base).inv.app Y.sheaf)) := by
    infer_instance
  simpa [Functor.map_comp] using
    IsIso.comp_isIso'
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u}
        (topCommRingPresheaf f))
      (Functor.map_isIso
        (TopCat.Sheaf.forget CommRingCat.{u} X.carrier ⋙
          TopCat.Presheaf.stalkFunctor CommRingCat.{u} x)
        (((TopCat.Sheaf.pullbackIso CommRingCat.{u} f.hom.base).inv.app Y.sheaf)))

/-- Helper for Lemma 6.26.4: a same-space morphism of commutative-ring presheaves viewed as a
ring-presheaf morphism over the identity. -/
private noncomputable abbrev ringHomOverId
    {T : TopCat.{u}} {𝒪 𝒪' : T.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪') :
    𝒪 ⋙ forget₂ CommRingCat RingCat ⟶
      (𝟭 (Opens T)).op ⋙ (𝒪' ⋙ forget₂ CommRingCat RingCat) := by
  simpa using Functor.whiskerRight p (forget₂ CommRingCat RingCat)

/-- Helper for Lemma 6.26.4: if a same-space ring-presheaf map is a stalkwise isomorphism, then
the unit of module pullback along it is an isomorphism on stalks. -/
private theorem pullback_unit_stalk_isIso_of_stalk_map_isIso
    {T : TopCat.{u}} {𝒪 𝒪' : T.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (M : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) (x : T)
    [IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map p)] :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat)).map
          ((PresheafOfModules.pullbackPushforwardAdjunction
            (ringHomOverId p)).unit.app M))) := by
  let pₓ := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map p).hom
  let eₓ := asIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map p)
  let c := TopCat.Presheaf.stalkBaseChangeComparison p M x
  haveI hc : IsIso c := inferInstance
  let adj := ModuleCat.extendRestrictScalarsAdj pₓ
  let g := adj.homEquiv _ _ c
  haveI hg : IsIso g := by
    haveI hunit : IsIso (adj.unit.app (ModuleCat.of
        ↑(TopCat.Presheaf.stalk 𝒪 x)
        ↑(TopCat.Presheaf.stalk M.presheaf x))) := by
      letI : (ModuleCat.restrictScalars pₓ).IsEquivalence := by
        simpa [pₓ, eₓ] using
          (ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
            eₓ.commRingCatIsoToRingEquiv)
      infer_instance
    haveI hmap : IsIso ((ModuleCat.restrictScalars pₓ).map c) :=
      Functor.map_isIso (ModuleCat.restrictScalars pₓ) c
    change IsIso (adj.unit.app _ ≫ (ModuleCat.restrictScalars pₓ).map c)
    exact IsIso.comp_isIso' hunit hmap
  have hforget :
      IsIso ((forget₂ (ModuleCat
        ↑(TopCat.Presheaf.stalk 𝒪 x)) AddCommGrpCat.{u}).map g) := by
    letI : IsIso g := hg
    exact (Functor.mapIso
      (forget₂ (ModuleCat
        ↑(TopCat.Presheaf.stalk 𝒪 x)) AddCommGrpCat.{u})
      (@asIso _ _ _ _ g hg)).isIso_hom
  convert hforget using 1
  ext m
  dsimp [g, c, adj, TopCat.Presheaf.stalkBaseChangeComparison]
  change _ =
    (ModuleCat.Hom.hom
      (((ModuleCat.extendRestrictScalarsAdj pₓ).homEquiv
          (ModuleCat.of ↑(TopCat.Presheaf.stalk 𝒪 x)
            ↑(TopCat.Presheaf.stalk M.presheaf x))
          (ModuleCat.of
            ↑(TopCat.Presheaf.stalk 𝒪' x)
            ↑(TopCat.Presheaf.stalk
              ((PresheafOfModules.pullback (ringHomOverId p)).obj M).presheaf x)))
        (((ModuleCat.extendRestrictScalarsAdj pₓ).homEquiv _ _).symm _))) m
  rw [Equiv.apply_symm_apply]
  rfl

/-- Helper for Lemma 6.26.4: the same-space structure-sheaf comparison unit on the pulled-back
presheaf module is an isomorphism on stalks. -/
private noncomputable abbrev topToInvRingPullbackUnitStalkMap
    (𝒢 : Y.Modules) (x : X) :
    TopCat.Presheaf.stalk
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf) x ⟶
      TopCat.Presheaf.stalk
        (((PresheafOfModules.pullback (ringHomOverId (topToInvComm f))).obj
          ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).presheaf) x := by
  let M : PresheafOfModules (topRingPresheafFromComm f) :=
    (PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val
  exact
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).map
        ((PresheafOfModules.pullbackPushforwardAdjunction
          (ringHomOverId (topToInvComm f))).unit.app M)))

/-- Helper for Lemma 6.26.4: the same-space structure-sheaf comparison unit is an isomorphism on
stalks after topological pullback. -/
private theorem topToInvRing_pullback_unit_stalk_isIso
    (𝒢 : Y.Modules) (x : X) :
    IsIso (topToInvRingPullbackUnitStalkMap f 𝒢 x) := by
  let M : PresheafOfModules (topRingPresheafFromComm f) :=
    (PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val
  haveI hp : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map (topToInvComm f)) :=
    topToInvComm_stalk_map_isIso f x
  exact pullback_unit_stalk_isIso_of_stalk_map_isIso (topToInvComm f) M x

/-- Helper for Lemma 6.26.4: the sheaf inverse-image unit factors through the presheaf topological
unit and the structure-sheaf comparison viewed over the identity. -/
private theorem inverseImageRingUnit_hom_eq_top_factor_ringHomOverId (f : X ⟶ Y) :
    (inverseImageRingUnit f).hom =
      topUnitFromComm f ≫
        (Opens.map f.hom.base).op.whiskerLeft (ringHomOverId (topToInvComm f)) := by
  rw [inverseImageRingUnit_hom_eq_top_factor]
  rfl

/-- Helper for Lemma 6.26.4: composing the presheaf pullbacks along the topological unit and the
identity structure-sheaf comparison gives the presheaf pullback along the inverse-image unit. -/
private noncomputable def topToInvCompositePullbackIso (𝒢 : Y.Modules) :
    (PresheafOfModules.pullback (ringHomOverId (topToInvComm f))).obj
        ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val) ≅
      (PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val := by
  exact
    (PresheafOfModules.pullbackComp (topUnitFromComm f)
      (ringHomOverId (topToInvComm f))).app 𝒢.val ≪≫
    (eqToIso (congrArg (fun τ ↦ PresheafOfModules.pullback τ)
      (inverseImageRingUnit_hom_eq_top_factor_ringHomOverId f).symm)).app 𝒢.val

/-- Helper for Lemma 6.26.4: sectionwise, the composite pullback comparison is the
pullback-composition map followed by transport along the inverse-image ring-unit factorization. -/
private theorem topToInvCompositePullbackIso_hom_app_eqToHom
    (𝒢 : Y.Modules) (U : Opens Y)
    (z : ((PresheafOfModules.pullback (ringHomOverId (topToInvComm f))).obj
        ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).obj
          (op ((Opens.map f.hom.base).obj U))) :
    ((topToInvCompositePullbackIso f 𝒢).hom.app
        (op ((Opens.map f.hom.base).obj U))) z =
      (((eqToHom (congrArg (fun τ ↦ PresheafOfModules.pullback τ)
          (inverseImageRingUnit_hom_eq_top_factor_ringHomOverId f).symm)).app
          𝒢.val).app (op ((Opens.map f.hom.base).obj U)))
        ((((PresheafOfModules.pullbackComp (topUnitFromComm f)
              (ringHomOverId (topToInvComm f))).hom.app 𝒢.val).app
            (op ((Opens.map f.hom.base).obj U))) z) := by
  rfl

/-- Helper for Lemma 6.26.4: the inverse component of `SheafOfModules.pullbackIso` carries the
sheafified presheaf module pullback-unit section to the sheaf-level module pullback-unit section. -/
private theorem pullbackIso_inv_toSheafify_unit_section_eq_module
    (𝒢 : Y.Modules) (U : Opens Y) (s : 𝒢.val.presheaf.obj (op U)) :
    (ConcreteCategory.hom
      (((SheafOfModules.pullbackIso (inverseImageRingUnit f)).inv.app 𝒢).val.app
        (op ((Opens.map f.hom.base).obj U))))
      ((ConcreteCategory.hom
        ((((PresheafOfModules.sheafificationAdjunction
                (𝟙 (inverseImageRingSheaf f).obj)).unit.app
              ((PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val)).app
            (op ((Opens.map f.hom.base).obj U))))
        ((ConcreteCategory.hom
          (((PresheafOfModules.pullbackPushforwardAdjunction
                (inverseImageRingUnit f).hom).unit.app 𝒢.val).app (op U))) s))) =
      ((ConcreteCategory.hom
        (((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
          𝒢).val.app (op U))) s) := by
  have h :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f))
      (SheafOfModules.PullbackConstruction.adjunction (inverseImageRingUnit f))
      𝒢
  have happ := congrArg (fun k ↦ (k.val.app (op U)) s) h
  have happ' :
      (ConcreteCategory.hom
        (((SheafOfModules.pullbackIso (inverseImageRingUnit f)).hom.app 𝒢).val.app
          (op ((Opens.map f.hom.base).obj U))))
        ((ConcreteCategory.hom
          (((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
            𝒢).val.app (op U))) s) =
      (ConcreteCategory.hom
        ((((PresheafOfModules.sheafificationAdjunction
                (𝟙 (inverseImageRingSheaf f).obj)).unit.app
              ((PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val)).app
            (op ((Opens.map f.hom.base).obj U))))
        ((ConcreteCategory.hom
          (((PresheafOfModules.pullbackPushforwardAdjunction
                (inverseImageRingUnit f).hom).unit.app 𝒢.val).app (op U))) s)) := by
    simpa [SheafOfModules.PullbackConstruction.adjunction, SheafOfModules.pullbackIso] using happ
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.val.app (op ((Opens.map f.hom.base).obj U)))
        ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
            𝒢).val.app (op U)) s))
      (Iso.hom_inv_id_app (SheafOfModules.pullbackIso (inverseImageRingUnit f)) 𝒢)

/-- Helper for Lemma 6.26.4: for presheaves of modules, the pullback-composition isomorphism
identifies the two-step pullback adjunction unit with the one-step pullback adjunction unit. -/
private theorem presheaf_pullbackComp_unit_section_eq
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}} {T : Eᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ T)
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (M : PresheafOfModules.{u} S) (U : C) (m : M.obj (op U)) :
    (((PresheafOfModules.pullbackComp φ ψ).hom.app M).app (op ((F ⋙ G).obj U)))
      ((((PresheafOfModules.pullbackPushforwardAdjunction ψ).unit.app
          ((PresheafOfModules.pullback φ).obj M)).app (op (F.obj U)))
        ((((PresheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).app (op U)) m)) =
      ((((PresheafOfModules.pullbackPushforwardAdjunction
          (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ)).unit.app M).app (op U)) m) := by
  have hconj :
      CategoryTheory.conjugateEquiv
        (PresheafOfModules.pullbackPushforwardAdjunction
          (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ))
        ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
          (PresheafOfModules.pullbackPushforwardAdjunction ψ))
        (PresheafOfModules.pullbackComp φ ψ).hom =
      (PresheafOfModules.pushforwardComp φ ψ).inv := by
    simpa only [PresheafOfModules.pullbackComp, CategoryTheory.Adjunction.leftAdjointCompIso,
      CategoryTheory.conjugateIsoEquiv_symm_apply_hom] using
      (Equiv.apply_symm_apply
          (CategoryTheory.conjugateEquiv
          (PresheafOfModules.pullbackPushforwardAdjunction
            (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ))
          ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
            (PresheafOfModules.pullbackPushforwardAdjunction ψ)))
        (PresheafOfModules.pushforwardComp φ ψ).inv)
  have hunit := CategoryTheory.unit_conjugateEquiv
    (PresheafOfModules.pullbackPushforwardAdjunction
      (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ))
    ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
      (PresheafOfModules.pullbackPushforwardAdjunction ψ))
    (PresheafOfModules.pullbackComp φ ψ).hom M
  rw [hconj] at hunit
  have happ := congrArg (fun k ↦ (k.app (op U)) m) hunit
  simpa [CategoryTheory.Adjunction.comp_unit_app, PresheafOfModules.pushforwardComp] using
    happ.symm

/-- Helper for Lemma 6.26.4: transporting presheaf module pullback along an equality of ring maps
sends the pullback adjunction unit for the first map to the unit for the second map. -/
private theorem presheaf_pullback_unit_eqToHom_section_eq
    {C D : Type u} [SmallCategory C] [SmallCategory D] {F : C ⥤ D}
    {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    (φ φ' : S ⟶ F.op ⋙ R)
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward φ').IsRightAdjoint]
    (h : φ = φ') (M : PresheafOfModules.{u} S) (U : C) (m : M.obj (op U)) :
    (((eqToHom (congrArg (fun τ ↦ PresheafOfModules.pullback τ) h)).app M).app
        (op (F.obj U)))
      ((((PresheafOfModules.pullbackPushforwardAdjunction φ).unit.app M).app (op U)) m) =
      ((((PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app M).app (op U)) m) := by
  subst φ'
  rfl

/-- Helper for Lemma 6.26.4: the presheaf module pullback unit for the factored topological
ring map becomes the presheaf module pullback unit for the inverse-image ring unit. -/
private theorem topToInvCompositePullbackIso_unit_section_eq
    (𝒢 : Y.Modules) (U : Opens Y) (m : 𝒢.val.presheaf.obj (op U)) :
    ((topToInvCompositePullbackIso f 𝒢).hom.app (op ((Opens.map f.hom.base).obj U)))
      ((((PresheafOfModules.pullbackPushforwardAdjunction
              (ringHomOverId (topToInvComm f))).unit.app
            ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).app
          (op ((Opens.map f.hom.base).obj U)))
        ((((PresheafOfModules.pullbackPushforwardAdjunction
              (topUnitFromComm f)).unit.app 𝒢.val).app (op U)) m)) =
      ((((PresheafOfModules.pullbackPushforwardAdjunction
            (inverseImageRingUnit f).hom).unit.app 𝒢.val).app (op U)) m) := by
  have hφ₀ :
      topUnitFromComm f ≫
          (Opens.map f.hom.base).op.whiskerLeft (ringHomOverId (topToInvComm f)) =
        (inverseImageRingUnit f).hom :=
    (inverseImageRingUnit_hom_eq_top_factor_ringHomOverId f).symm
  have hcomp := presheaf_pullbackComp_unit_section_eq
    (φ := topUnitFromComm f) (ψ := ringHomOverId (topToInvComm f)) 𝒢.val U m
  have htransport := presheaf_pullback_unit_eqToHom_section_eq
    (φ := topUnitFromComm f ≫
      (Opens.map f.hom.base).op.whiskerLeft (ringHomOverId (topToInvComm f)))
    (φ' := (inverseImageRingUnit f).hom) hφ₀ 𝒢.val U m
  have hstep :
      ((topToInvCompositePullbackIso f 𝒢).hom.app (op ((Opens.map f.hom.base).obj U)))
        ((((PresheafOfModules.pullbackPushforwardAdjunction
                (ringHomOverId (topToInvComm f))).unit.app
              ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).app
            (op ((Opens.map f.hom.base).obj U)))
          ((((PresheafOfModules.pullbackPushforwardAdjunction
                (topUnitFromComm f)).unit.app 𝒢.val).app (op U)) m)) =
      (((eqToHom (congrArg (fun τ ↦ PresheafOfModules.pullback τ) hφ₀)).app
          𝒢.val).app (op ((Opens.map f.hom.base).obj U)))
        ((((PresheafOfModules.pullbackPushforwardAdjunction
              (topUnitFromComm f ≫
                (Opens.map f.hom.base).op.whiskerLeft
                  (ringHomOverId (topToInvComm f)))).unit.app 𝒢.val).app (op U)) m) := by
    let z :=
      (((((PresheafOfModules.pullbackPushforwardAdjunction
                (ringHomOverId (topToInvComm f))).unit.app
              ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).app
            (op ((Opens.map f.hom.base).obj U)))
          ((((PresheafOfModules.pullbackPushforwardAdjunction
                (topUnitFromComm f)).unit.app 𝒢.val).app (op U)) m)))
    have hdef := topToInvCompositePullbackIso_hom_app_eqToHom f 𝒢 U z
    have hcompEq :=
      congrArg
        (fun y ↦
          (((eqToHom (congrArg (fun τ ↦ PresheafOfModules.pullback τ) hφ₀)).app
              𝒢.val).app (op ((Opens.map f.hom.base).obj U))) y)
        hcomp
    exact hdef.trans hcompEq
  exact hstep.trans htransport

/-- Helper for Lemma 6.26.4: the sectionwise composite from the two-step presheaf pullback through
sheafification and `pullbackIso.inv` is the sheaf inverse-image module unit. -/
private theorem topToInvStalkBridge_section_eq
    (𝒢 : Y.Modules) (U : Opens Y) (m : 𝒢.val.presheaf.obj (op U)) :
    ((((SheafOfModules.toSheaf (inverseImageRingSheaf f)).map
            ((SheafOfModules.pullbackIso (inverseImageRingUnit f)).app 𝒢).inv).hom.app
        (op ((Opens.map f.hom.base).obj U)))
      ((((PresheafOfModules.sheafificationAdjunction
              (𝟙 (inverseImageRingSheaf f).obj)).unit.app
            ((PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val)).app
          (op ((Opens.map f.hom.base).obj U)))
        (((topToInvCompositePullbackIso f 𝒢).hom.app
            (op ((Opens.map f.hom.base).obj U)))
          ((((PresheafOfModules.pullbackPushforwardAdjunction
                  (ringHomOverId (topToInvComm f))).unit.app
                ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).app
              (op ((Opens.map f.hom.base).obj U)))
            ((((PresheafOfModules.pullbackPushforwardAdjunction
                  (topUnitFromComm f)).unit.app 𝒢.val).app (op U)) m))))) =
      ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
          𝒢).val.app (op U)) m) := by
  rw [topToInvCompositePullbackIso_unit_section_eq]
  simpa using pullbackIso_inv_toSheafify_unit_section_eq_module f 𝒢 U m

/-- Helper for Lemma 6.26.4: the stalk map from the iterated presheaf pullback through
sheafification to the inverse-image module. -/
private noncomputable abbrev topToInvToInverseStalkMap
    (𝒢 : Y.Modules) (x : X) :
    TopCat.Presheaf.stalk
        (((PresheafOfModules.pullback (ringHomOverId (topToInvComm f))).obj
          ((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val)).presheaf) x ⟶
      TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x := by
  let Mcomp : PresheafOfModules (inverseImageRingSheaf f).obj :=
    (PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val
  exact
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        (topToInvCompositePullbackIso f 𝒢).hom)) ≫
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (inverseImageRingSheaf f).obj)).unit.app Mcomp))) ≫
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (((SheafOfModules.toSheaf (inverseImageRingSheaf f)).map
        ((SheafOfModules.pullbackIso (inverseImageRingUnit f)).app 𝒢).inv).hom))

/-- Helper for Lemma 6.26.4: the stalk map from the iterated presheaf pullback to the
inverse-image module is an isomorphism. -/
private theorem topToInvToInverseStalkMap_isIso
    (𝒢 : Y.Modules) (x : X) :
    IsIso (topToInvToInverseStalkMap f 𝒢 x) := by
  let Mcomp : PresheafOfModules (inverseImageRingSheaf f).obj :=
    (PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val
  haveI hcomp :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map
          (topToInvCompositePullbackIso f 𝒢).hom)) := by
    exact Functor.map_isIso
      (PresheafOfModules.toPresheaf _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (topToInvCompositePullbackIso f 𝒢).hom
  haveI hsheaf :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (inverseImageRingSheaf f).obj)).unit.app Mcomp))) := by
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
        Mcomp.presheaf)
  haveI hpullback :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((SheafOfModules.toSheaf (inverseImageRingSheaf f)).map
          ((SheafOfModules.pullbackIso (inverseImageRingUnit f)).app 𝒢).inv).hom)) := by
    let e := (SheafOfModules.pullbackIso (inverseImageRingUnit f)).app 𝒢
    let η := (SheafOfModules.toSheaf (inverseImageRingSheaf f)).map e.inv
    let φ := η.hom
    haveI hη : IsIso η := by
      dsimp [η]
      exact Functor.map_isIso (SheafOfModules.toSheaf (inverseImageRingSheaf f)) e.inv
    haveI hφ : IsIso φ := by
      dsimp [φ, η]
      exact Functor.map_isIso (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier)
        ((SheafOfModules.toSheaf (inverseImageRingSheaf f)).map e.inv)
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ) :=
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        (@asIso _ _ _ _ φ hφ)).isIso_hom
    simpa [φ, η, e] using this
  dsimp [topToInvToInverseStalkMap]
  exact IsIso.comp_isIso' hcomp (IsIso.comp_isIso' hsheaf hpullback)

/-- Helper for Lemma 6.26.4: the full stalk bridge from the presheaf topological pullback to the
sheaf inverse-image module. -/
private noncomputable abbrev topToInvStalkBridge (𝒢 : Y.Modules) (x : X) :
    TopCat.Presheaf.stalk
        (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf) x ⟶
      TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x :=
  topToInvRingPullbackUnitStalkMap f 𝒢 x ≫ topToInvToInverseStalkMap f 𝒢 x

/-- Helper for Lemma 6.26.4: the full stalk bridge from the presheaf topological pullback to the
sheaf inverse-image module is an isomorphism. -/
private theorem topToInvStalkBridge_isIso (𝒢 : Y.Modules) (x : X) :
    IsIso (topToInvStalkBridge f 𝒢 x) := by
  dsimp [topToInvStalkBridge]
  exact IsIso.comp_isIso'
    (topToInvRing_pullback_unit_stalk_isIso f 𝒢 x)
    (topToInvToInverseStalkMap_isIso f 𝒢 x)

/-- Helper for Lemma 6.26.4: a fourfold composite of stalk-functor maps sends a germ to the germ of
the fourfold sectionwise composite. -/
private theorem stalkFunctor_map_four_germ_apply
    {T : TopCat.{u}} {F₀ F₁ F₂ F₃ F₄ : T.Presheaf AddCommGrpCat.{u}}
    (α₀ : F₀ ⟶ F₁) (α₁ : F₁ ⟶ F₂) (α₂ : F₂ ⟶ F₃) (α₃ : F₃ ⟶ F₄)
    (U : Opens T) (x : T) (hxU : x ∈ U) (s : F₀.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α₃)
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α₂)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α₁)
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α₀)
            (TopCat.Presheaf.germ F₀ U x hxU s)))) =
      TopCat.Presheaf.germ F₄ U x hxU
        ((α₃.app (op U)) ((α₂.app (op U)) ((α₁.app (op U)) ((α₀.app (op U)) s)))) := by
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU α₀ s]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU α₁ ((α₀.app (op U)) s)]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU α₂
    ((α₁.app (op U)) ((α₀.app (op U)) s))]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU α₃
    ((α₂.app (op U)) ((α₁.app (op U)) ((α₀.app (op U)) s)))]

/-- Helper for Lemma 6.26.4: the stalk bridge sends the presheaf topological inverse-image germ
to the corresponding sheaf inverse-image module germ. -/
private theorem topToInvStalkBridge_germ_apply
    (𝒢 : Y.Modules) (U : Opens Y) (x : X)
    (hxU : f.hom.base x ∈ U) (m : 𝒢.val.presheaf.obj (op U)) :
    topToInvStalkBridge f 𝒢 x
        (TopCat.Presheaf.germ
          (((PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val).presheaf)
          ((Opens.map f.hom.base).obj U) x (by simpa using hxU)
          ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
            𝒢.val).app (op U)) m)) =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf
        ((Opens.map f.hom.base).obj U) x (by simpa using hxU)
        ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
          𝒢).val.app (op U)) m) := by
  let W : Opens X := (Opens.map f.hom.base).obj U
  have hxW : x ∈ W := by
    simpa [W] using hxU
  let M₀ : PresheafOfModules (topRingPresheafFromComm f) :=
    (PresheafOfModules.pullback (topUnitFromComm f)).obj 𝒢.val
  let υ := (PresheafOfModules.pullbackPushforwardAdjunction
    (ringHomOverId (topToInvComm f))).unit.app M₀
  let M₁ :=
    (PresheafOfModules.pullback (ringHomOverId (topToInvComm f))).obj M₀
  let κ := (topToInvCompositePullbackIso f 𝒢).hom
  let M₂ : PresheafOfModules (inverseImageRingSheaf f).obj :=
    (PresheafOfModules.pullback (inverseImageRingUnit f).hom).obj 𝒢.val
  let σ := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((inverseImageRingSheaf f).obj))).unit.app M₂
  let π :=
    (((SheafOfModules.toSheaf (inverseImageRingSheaf f)).map
      ((SheafOfModules.pullbackIso (inverseImageRingUnit f)).app 𝒢).inv).hom)
  let s₀ : M₀.obj (op W) :=
    ((((PresheafOfModules.pullbackPushforwardAdjunction (topUnitFromComm f)).unit.app
      𝒢.val).app (op U)) m)
  change topToInvStalkBridge f 𝒢 x (TopCat.Presheaf.germ M₀.presheaf W x hxW s₀) =
    TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf W x hxW
      ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
        𝒢).val.app (op U)) m)
  dsimp [topToInvStalkBridge, topToInvRingPullbackUnitStalkMap, topToInvToInverseStalkMap]
  erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply]
  dsimp [AddCommGrpCat.Hom.hom]
  have hυ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).map υ))
        (TopCat.Presheaf.germ M₀.presheaf W x hxW s₀) =
      TopCat.Presheaf.germ M₁.presheaf W x hxW ((υ.app (op W)) s₀) := by
    simpa [M₀, M₁, υ, W, s₀] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).map υ) s₀)
  have hκ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map κ))
        (TopCat.Presheaf.germ M₁.presheaf W x hxW ((υ.app (op W)) s₀)) =
      TopCat.Presheaf.germ M₂.presheaf W x hxW ((κ.app (op W)) ((υ.app (op W)) s₀)) := by
    exact
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        ((PresheafOfModules.toPresheaf _).map κ) ((υ.app (op W)) s₀))
  have hσ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ))
        (TopCat.Presheaf.germ M₂.presheaf W x hxW
          ((κ.app (op W)) ((υ.app (op W)) s₀))) =
      TopCat.Presheaf.germ
        (((SheafOfModules.toSheaf (inverseImageRingSheaf f)).obj
          ((PresheafOfModules.sheafification
            (R₀ := (inverseImageRingSheaf f).obj)
            (𝟙 ((inverseImageRingSheaf f).obj))).obj M₂)).obj)
        W x hxW ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀))) := by
    simpa [M₂, σ, W] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ)
        ((κ.app (op W)) ((υ.app (op W)) s₀)))
  have hπ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
        (TopCat.Presheaf.germ
          (((SheafOfModules.toSheaf (inverseImageRingSheaf f)).obj
            ((PresheafOfModules.sheafification
              (R₀ := (inverseImageRingSheaf f).obj)
              (𝟙 ((inverseImageRingSheaf f).obj))).obj M₂)).obj)
          W x hxW ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀)))) =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf W x hxW
        ((π.app (op W)) ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀)))) := by
    simpa [π, W] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW π
        ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀))))
  have hυ' :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf (topRingPresheafFromComm f)).map
            ((PresheafOfModules.pullbackPushforwardAdjunction
              (ringHomOverId (topToInvComm f))).unit.app
                ((PresheafOfModules.pullback
                  (Functor.whiskerRight
                    ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
                      f.hom.base).unit.app Y.sheaf.obj)
                    (forget₂ CommRingCat RingCat))).obj 𝒢.val))))
        (TopCat.Presheaf.germ M₀.presheaf W x hxW s₀) =
      TopCat.Presheaf.germ M₁.presheaf W x hxW ((υ.app (op W)) s₀) := by
    simpa [M₀, topUnitFromComm] using hυ
  have htail :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ))
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((PresheafOfModules.toPresheaf _).map κ))
            (TopCat.Presheaf.germ M₁.presheaf W x hxW ((υ.app (op W)) s₀)))) =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf W x hxW
        ((π.app (op W)) ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀)))) := by
    calc
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ))
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((PresheafOfModules.toPresheaf _).map κ))
              (TopCat.Presheaf.germ M₁.presheaf W x hxW ((υ.app (op W)) s₀)))) =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ))
            (TopCat.Presheaf.germ M₂.presheaf W x hxW
              ((κ.app (op W)) ((υ.app (op W)) s₀)))) := by
          exact congrArg
            (fun z ↦
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
                (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                  ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ)) z))
            hκ
      _ =
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
          (TopCat.Presheaf.germ
            (((SheafOfModules.toSheaf (inverseImageRingSheaf f)).obj
              ((PresheafOfModules.sheafification
                (R₀ := (inverseImageRingSheaf f).obj)
                (𝟙 ((inverseImageRingSheaf f).obj))).obj M₂)).obj)
            W x hxW ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀)))) := by
          exact congrArg
            (fun z ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π) z)
            hσ
      _ =
        TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf W x hxW
          ((π.app (op W)) ((σ.app (op W)) ((κ.app (op W)) ((υ.app (op W)) s₀)))) := hπ
  erw [hυ']
  change
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((PresheafOfModules.toPresheaf (inverseImageRingSheaf f).obj).map σ))
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((PresheafOfModules.toPresheaf _).map κ))
            (TopCat.Presheaf.germ M₁.presheaf W x hxW ((υ.app (op W)) s₀)))) =
      TopCat.Presheaf.germ ((inverseImageModule f).obj 𝒢).val.presheaf W x hxW
        ((((SheafOfModules.pullbackPushforwardAdjunction (inverseImageRingUnit f)).unit.app
          𝒢).val.app (op U)) m)
  rw [htail]
  congr 1
  simpa [W, M₀, M₂, υ, κ, σ, π, s₀] using
    (topToInvStalkBridge_section_eq f 𝒢 U m)

/-- Helper for Lemma 6.26.4: the inverse-image module stalk map is the composite through the
presheaf topological pullback and the sheafification bridge. -/
private theorem inverseImageModuleStalkHom_eq_topToInvStalkBridge
    (𝒢 : Y.Modules) (x : X) :
    inverseImageModuleStalkHom f 𝒢 x =
      topUnitModuleStalkHom f 𝒢 x ≫ topToInvStalkBridge f 𝒢 x := by
  apply TopCat.Presheaf.stalk_hom_ext 𝒢.val.presheaf
  intro U hxU
  ext m
  change
    inverseImageModuleStalkHom f 𝒢 x
        (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m) =
      topToInvStalkBridge f 𝒢 x
        (topUnitModuleStalkHom f 𝒢 x
          (TopCat.Presheaf.germ 𝒢.val.presheaf U (f.hom.base x) hxU m))
  rw [inverseImageModuleStalkHom_germ_apply]
  rw [topUnitModuleStalkHom_germ_apply]
  exact (topToInvStalkBridge_germ_apply f 𝒢 U x hxU m).symm

/-- Helper for Lemma 6.26.4: the canonical inverse-image module stalk map is an isomorphism,
factored through the presheaf topological inverse-image stalk and sheafification bridge. -/
private theorem inverseImageModuleStalkHom_isIso_direct (𝒢 : Y.Modules) (x : X) :
    IsIso (inverseImageModuleStalkHom f 𝒢 x) := by
  haveI : IsIso (topUnitModuleStalkHom f 𝒢 x) := topUnitModuleStalkHom_isIso f 𝒢 x
  haveI : IsIso (topToInvStalkBridge f 𝒢 x) := topToInvStalkBridge_isIso f 𝒢 x
  rw [inverseImageModuleStalkHom_eq_topToInvStalkBridge f 𝒢 x]
  infer_instance

/-- Helper for Lemma 6.26.4: the underlying-sheaf comparison `inverseImageModuleUnderlyingPullbackHom`
is an isomorphism once its canonical stalk maps are isomorphisms. -/
private theorem inverseImageModuleUnderlyingPullbackHom_isIso_of_stalk
    (𝒢 : Y.Modules)
    (h : ∀ x : X, IsIso (inverseImageModuleStalkHom f 𝒢 x)) :
    IsIso (inverseImageModuleUnderlyingPullbackHom f 𝒢) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro x
  exact (@_root_.CategoryTheory.IsIso.of_isIso_fac_left AddCommGrpCat _ _ _ _
    (TopCat.Sheaf.stalkPullbackIso f.hom.base
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) x).hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (inverseImageModuleUnderlyingPullbackHom f 𝒢).hom)
    (inverseImageModuleStalkHom f 𝒢 x)
    inferInstance
    (h x)
    (inverseImageModuleUnderlyingPullbackHom_stalk_comp f 𝒢 x))

/-- Helper for Lemma 6.26.4: the underlying-sheaf comparison `inverseImageModuleUnderlyingPullbackHom`
for the inverse-image module is an isomorphism. This is the topological Beck-Chevalley statement that
forming the underlying abelian sheaf commutes with the module pullback. -/
private theorem inverseImageModuleUnderlyingPullbackHom_isIso (𝒢 : Y.Modules) :
    IsIso (inverseImageModuleUnderlyingPullbackHom f 𝒢) := by
  exact inverseImageModuleUnderlyingPullbackHom_isIso_of_stalk f 𝒢
    (fun x => inverseImageModuleStalkHom_isIso_direct f 𝒢 x)

/-- Helper for Lemma 6.26.4: the canonical stalk map from a module to its topological inverse
image is an isomorphism. This is the module-valued analogue of `TopCat.Sheaf.stalkPullbackIso`,
with the module pullback taken along the inverse-image unit. -/
private theorem inverseImageModuleStalkHom_isIso (𝒢 : Y.Modules) (x : X) :
    IsIso (inverseImageModuleStalkHom f 𝒢 x) := by
  haveI : IsIso (inverseImageModuleUnderlyingPullbackHom f 𝒢) :=
    inverseImageModuleUnderlyingPullbackHom_isIso f 𝒢
  rw [← inverseImageModuleUnderlyingPullbackHom_stalk_comp f 𝒢 x]
  exact IsIso.comp_isIso'
    (inferInstance : IsIso (TopCat.Sheaf.stalkPullbackIso f.hom.base
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) x).hom)
    (Functor.map_isIso
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      (inverseImageModuleUnderlyingPullbackHom f 𝒢))

/-- Helper for Lemma 6.26.4: after identifying inverse-image stalks with stalks over `f x`,
the source of the stalkwise base-change isomorphism is the expected extension of scalars. -/
public noncomputable abbrev inverseImagePullbackSourceStalkIso (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars
        (CommRingCat.Hom.hom
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom))).obj
      (ModuleCat.of
        ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
      ↑(TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x)) ≅
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
      (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) := by
  let eR :=
    (TopCat.Sheaf.stalkPullbackIso f.hom.base Y.sheaf x).commRingCatIsoToRingEquiv
  let p : ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x) →+*
      ↑(TopCat.Presheaf.stalk X.presheaf x) :=
    CommRingCat.Hom.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom)
  let q : ↑(TopCat.Presheaf.stalk Y.presheaf (f.hom.base x)) →+*
      ↑(TopCat.Presheaf.stalk X.presheaf x) :=
    (f.hom.stalkMap x).hom
  have hq : q = p.comp eR.toRingHom := by
    have hcat := inverseImageStructureSheafHomComm_stalkMap_eq (f := f) x
    have h := congrArg (fun α ↦ CommRingCat.Hom.hom α) hcat
    simpa [eR, p, q, RingHom.comp_apply] using h.symm
  haveI : IsIso (inverseImageModuleStalkHom f 𝒢 x) := by
    exact inverseImageModuleStalkHom_isIso f 𝒢 x
  let φ₀ :
      ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf (f.hom.base x)) →ₛₗ[eR.toRingHom]
        ↑(TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x) :=
    { toFun := fun m ↦ inverseImageModuleStalkHom f 𝒢 x m
      map_add' := by
        intro m n
        exact (inverseImageModuleStalkHom f 𝒢 x).hom.map_add m n
      map_smul' := by
        intro r m
        exact inverseImageModuleStalkHom_smul f 𝒢 x r m }
  have hbij : Function.Bijective φ₀ := by
    simpa [φ₀] using
      (ConcreteCategory.bijective_of_isIso (inverseImageModuleStalkHom f 𝒢 x))
  letI : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eR
  let φ : @LinearEquiv
      ↑(TopCat.Presheaf.stalk Y.presheaf (f.hom.base x))
      ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
      _ _ eR.toRingHom eR.symm.toRingHom
      (RingHomInvPair.of_ringEquiv eR) (RingHomInvPair.of_ringEquiv_symm eR)
      ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf (f.hom.base x))
      ↑(TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x)
      _ _ _ _ :=
    LinearEquiv.ofBijective φ₀ hbij
  simpa [RingedSpace.stalkModuleCat, eR, p, q] using
    transportedExtendIso eR p q hq φ

/-- Helper for Lemma 6.26.4: the pullback-comparison isomorphism identifies the codomain of the
stalkwise base-change comparison with the final pullback stalk. -/
public noncomputable abbrev pullbackCompStalkIso (𝒢 : Y.Modules) (x : X) :
    ModuleCat.of
      ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
      ↑(TopCat.Presheaf.stalk
        ((SheafOfModules.pullback
            (ringSheafHomOverId
              (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj
          ((inverseImageModule f).obj 𝒢)).val.presheaf x) ≅
    RingedSpace.stalkModuleCat ((f^*).obj 𝒢) x := by
  -- TODO: stalk the `SheafOfModules.pullbackComp` component and then normalize the source from the
  -- functor-composition spelling to `((SheafOfModules.pullback (inverseImageStructureSheafHom f)).obj
  -- ((inverseImageModule f).obj 𝒢))`, and the target to `((f^*).obj 𝒢)`.
  let hcomp := inverseImageRingUnit_comp_inverseImageStructureSheafHom f
  let e :
      ((SheafOfModules.pullback (inverseImageRingUnit f) ⋙
          SheafOfModules.pullback
            (ringSheafHomOverId
              (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj 𝒢) ≅
        ((f^*).obj 𝒢) :=
    ((SheafOfModules.pullbackComp (inverseImageRingUnit f)
        (ringSheafHomOverId
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).app 𝒢) ≪≫
      (eqToIso (congrArg (fun φ ↦ SheafOfModules.pullback φ)
        (by
          simpa [inverseImageStructureSheafHom, RingedSpace.ringCatSheaf,
            inverseImageCommRingSheaf, inverseImageRingSheaf] using
            hcomp))).app 𝒢
  simpa [RingedSpace.stalkModuleCat, RingedSpace.Hom.pullback, inverseImageModule, e,
    RingedSpace.ringCatSheaf] using
    stalkModuleIsoOfIso e x

-- Proof sketch: factor `f^*` as topological inverse image followed by the same-space change of
-- rings `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`; then compose the owner-level stalk isomorphisms
-- `TopCat.Sheaf.stalkPullbackIso` and `sheafOfModules_pullback_stalkIso`, together with the
-- pullback-composition comparison from Lemma 6.26.3.
/-- Lemma 6.26.4: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, an `\mathcal O_Y`-module sheaf `𝒢`, and a point
`x : X`, the stalk of `f^* 𝒢` at `x` is canonically the extension of scalars of the stalk
`𝒢_{f(x)}` along the induced local ring map
`\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}`. -/
noncomputable abbrev pullbackStalkIso (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
      (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) ≅
      RingedSpace.stalkModuleCat ((f^*).obj 𝒢) x := by
  let e₁ :=
    sheafOfModules_pullback_stalkIso
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
      ((inverseImageModule f).obj 𝒢) x
  let e₂ :=
    TopCat.Sheaf.stalkPullbackIso f.hom.base
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) x
  let e₃ := inverseImageStructureSheafHom f
  let e₄ := SheafOfModules.pullbackComp (inverseImageRingUnit f) e₃
  -- First rewrite the source of the stalkwise base-change isomorphism into the standard
  -- extended-scalars presentation along `f.hom.stalkMap x`.
  exact
    (inverseImagePullbackSourceStalkIso f 𝒢 x).symm ≪≫ e₁ ≪≫
      (by
        -- Normalize the same-space change-of-rings spelling used by Lemma 6.20.3 to the
        -- ring-valued morphism used by the pullback-composition comparison.
        refine ?_ ≪≫ pullbackCompStalkIso f 𝒢 x
        exact moduleCatOfIsoOfSMulEq
          ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
          ↑(TopCat.Presheaf.stalk
            ((SheafOfModules.pullback
              (ringSheafHomOverId
                (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj
              ((inverseImageModule f).obj 𝒢)).val.presheaf x)
          (sheafOfModules_pullbackStalkModule
            (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
            ((inverseImageModule f).obj 𝒢) x)
          (ringedSpaceModuleStalkModule_sheaf_obj
            ((SheafOfModules.pullback
              (ringSheafHomOverId
                (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj
              ((inverseImageModule f).obj 𝒢)) x)
          (by
            intro r m
            let N : X.Modules :=
              ((SheafOfModules.pullback
                (ringSheafHomOverId
                  (RingedSpace.Hom.inverseImageStructureSheafHomComm f))).obj
                ((inverseImageModule f).obj 𝒢))
            obtain ⟨U, hxU, rU, rfl⟩ := X.presheaf.germ_exist x r
            obtain ⟨V, hxV, mV, rfl⟩ := TopCat.Presheaf.germ_exist N.val.presheaf x m
            let W : Opens X := U ⊓ V
            let hxW : x ∈ W := ⟨hxU, hxV⟩
            let iWU : W ⟶ U := homOfLE inf_le_left
            let iWV : W ⟶ V := homOfLE inf_le_right
            let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
            let mW : N.val.obj (op W) := N.val.map iWV.op mV
            have hr : X.presheaf.germ W x hxW rW = X.presheaf.germ U x hxU rU := by
              exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res X.presheaf iWU x hxW) rU
            have hm : TopCat.Presheaf.germ N.val.presheaf W x hxW mW =
                TopCat.Presheaf.germ N.val.presheaf V x hxV mV := by
              exact ConcreteCategory.congr_hom
                (TopCat.Presheaf.germ_res N.val.presheaf iWV x hxW) mV
            rw [← hr, ← hm]
            have hleft :
                @SMul.smul
                  ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
                  ↑(TopCat.Presheaf.stalk N.val.presheaf x)
                  (sheafOfModules_pullbackStalkModule
                    (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
                    ((inverseImageModule f).obj 𝒢) x).toSMul
                  (X.presheaf.germ W x hxW rW)
                  (TopCat.Presheaf.germ N.val.presheaf W x hxW mW) =
                TopCat.Presheaf.germ N.val.presheaf W x hxW (rW • mW) := by
              letI :
                  Module ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
                    ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
                sheafOfModules_pullbackStalkModule
                  (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
                  ((inverseImageModule f).obj 𝒢) x
              change
                ((commRingStalkToRingStalkIso x (SheafedSpace.sheaf X)).hom.hom
                    (X.presheaf.germ W x hxW rW)) •
                  TopCat.Presheaf.germ N.val.presheaf W x hxW mW =
                TopCat.Presheaf.germ N.val.presheaf W x hxW (rW • mW)
              change
                ((commRingStalkToRingStalkIso x (SheafedSpace.sheaf X)).hom.hom
                    (TopCat.Presheaf.germ (SheafedSpace.sheaf X).obj W x hxW rW)) •
                  TopCat.Presheaf.germ N.val.presheaf W x hxW mW =
                TopCat.Presheaf.germ N.val.presheaf W x hxW (rW • mW)
              rw [commRingStalkToRingStalkIso_hom_germ_apply x (SheafedSpace.sheaf X) W hxW rW]
              simpa [N, RingedSpace.ringCatSheaf] using
                (PresheafOfModules.germ_ringCat_smul
                  (R := (ringSheafOfComm (SheafedSpace.sheaf X)).obj)
                  (M := N.val) x W hxW rW mW).symm
            have hright :
                @SMul.smul
                  ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
                  ↑(TopCat.Presheaf.stalk N.val.presheaf x)
                  (ringedSpaceModuleStalkModule_sheaf_obj N x).toSMul
                  (X.presheaf.germ W x hxW rW)
                  (TopCat.Presheaf.germ N.val.presheaf W x hxW mW) =
                TopCat.Presheaf.germ N.val.presheaf W x hxW (rW • mW) := by
              letI :
                  Module ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
                    ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
                ringedSpaceModuleStalkModule_sheaf_obj N x
              symm
              simpa [N, RingedSpace.ringCatSheaf] using
                (PresheafOfModules.germ_smul (M := N.val) x W hxW rW mW)
            rw [hleft, hright]))

-- Proof sketch: apply the standard identity law for the isomorphism `pullbackStalkIso f 𝒢 x`.
/-- The canonical stalk pullback isomorphism has inverse equalities as usual for an isomorphism. -/
theorem pullbackStalkIso_hom_inv_id (𝒢 : Y.Modules) (x : X) :
    (pullbackStalkIso f 𝒢 x).hom ≫ (pullbackStalkIso f 𝒢 x).inv =
      𝟙 ((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x))) := by
  -- This is the standard inverse identity for the canonical stalk isomorphism just constructed.
  exact (pullbackStalkIso f 𝒢 x).hom_inv_id

end

end RingedSpace.Hom

end AlgebraicGeometry
