module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

open GrothendieckTopology

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

open CategoryOfElements in
set_option backward.isDefEq.respectTransparency false in
def fromOverFunctorElementsEquivalence'
    (F : C ⥤ Type w) {X : C} (x : F.obj X) :
    (FunctorToTypes.fromOverFunctor F x).Elements ≌ Over (F.elementsMk X x) where
  functor.obj u :=
    Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom
      ((FunctorToTypes.mem_fromOverSubfunctor_iff (F := F) (x := x)
        (U := u.fst) u.snd.1).1 u.snd.2))
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd,
      (FunctorToTypes.mem_fromOverSubfunctor_iff (F := F) (x := x)
        (U := Over.mk u.hom.1) u.left.snd).2 (by simpa using u.hom.2)⟩
  inverse.map f := homMk _ _ (Over.homMk f.left.val (Subtype.ext_iff.1 (Over.w f)))
    (by cat_disch)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    simp_all
    rfl

/- Domain-style sampling for Lemma 7.35.1:
- primary domain: localized points of Grothendieck sites and their induced fiber functors on
  presheaves and sheaves;
- sampled owner API:
  `GrothendieckTopology.Point.over`,
  `FunctorToTypes.fromOverFunctorElementsEquivalence`,
  `Over.initial_forget`,
  `GrothendieckTopology.Point.presheafFiber`;
- best owner abstraction: the localized point owner `p.over x`, whose presheaf and sheaf fibers are
  derived API, together with the canonical equivalence between its category of elements and the
  over-category of `(U, x)` inside `p.fiber.Elements`;
- source/core/bridge triage:
  `source-facing`: the localization identity `(j_U^{-1} ℱ)_{p_x} ≅ ℱ_p`;
  `core/canonical`: `Point.over`, `Point.presheafFiber`, `Point.sheafFiber`, and the finality of
    `Over.forget` on a cofiltered category;
  `bridge/view`: the presheaf-level colimit comparison induced by
    `FunctorToTypes.fromOverFunctorElementsEquivalence` and `Over.initial_forget`.

Primitive data are only the point `p`, the object `U`, and the element `x : p.fiber.obj U`. The
comparison on sheaf fibers is derived from the canonical presheaf-fiber owner and the owner-level
formula `ℱ.over U` for restriction to the slice site, so this file should expose an actual
canonical `Iso` rather than a theorem-level `IsIsomorphic` wrapper.
-/

/-- Presheaf-fiber comparison underlying Lemma 7.35.1. Restricting a presheaf to `C / U` and then
taking the fiber at the localized point `p.over x` computes the same colimit as taking the fiber at
`p`. -/
noncomputable def point_over_overPullback_presheafFiberObjIso
    (p : Point.{w} J) {U : C} (x : p.fiber.obj U) (P : Cᵒᵖ ⥤ Type w) :
    (p.over x).presheafFiber.obj ((Over.forget U).op ⋙ P) ≅ p.presheafFiber.obj P := by
  let e := fromOverFunctorElementsEquivalence' p.fiber x
  let t :=
    (p.presheafFiberCocone P).whisker (Over.forget (p.fiber.elementsMk U x)).op
  have ht : IsColimit t := by
    exact
      (Functor.Final.isColimitWhiskerEquiv (Over.forget (p.fiber.elementsMk U x)).op
        (p.presheafFiberCocone P)).symm
        (p.isColimitPresheafFiberCocone P)
  have ht' : IsColimit (t.whisker e.functor.op) := by
    exact (Functor.Final.isColimitWhiskerEquiv e.functor.op t).symm ht
  let c1 := (p.over x).isColimitPresheafFiberCocone ((Over.forget U).op ⋙ P)
  simpa [e, t, fromOverFunctorElementsEquivalence'] using
    IsColimit.coconePointUniqueUpToIso c1 ht'

@[reassoc]
lemma point_over_overPullback_presheafFiberObjIso_hom_fac
    (p : Point.{w} J) {U : C} (x : p.fiber.obj U) (P : Cᵒᵖ ⥤ Type w)
    (V : Over U) (y : (p.over x).fiber.obj V) :
    (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
      (point_over_overPullback_presheafFiberObjIso p x P).hom =
        p.toPresheafFiber V.left y.1 P := by
  let e := fromOverFunctorElementsEquivalence' p.fiber x
  let t :=
    (p.presheafFiberCocone P).whisker (Over.forget (p.fiber.elementsMk U x)).op
  have ht : IsColimit t := by
    exact
      (Functor.Final.isColimitWhiskerEquiv (Over.forget (p.fiber.elementsMk U x)).op
        (p.presheafFiberCocone P)).symm
        (p.isColimitPresheafFiberCocone P)
  have ht' : IsColimit (t.whisker e.functor.op) := by
    exact (Functor.Final.isColimitWhiskerEquiv e.functor.op t).symm ht
  let c1 := (p.over x).isColimitPresheafFiberCocone ((Over.forget U).op ⋙ P)
  simpa [point_over_overPullback_presheafFiberObjIso, e, t,
    fromOverFunctorElementsEquivalence'] using
    IsColimit.comp_coconePointUniqueUpToIso_hom c1 ht' (op (Functor.elementsMk _ V y))

attribute [simp] point_over_overPullback_presheafFiberObjIso_hom_fac
attribute [simp] point_over_overPullback_presheafFiberObjIso_hom_fac_assoc

/-- Presheaf-fiber comparison underlying Lemma 7.35.1. Restricting a presheaf to `C / U` and then
taking the fiber at the localized point `p.over x` computes the same colimit as taking the fiber at
`p`. -/
noncomputable def point_over_overPullback_presheafFiberIso
    (p : Point.{w} J) {U : C} (x : p.fiber.obj U) :
    (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op ⋙
        (p.over x).presheafFiber ≅
      p.presheafFiber := by
  refine NatIso.ofComponents (fun P ↦ ?_) ?_
  · exact point_over_overPullback_presheafFiberObjIso p x P
  · intro P Q f
    apply (p.over x).presheafFiber_hom_ext
    intro V y
    change
      (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
          (p.over x).presheafFiber.map ((Over.forget U).op.whiskerLeft f) ≫
          (point_over_overPullback_presheafFiberObjIso p x Q).hom =
        (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
          (point_over_overPullback_presheafFiberObjIso p x P).hom ≫
          p.presheafFiber.map f
    repeat rw [← Category.assoc]
    rw [(p.over x).toPresheafFiber_naturality (((Over.forget U).op.whiskerLeft f)) V y]
    rw [Category.assoc]
    rw [point_over_overPullback_presheafFiberObjIso_hom_fac]
    rw [point_over_overPullback_presheafFiberObjIso_hom_fac]
    simpa using (p.toPresheafFiber_naturality f V.left y.1).symm

/-- Lemma 7.35.1 in canonical functor-iso form: restricting a sheaf to the slice site over `U`
and then taking the fiber at the localized point `p.over x` agrees with taking the fiber at `p`. -/
noncomputable def point_over_overPullback_sheafFiberIso
    (p : Point.{w} J) {U : C} (x : p.fiber.obj U) :
    J.overPullback (Type w) U ⋙ (p.over x).sheafFiber ≅ p.sheafFiber := by
  change
    (((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J ⋙
        sheafToPresheaf (J.over U) (Type w)) ⋙
      (p.over x).presheafFiber) ≅
      (sheafToPresheaf J (Type w) ⋙ p.presheafFiber)
  exact
    (Functor.associator
      ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J)
      (sheafToPresheaf (J.over U) (Type w))
      ((p.over x).presheafFiber)) ≪≫
    Functor.isoWhiskerRight
      ((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type w) (J.over U) J)
      ((p.over x).presheafFiber) ≪≫
    (Functor.associator
      (sheafToPresheaf J (Type w))
      ((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op)
      ((p.over x).presheafFiber)).symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type w))
      (point_over_overPullback_presheafFiberIso p x)

/-- Objectwise form of Lemma 7.35.1, stated on the canonical owner `ℱ.over U` for slice-site
restriction. -/
noncomputable def point_over_sheafFiberObjIso
    (p : Point.{w} J) {U : C} (x : p.fiber.obj U) (ℱ : Sheaf J (Type w)) :
    (p.over x).sheafFiber.obj (ℱ.over U) ≅ p.sheafFiber.obj ℱ := by
  simpa [Sheaf.over, GrothendieckTopology.overPullback] using
    (point_over_overPullback_sheafFiberIso p x).app ℱ

end

end

end CategoryTheory
