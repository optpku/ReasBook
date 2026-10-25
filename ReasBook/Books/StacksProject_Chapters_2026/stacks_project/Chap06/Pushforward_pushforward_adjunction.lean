module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous


@[expose] public section

/-!
# Pushforward–pushforward adjunction for presheaves of modules

This is the presheaf-of-modules analogue of `SheafOfModules.pushforwardPushforwardAdj`
(`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`).  Given an adjunction
`adj : F ⊣ G` between the index categories together with compatible morphisms of presheaves of
rings `φ : S ⟶ F.op ⋙ R` and `ψ : R ⟶ G.op ⋙ S`, the pushforward functors along `φ` and `ψ`
are themselves adjoint.

This is used in `Lemma_6_31_8` to identify the explicit concrete restriction owner
(`pushforward` along the open-map pullback comparison) with the canonical `pullback` owner along
the open-embedding adjunction unit, by the uniqueness of left adjoints.
-/

open CategoryTheory

universe v v₁ v₂ u₁ u₂ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Congr

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- Pushforward along equal morphisms of presheaves of rings gives isomorphic functors.  As in the
sheaf case, this is built so that on underlying sections it is the identity. -/
noncomputable def pushforwardCongr {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
    (fun X ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
    (fun _ _ _ ↦ by subst e; rfl)) (fun _ ↦ by subst e; rfl)

@[simp] lemma pushforwardCongr_hom_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) (M X x) :
    (((pushforwardCongr e).hom.app M).app X).hom x = x := rfl

@[simp] lemma pushforwardCongr_inv_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) (M X x) :
    (((pushforwardCongr e).inv.app M).app X).hom x = x := rfl

end Congr

section NatTrans

variable {F G : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
  (φ : S ⟶ G.op ⋙ R)

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation `α : F ⟶ G` gives a natural transformation between the pushforward
functors `pushforward φ ⟶ pushforward (φ ≫ Functor.whiskerRight (NatTrans.op α) R)`. -/
noncomputable def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶ pushforward.{v} (φ ≫ Functor.whiskerRight (NatTrans.op α) R) where
  app M :=
    { app X := (ModuleCat.restrictScalars (φ.app X).hom).map (M.map (α.app X.unop).op)
      naturality := fun {X Y} i => by
        ext x
        change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app Y.unop).op) _ =
          (M.presheaf.map (α.app X.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
        simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext X x
    exact (congr($((f.naturality (α.app X.unop).op)) x)).symm

lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M) (X) (x) :
    (((pushforwardNatTrans φ α).app M).app X).hom x = M.map (α.app X.unop).op x := rfl

end NatTrans

section Adjunction

variable {F : C ⥤ D} {G : D ⥤ C}
  {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G)
  (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- If `F ⊣ G`, then the pushforwards along compatible ring morphisms `φ`, `ψ` are also adjoint. -/
noncomputable def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components M := by
    ext X x
    change (M.presheaf.map (adj.counit.app (F.obj X.unop)).op ≫
      M.presheaf.map (F.map (adj.unit.app X.unop)).op) _ = _
    rw [← CategoryTheory.Functor.map_comp, ← op_comp]
    simp [adj.left_triangle_components]
  right_triangle_components M := by
    ext X x
    change (M.presheaf.map (G.map (adj.counit.app X.unop)).op ≫
      M.presheaf.map (adj.unit.app (G.obj X.unop)).op) _ = _
    rw [← CategoryTheory.Functor.map_comp, ← op_comp]
    simp [adj.right_triangle_components]

lemma pushforwardPushforwardAdj_unit_app_app_apply (M) (X) (x) :
    (((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app X).hom x =
      M.map (adj.counit.app X.unop).op x := rfl

lemma pushforwardPushforwardAdj_counit_app_app_apply (M) (X) (x) :
    (((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).app X).hom x =
      M.map (adj.unit.app X.unop).op x := rfl

end Adjunction

end PresheafOfModules
