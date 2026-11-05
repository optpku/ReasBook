module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite CategoryOfElements

universe u v w

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C]
variable (u : C ⥤ Type w)
variable [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]

/- Domain-style sampling for 7.32.1.1:
- primary domain: set-valued presheaf fibers presented as colimits over categories of elements;
- sampled canonical declarations in the same domain:
  `Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.toPresheafFiber`,
  `GrothendieckTopology.Point.presheafFiberDesc`;
- source/core/bridge triage:
  `source-facing`: the fiber functor `u.presheafFiber` for an arbitrary set-valued functor
  `u : C ⥤ Type w`;
  `core/canonical`: the colimit of `((CategoryOfElements.π u).op ⋙ F)` and the generic Yoneda
  comparison API for categories of elements in mathlib;
  `bridge/view`: the generator maps `toPresheafFiber` and the descent constructor
  `presheafFiberDesc`.

Primitive data are only the colimit cocone over `u.Elementsᵒᵖ`. The generator maps, the ext lemma,
and the descent constructor are derived API. This file therefore keeps `Functor.presheafFiber` as
the owner and exposes only the derived surface actually used downstream, instead of carrying
parallel public cocone wrappers with no later role in the chapter.
-/

/-- 7.32.1.1: for a set-valued functor `u : C ⥤ Type w`, the stalk/fiber functor is obtained by
taking, for each presheaf `F`, the colimit of the values `F.obj (op U)` over the opposite of the
category of pairs `(U, x)` with `x : u.obj U`. -/
noncomputable abbrev presheafFiber (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    (Cᵒᵖ ⥤ Type w) ⥤ Type w :=
  (whiskeringLeft _ _ _).obj (π u).op ⋙ colim

/-- The canonical map from a section of `F` over `X` to the `u`-fiber of `F` represented by
`x : u.obj X`. -/
noncomputable abbrev toPresheafFiber (X : C) (x : u.obj X) (F : Cᵒᵖ ⥤ Type w) :
    F.obj (op X) ⟶ u.presheafFiber.obj F :=
  colimit.ι ((π u).op ⋙ F) (op (u.elementsMk X x))

/-- Two maps out of `u.presheafFiber.obj F` agree as soon as they agree on all generators coming
from sections `F.obj (op X)` indexed by `x : u.obj X`. -/
@[ext]
lemma presheafFiber_hom_ext {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    {f g : u.presheafFiber.obj F ⟶ E}
    (h : ∀ (X : C) (x : u.obj X),
      u.toPresheafFiber X x F ≫ f = u.toPresheafFiber X x F ≫ g) :
    f = g := by
  exact colimit.hom_ext (by rintro ⟨⟨X, x⟩⟩; exact h X x)

/-- The generators of `u.presheafFiber.obj F` are compatible with restriction in the presheaf
argument. -/
@[elementwise, simp, reassoc]
lemma toPresheafFiber_w
    {F : Cᵒᵖ ⥤ Type w} {X Y : C} (f : X ⟶ Y) (x : u.obj X) :
    F.map f.op ≫ u.toPresheafFiber X x F =
      u.toPresheafFiber Y (u.map f x) F :=
  colimit.w ((π u).op ⋙ F)
    (CategoryOfElements.homMk (u.elementsMk X x) (u.elementsMk Y (u.map f x)) f rfl).op

/-- The canonical generators are natural in the presheaf argument. -/
@[elementwise, simp, reassoc]
  lemma toPresheafFiber_naturality
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ u.presheafFiber.map f =
      f.app (op X) ≫ u.toPresheafFiber X x G := by
  simpa [presheafFiber, toPresheafFiber] using
    (ι_colimMap ((π u).op.whiskerLeft f) (op (u.elementsMk X x)))

section

variable {F : Cᵒᵖ ⥤ Type w} {E : Type w}
/-- Descend a compatible family of maps indexed by the elements of `u` to a map out of the
presheaf fiber. -/
noncomputable def presheafFiberDesc
    (φ : ∀ (X : C) (_ : u.obj X), F.obj (op X) ⟶ E)
    (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : u.obj X), F.map f.op ≫ φ X x = φ Y (u.map f x) := by
      cat_disch) :
    u.presheafFiber.obj F ⟶ E :=
  colimit.desc ((π u).op ⋙ F) <|
    Cocone.mk E
      { app := fun j ↦ φ j.unop.1 j.unop.2
        naturality := by
          intro i j g
          simpa using hφ g.unop.1 j.unop.2 }

/-- Evaluating `presheafFiberDesc` on a generator recovers the corresponding component map. -/
@[simp, reassoc]
lemma toPresheafFiber_presheafFiberDesc
    (φ : ∀ (X : C) (_ : u.obj X), F.obj (op X) ⟶ E)
    (hφ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : u.obj X), F.map f.op ≫ φ X x = φ Y (u.map f x))
    (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ u.presheafFiberDesc φ hφ = φ X x :=
  colimit.ι_desc _ _

end

end Functor

namespace NatTrans

open Functor

variable {C : Type u} [Category.{v} C]
variable {u v : C ⥤ Type w}
variable [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
variable [HasColimitsOfShape v.Elementsᵒᵖ (Type w)]

attribute [local simp] FunctorToTypes.naturality

omit [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] in
/-- Compatibility of the canonical generators with the map induced by a natural transformation of
set-valued functors. -/
private lemma toPresheafFiber_w_app (η : u ⟶ v)
    {F : Cᵒᵖ ⥤ Type w} {X Y : C} (f : X ⟶ Y) (x : u.obj X) :
    F.map f.op ≫ v.toPresheafFiber X (η.app X x) F =
      v.toPresheafFiber Y (η.app Y (u.map f x)) F := by
  simpa using (v.toPresheafFiber_w f (η.app X x) :
    F.map f.op ≫ v.toPresheafFiber X (η.app X x) F =
      v.toPresheafFiber Y (v.map f (η.app X x)) F)

/-- A natural transformation of set-valued functors induces the canonical map on their
presheaf-fiber functors. -/
noncomputable def presheafFiber (η : u ⟶ v) :
    u.presheafFiber ⟶ v.presheafFiber where
  app F := u.presheafFiberDesc
    (fun X x ↦ v.toPresheafFiber X (η.app X x) F)
    (by
      intro X Y f x
      exact toPresheafFiber_w_app η f x)
  naturality := by
    intro F G f
    have hG :
      ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (x : u.obj X),
          G.map g.op ≫ v.toPresheafFiber X (η.app X x) G =
            v.toPresheafFiber Y (η.app Y (u.map g x)) G := by
      intro X Y g x
      exact toPresheafFiber_w_app η g x
    have hF :
      ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (x : u.obj X),
          F.map g.op ≫ v.toPresheafFiber X (η.app X x) F =
            v.toPresheafFiber Y (η.app Y (u.map g x)) F := by
      intro X Y g x
      exact toPresheafFiber_w_app η g x
    apply u.presheafFiber_hom_ext
    intro X x
    calc
      u.toPresheafFiber X x F ≫ u.presheafFiber.map f ≫
          u.presheafFiberDesc
            (fun X x ↦ v.toPresheafFiber X (η.app X x) G)
            hG
          = f.app (op X) ≫
              (u.toPresheafFiber X x G ≫
                u.presheafFiberDesc
                  (fun X x ↦ v.toPresheafFiber X (η.app X x) G)
                  hG) := by
              rw [← Category.assoc, u.toPresheafFiber_naturality, Category.assoc]
      _ = f.app (op X) ≫ v.toPresheafFiber X (η.app X x) G := by
            rw [u.toPresheafFiber_presheafFiberDesc _ hG]
      _ = v.toPresheafFiber X (η.app X x) F ≫ v.presheafFiber.map f := by
            simpa using (v.toPresheafFiber_naturality f X (η.app X x)).symm
      _ = u.toPresheafFiber X x F ≫
            u.presheafFiberDesc
              (fun X x ↦ v.toPresheafFiber X (η.app X x) F)
              hF ≫
            v.presheafFiber.map f := by
              simpa using
                (u.toPresheafFiber_presheafFiberDesc_assoc
                  (fun X x ↦ v.toPresheafFiber X (η.app X x) F) hF X x
                  (v.presheafFiber.map f)).symm

@[simp, reassoc]
lemma toPresheafFiber_presheafFiber_app
    (η : u ⟶ v) {F : Cᵒᵖ ⥤ Type w} (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ η.presheafFiber.app F =
      v.toPresheafFiber X (η.app X x) F := by
  have hF :
      ∀ ⦃Y Z : C⦄ (f : Y ⟶ Z) (y : u.obj Y),
        F.map f.op ≫ v.toPresheafFiber Y (η.app Y y) F =
          v.toPresheafFiber Z (η.app Z (u.map f y)) F := by
    intro Y Z f y
    exact toPresheafFiber_w_app η f y
  simpa [NatTrans.presheafFiber] using
    u.toPresheafFiber_presheafFiberDesc
      (fun X x ↦ v.toPresheafFiber X (η.app X x) F) hF X x

end NatTrans

end CategoryTheory
