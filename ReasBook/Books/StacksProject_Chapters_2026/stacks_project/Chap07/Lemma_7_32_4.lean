module

public import stacks_project.Chap07.«7_32_1_1»
public import stacks_project.Chap07.«7_32_3_1»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Functor
open scoped PresheafCostalk

/-- The value of `u^p E` at `X` is the set of maps from `u.obj X` to `E`. -/
theorem presheafCostalk_obj_obj (u : C ⥤ Type w) (E : Type w) (X : C) :
    ((u^p).obj E).obj (op X) = (u.obj X → E) :=
  rfl

section

variable (u : C ⥤ Type w)
variable [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]

/-- The hom-set bijection underlying the adjunction between the presheaf fiber functor of `u` and
the costalk functor `u^p`. -/
noncomputable def presheafCostalkHomEquiv (F : Cᵒᵖ ⥤ Type w) (E : Type w) :
    (u.presheafFiber.obj F ⟶ E) ≃ (F ⟶ (u^p).obj E) where
  toFun f :=
    { app := fun X s x ↦ f (u.toPresheafFiber X.unop x F s)
      naturality := by
        intro X Y g
        ext s
        funext x
        have h : u.toPresheafFiber Y.unop x F ((F.map g) s) =
            u.toPresheafFiber X.unop (u.map g.unop x) F s := by
          simpa using congr_fun (u.toPresheafFiber_w g.unop x) s
        exact congrArg f h }
  invFun g :=
    u.presheafFiberDesc
      (fun X x s ↦ g.app (op X) s x)
      (fun {Y Z} α y ↦ by
        ext s
        exact congr_fun (congr_fun (g.naturality α.op) s) y)
  left_inv f := by
    apply u.presheafFiber_hom_ext
    intro X x
    change u.toPresheafFiber X x F ≫
        u.presheafFiberDesc (fun X x s ↦ f (u.toPresheafFiber X x F s))
          (fun {Y Z} α y ↦ by
            ext s
            exact congrArg f (congr_fun (u.toPresheafFiber_w α y) s)) =
      u.toPresheafFiber X x F ≫ f
    exact u.toPresheafFiber_presheafFiberDesc _ _ X x
  right_inv g := by
    ext X s
    funext x
    change (u.toPresheafFiber X.unop x F ≫
        u.presheafFiberDesc (fun X x s ↦ g.app (op X) s x)
          (fun {Y Z} α y ↦ by
            ext s
            exact congr_fun (congr_fun (g.naturality α.op) s) y)) s = _
    simpa using congr_fun (u.toPresheafFiber_presheafFiberDesc _ _ X.unop x) s

/-- Evaluating the inverse hom-equivalence on a generator of the presheaf fiber recovers the
corresponding component of the given presheaf map. -/
private lemma toPresheafFiber_presheafCostalkHomEquiv_symm {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (g : F ⟶ (u^p).obj E) (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ (presheafCostalkHomEquiv u F E).symm g =
      fun s ↦ g.app (op X) s x := by
  change u.toPresheafFiber X x F ≫
      u.presheafFiberDesc (fun X x s ↦ g.app (op X) s x)
        (fun {Y Z} α y ↦ by
          ext s
          exact congr_fun (congr_fun (g.naturality α.op) s) y) = _
  exact u.toPresheafFiber_presheafFiberDesc _ _ X x

/-- Naturality on the presheaf argument for the inverse of the hom-equivalence defining the
adjunction `presheafFiber u ⊣ u^p`. -/
lemma presheafCostalkHomEquiv_naturality_left_symm {F G : Cᵒᵖ ⥤ Type w} {E : Type w}
    (f : F ⟶ G) (g : G ⟶ (u^p).obj E) :
    (presheafCostalkHomEquiv u F E).symm (f ≫ g) =
      u.presheafFiber.map f ≫ (presheafCostalkHomEquiv u G E).symm g := by
  apply u.presheafFiber_hom_ext
  intro X x
  rw [← Category.assoc, u.toPresheafFiber_naturality]
  ext s
  have h₁ := congr_fun
    (toPresheafFiber_presheafCostalkHomEquiv_symm u (f ≫ g) X x) s
  have h₂ := congr_fun
    (toPresheafFiber_presheafCostalkHomEquiv_symm u g X x)
    (f.app (op X) s)
  simpa [NatTrans.comp_app] using h₁.trans h₂.symm

/-- Naturality on the target set for the hom-equivalence defining `presheafFiber u ⊣ u^p`. -/
lemma presheafCostalkHomEquiv_naturality_right {F : Cᵒᵖ ⥤ Type w} {E E' : Type w}
    (f : u.presheafFiber.obj F ⟶ E) (g : E ⟶ E') :
    presheafCostalkHomEquiv u F E' (f ≫ g) =
      presheafCostalkHomEquiv u F E f ≫ (u^p).map g := by
  ext X s
  funext x
  rfl

/-- Lemma 7.32.4: for any functor `u : C ⥤ Type`, the costalk functor `u^p` is right adjoint to
the presheaf fiber functor of `u`. -/
noncomputable def presheafCostalkAdjunction :
    u.presheafFiber ⊣ u^p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := presheafCostalkHomEquiv u
      homEquiv_naturality_left_symm := presheafCostalkHomEquiv_naturality_left_symm u
      homEquiv_naturality_right := presheafCostalkHomEquiv_naturality_right u }

/-- The adjunction `presheafCostalkAdjunction u` induces the expected bijection on Hom-sets. -/
-- Proof sketch: use the generic fact that the Hom-equivalence of any adjunction is bijective.
theorem presheafCostalkAdjunction_homEquiv_bijective (F : Cᵒᵖ ⥤ Type w) (E : Type w) :
    Function.Bijective ((presheafCostalkAdjunction u).homEquiv F E) := by
  -- The adjunction already packages the source proof as an equivalence of Hom-sets.
  exact ((presheafCostalkAdjunction u).homEquiv F E).bijective

/-- Lemma 7.32.4 in `IsRightAdjoint` form: once the presheaf fiber of `u` is available as the
canonical colimit over `u.Elementsᵒᵖ`, the functor `u^p` is a right adjoint. -/
instance presheafCostalk_isRightAdjoint :
    (u^p).IsRightAdjoint :=
  (presheafCostalkAdjunction u).isRightAdjoint

end

end CategoryTheory
