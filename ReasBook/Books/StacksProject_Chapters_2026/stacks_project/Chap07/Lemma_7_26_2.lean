module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CartesianClosed

universe u v

attribute [local instance 2000] CategoryTheory.FunctorToTypes.monoidalClosed

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 7.26.2:
- primary domain: cartesian closed structure on sheaves of types and the source-facing sheaf-Hom;
- sampled owner declarations:
  `CategoryTheory.sheafHom`,
  `CategoryTheory.sheafHom'Iso`,
  `CategoryTheory.Functor.functorHom`,
  `CategoryTheory.fullyFaithfulSheafToPresheaf`,
  `(ihom.adjunction G).homEquiv`;
- source-facing layer: the Stacks-project sheaf-Hom currying bijection
  `((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H)`;
- core/canonical owner: the cartesian-closed internal Hom `G ⟹ H` in `Sheaf J (Type (max u v))`;
- bridge/view: the canonical presheaf bridge
  `presheafHomIsoFunctorHom : presheafHom F G ≅ F.functorHom G` and its sheaf-level transport
  `ihomIsoSheafHom : G ⟹ H ≅ sheafHom G H`.

Primitive data are only the sheaves `F`, `G`, and `H`. The source and target variance maps on the
right-hand side are derived by transporting the canonical owner maps `pre` and `(ihom G).map`
across `ihomIsoSheafHom`, so they should not remain separate public owner-level definitions.
At the presheaf level, the objectwise bridge `presheafHom F G (X) ≃ (F.functorHom G)(X)` is only
internal proof machinery for this owner-level comparison, not a second local API layer.
-/

/-- The localized Hom presheaf `presheafHom F G` is canonically the functor-category internal Hom
proxy `F.functorHom G`. -/
def presheafHomIsoFunctorHom (F G : Cᵒᵖ ⥤ Type (max u v)) :
    presheafHom F G ≅ F.functorHom G :=
  NatIso.ofComponents
    (fun X ↦
      (show (presheafHom F G).obj X ≃ (F.functorHom G).obj X from
        { toFun := fun α ↦
            { app := fun Y f ↦ α.app (op (Over.mk f.unop))
              naturality := by
                intro Y Z g f
                simpa using
                  α.naturality
                    (Over.homMk g.unop : Over.mk ((f ≫ g).unop) ⟶ Over.mk f.unop).op }
          invFun := fun α ↦
            { app := fun ⟨Y⟩ ↦ α.app (op Y.left) Y.hom.op
              naturality := by
                rintro ⟨Y⟩ ⟨Z⟩ ⟨g⟩
                dsimp
                have hfg : Y.hom.op ≫ g.left.op = Z.hom.op := by
                  simpa using congrArg Quiver.Hom.op (Over.w g)
                erw [← hfg]
                exact α.naturality g.left.op Y.hom.op }
          left_inv := fun _ ↦ rfl
          right_inv := fun α ↦ by
            ext Y f
            rfl }).toIso)
    fun {X} {Y} f ↦ by
      ext α Z g
      rfl

/-- For sheaves of types, the exponential object in `Sheaf J (Type (max u v))` is canonically the
sheaf `sheafHom G H` of localized morphisms. -/
def ihomIsoSheafHom (G H : Sheaf J (Type (max u v))) : G ⟹ H ≅ sheafHom G H :=
  (fullyFaithfulSheafToPresheaf J (Type (max u v))).preimageIso
    ((presheafHomIsoFunctorHom G.obj H.obj).symm ≪≫ (sheafHom'Iso G H).symm)

/-- Lemma 7.26.2: for sheaves of types on a site `(C, J)`, morphisms `F × G ⟶ H` are in
canonical bijection with morphisms `F ⟶ sheafHom G H`. This is the Stacks Project sheaf-Hom form
of currying. -/
def sheaf_prod_sheafHom_equiv (F G H : Sheaf J (Type (max u v))) :
    ((F ⨯ G) ⟶ H) ≃ (F ⟶ sheafHom G H) :=
  (((prod.braiding F G).homCongr (Iso.refl H)).trans
      ((((tensorLeftIsoProd G).app F).symm.homCongr (Iso.refl H)).trans
        ((ihom.adjunction G).homEquiv F H))).trans
    ((Iso.refl F).homCongr (ihomIsoSheafHom G H))

-- Proof sketch: this is the standard `Equiv.apply_symm_apply` identity for the currying
-- equivalence above.
/-- The inverse of `sheaf_prod_sheafHom_equiv` sends a sheaf-Hom morphism back to the unique
product morphism whose curry is that morphism. -/
theorem sheaf_prod_sheafHom_equiv_apply_symm_apply
    (F G H : Sheaf J (Type (max u v))) (f : F ⟶ sheafHom G H) :
    sheaf_prod_sheafHom_equiv F G H ((sheaf_prod_sheafHom_equiv F G H).symm f) = f := by
  -- This is the left inverse law of the already-constructed currying equivalence.
  exact (sheaf_prod_sheafHom_equiv F G H).apply_symm_apply f

-- Proof sketch: this is the standard `Equiv.symm_apply_apply` identity for the currying
-- equivalence above.
/-- Currying and then uncurrying via `sheaf_prod_sheafHom_equiv` recovers the original morphism
`F × G ⟶ H`. -/
theorem sheaf_prod_sheafHom_equiv_symm_apply_apply
    (F G H : Sheaf J (Type (max u v))) (f : (F ⨯ G) ⟶ H) :
    (sheaf_prod_sheafHom_equiv F G H).symm (sheaf_prod_sheafHom_equiv F G H f) = f := by
  -- This is the right inverse law of the same currying equivalence.
  exact (sheaf_prod_sheafHom_equiv F G H).symm_apply_apply f

end
