module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Adjunction
open MonoidalCategory
open Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: internal Homs in a monoidal category, viewed in the source orientation
  `Mor(W, hom(X, Y)) ≃ Mor(W ⊗ X, Y)`.
- Core/canonical declarations inspected:
  - `tensoringRight`
  - `ParametrizedAdjunction`
  - `ParametrizedAdjunction.homEquiv`
  - `Adjunction.rightAdjointUniq`
- Owner abstraction: a source-facing internal-Hom structure is a bifunctor
  `hom : Cᵒᵖ ⥤ C ⥤ C` equipped with a parametrized adjunction `tensoringRight C ⊣₂ hom`.
- Layer triage:
  - `source-facing`: `tensoringRight C ⊣₂ hom`, which is exactly the right-tensor adjunction
    `Mor(W, hom(X, Y)) ≃ Mor(W ⊗ X, Y)`;
  - `core/canonical`: `ParametrizedAdjunction` and its Hom-set bijection `homEquiv`;
  - `bridge/view`: pointwise uniqueness is supplied by `Adjunction.rightAdjointUniq`; in braided
    settings, the left-oriented mathlib owner
    `MonoidalClosed.internalHomAdjunction₂` can be transported to this source orientation, but
    that bridge is companion-only and must not replace the source-facing owner.
- Primitive vs. derived:
  - primitive data: the bifunctor `hom` and the parametrized adjunction `adj₂ : tensoringRight C ⊣₂ hom`;
  - derived API: the uniqueness isomorphism and the transposed composition/left-tensor/right-tensor
    maps below; the evaluation and coevaluation morphisms are used directly from the owner adjunction
    as `(adj₂.adj X).counit.app Y` and `(adj₂.adj X).unit.app Y`.
-/

namespace ParametrizedAdjunction

variable {hom : Cᵒᵖ ⥤ C ⥤ C}

set_option linter.unusedVariables false in
set_option quotPrecheck false in
notation X " ⟶[" hom "] " Y:10 => (hom.obj (op X)).obj Y

/- Remark 4.43.12: an internal Hom in the source sense is a bifunctor `hom` together with a
parametrized adjunction `tensoringRight C ⊣₂ hom`, whose defining bijection is
`adj₂.homEquiv : (W ⊗ X ⟶ Y) ≃ (W ⟶ X ⟶[hom] Y)`. The following maps are the
canonical constructions carried by that owner abstraction. -/

variable {hom' : Cᵒᵖ ⥤ C ⥤ C}

/-- Remark 4.43.12: if `hom` and `hom'` both realize the source-facing internal-Hom adjunction
`tensoringRight C ⊣₂ -`, then they are canonically naturally isomorphic. This is the Yoneda-style
uniqueness statement that the bifunctor `hom` is determined up to unique isomorphism by the
bijections `Mor(W ⊗ X, Y) ≃ Mor(W, hom(X, Y))`, obtained by applying
`Adjunction.rightAdjointUniq` pointwise in `X`. -/
noncomputable def rightAdjointUniq
    (adj₂ : tensoringRight C ⊣₂ hom) (adj₂' : tensoringRight C ⊣₂ hom') :
    hom ≅ hom' :=
  let e (X : Cᵒᵖ) : hom.obj X ≅ hom'.obj X :=
    (adj₂.adj (unop X)).rightAdjointUniq (adj₂'.adj (unop X))
  NatIso.ofComponents
    (fun X ↦ e X)
    (fun {X Y} f ↦ by
      ext Z
      apply ((adj₂'.adj (unop Y)).homEquiv _ _).symm.injective
      simp only [NatTrans.comp_app]
      rw [(adj₂'.adj (unop Y)).homEquiv_naturality_left_symm]
      have hright :
          ((adj₂'.adj (unop Y)).homEquiv ((hom.obj X).obj Z) Z).symm
              ((e X).hom.app Z ≫ (hom'.map f).app Z) =
            ((tensoringRight C).map f.unop).app ((hom.obj X).obj Z) ≫
              ((adj₂'.adj (unop X)).homEquiv ((hom.obj X).obj Z) Z).symm
                ((e X).hom.app Z) := by
        simpa [e] using
          (adj₂'.homEquiv_symm_naturality_one f.unop ((e X).hom.app Z))
      rw [hright]
      rw [homEquiv_symm_rightAdjointUniq_hom_app, homEquiv_symm_rightAdjointUniq_hom_app]
      simpa [e] using (NatTrans.congr_app (adj₂.whiskerLeft_map_counit f.unop) Z).symm)

/-- The component of `rightAdjointUniq adj₂ adj₂'` at `X` is the usual pointwise right-adjoint
uniqueness morphism for the adjunctions obtained by fixing `X`. -/
-- Proof sketch: unfold `rightAdjointUniq`; it was defined by `NatIso.ofComponents` using the
-- pointwise isomorphisms `(adj₂.adj (unop X)).rightAdjointUniq (adj₂'.adj (unop X))`.
theorem rightAdjointUniq_hom_app
    (adj₂ : tensoringRight C ⊣₂ hom) (adj₂' : tensoringRight C ⊣₂ hom') (X : Cᵒᵖ) :
    (rightAdjointUniq adj₂ adj₂').hom.app X =
      ((adj₂.adj (unop X)).rightAdjointUniq (adj₂'.adj (unop X))).hom := by
  -- Unfold the parametrized uniqueness isomorphism to expose its `NatIso.ofComponents` definition.
  delta rightAdjointUniq
  -- The `X`-component is definitionally the pointwise `Adjunction.rightAdjointUniq` morphism.
  rfl

variable (adj₂ : tensoringRight C ⊣₂ hom)

/-- The composition morphism `hom(Y, Z) ⊗ hom(X, Y) ⟶ hom(X, Z)` obtained by transposing the
obvious double-evaluation composite. -/
abbrev comp (X Y Z : C) :
    ((Y ⟶[hom] Z) ⊗ (X ⟶[hom] Y)) ⟶ (X ⟶[hom] Z) :=
  adj₂.homEquiv
    ((α_ (Y ⟶[hom] Z) (X ⟶[hom] Y) X).hom ≫
      ((Y ⟶[hom] Z) ◁ (adj₂.adj X).counit.app Y) ≫
      (adj₂.adj Y).counit.app Z)

/-- For every `Z`, tensoring on the left induces a canonical morphism
`Z ⊗ hom(X, Y) ⟶ hom(X, Z ⊗ Y)`. -/
abbrev tensorLeft (X Y Z : C) :
    (Z ⊗ (X ⟶[hom] Y)) ⟶ (X ⟶[hom] (Z ⊗ Y)) :=
  adj₂.homEquiv
    ((α_ Z (X ⟶[hom] Y) X).hom ≫
      (Z ◁ (adj₂.adj X).counit.app Y))

section Braided

variable [BraidedCategory C]

/-- In a braided monoidal category there is also a canonical morphism
`hom(Y, Z) ⊗ X ⟶ hom(hom(X, Y), Z)`, obtained by using the braiding to feed `X` into the
evaluation map `hom(X, Y) ⊗ X ⟶ Y`. -/
abbrev braidedTensorRight (X Y Z : C) :
    (((Y ⟶[hom] Z) ⊗ X) ⟶ ((X ⟶[hom] Y) ⟶[hom] Z)) :=
  adj₂.homEquiv
    ((α_ (Y ⟶[hom] Z) X (X ⟶[hom] Y)).hom ≫
      ((Y ⟶[hom] Z) ◁ (β_ X (X ⟶[hom] Y)).hom) ≫
      ((Y ⟶[hom] Z) ◁ (adj₂.adj X).counit.app Y) ≫
      (adj₂.adj Y).counit.app Z)

end Braided

end ParametrizedAdjunction

end CategoryTheory
