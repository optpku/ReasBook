module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.Ring.Basic
public import stacks_project.Chap06.Definition_6_30_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

variable {X : Type u} [TopologicalSpace X]

/-- A presheaf of modules on the basis `B` over the basis ring-valued presheaf `𝒪`. -/
abbrev BasisPresheafOfModules {B : Set (Opens X)} (𝒪 : (BasisOpen B)ᵒᵖ ⥤ RingCat.{u}) :=
  PresheafOfModules 𝒪

variable {B : Set (Opens X)}

/-- Transition to presheaves of modules on a basis: products of basis presheaves of modules are
computed objectwise on basis opens. -/
noncomputable abbrev basisPresheafOfModulesProductObjIso
    (𝒪 : (BasisOpen B)ᵒᵖ ⥤ RingCat.{u}) {ι : Type v} (F : ι → BasisPresheafOfModules 𝒪)
    (U : BasisOpen B) :
    (∏ᶜ F).obj (op U) ≅ ∏ᶜ fun i ↦ (F i).obj (op U) :=
  PreservesProduct.iso (PresheafOfModules.evaluation 𝒪 (op U)) F

-- Proof sketch: `PresheafOfModules.evaluation 𝒪 (op U)` preserves products, so the comparison map
-- from the evaluation of the product to the product of the evaluations is exactly the product
-- comparison morphism for this evaluation functor.
/-- The objectwise product comparison over a basis open identifies the product projections after
evaluation with the projections of the product of modules. -/
theorem basisPresheafOfModulesProductObjIso_hom_comp_π
    (𝒪 : (BasisOpen B)ᵒᵖ ⥤ RingCat.{u}) {ι : Type v} (F : ι → BasisPresheafOfModules 𝒪)
    (U : BasisOpen B) (i : ι) :
    (basisPresheafOfModulesProductObjIso 𝒪 F U).hom ≫
        Pi.π (fun j ↦ (F j).obj (op U)) i =
      (Pi.π F i).app (op U) := by
  -- The basis-open product comparison is the standard `piComparison` for evaluation at `U`.
  simpa [basisPresheafOfModulesProductObjIso, PreservesProduct.iso_hom] using
    (piComparison_comp_π (PresheafOfModules.evaluation 𝒪 (op U)) F i)
