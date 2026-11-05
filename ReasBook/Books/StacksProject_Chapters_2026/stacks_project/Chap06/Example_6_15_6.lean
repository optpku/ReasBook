module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import stacks_project.Chap06.Definition_6_15_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w v u uC

variable {C : Type v} [Category.{uC} C] {X : TopCat.{u}}

/-
Domain-style sampling for Example 6.15.6:
- primary domain: presheaves on `X` built from categorical products in `C`, together with the
  canonical comparison between sheaf conditions before and after composing with a forgetful functor
  to types;
- inspected owner declarations:
  `TopCat.presheafToTypes`,
  `TopCat.Presheaf.toTypes_isSheaf`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`,
  `CategoryTheory.Limits.Pi.map'`;
- owner abstraction:
  the source-facing owner in this file is the `C`-valued presheaf itself, while its underlying
  `Type`-valued comparison should be expressed through the canonical dependent-function presheaf
  `TopCat.presheafToTypes`;
- primitive-vs-derived split:
  primitive data are the product objects `∏ᶜ fun x : U.unop ↦ Aₓ x.1`;
  the restriction maps are derived from the canonical product reindexing morphism `Pi.map'`,
  and the sheaf statement is derived by comparing with the underlying `Type`-valued presheaf;
  the owner itself only needs `[HasProducts.{u} C]`, while the bridge theorem only needs
  `[HasLimitsOfSize.{u, u} C]`, `[PreservesLimitsOfSize.{u, u} F]`, and
  `[F.ReflectsIsomorphisms]`, so the larger chapter package `IsAlgebraicStructure C F` is
  derived context here rather than primitive data.

Source/core/bridge triage:
- `source-facing`: the `C`-valued presheaf `U ↦ ∏ x : U, Aₓ x`;
- `core/canonical`: `Pi.map'` for product reindexing and `TopCat.presheafToTypes` for the
  underlying dependent-function presheaf;
- `bridge/view`: the sheaf comparison after composing with `F ⋙ uliftFunctor`.
-/

section HasProducts

variable [HasProducts.{u} C]

local instance sectionHasProduct (Aₓ : X → C) (U : (Opens X)ᵒᵖ) :
    HasProduct (fun x : U.unop ↦ Aₓ x.1) := by
  change HasLimit (Discrete.functor (fun x : U.unop ↦ Aₓ x.1))
  let h : HasProductsOfShape U.unop C := hasProductsOfShape_of_hasProducts U.unop
  exact h.has_limit (Discrete.functor (fun x : U.unop ↦ Aₓ x.1))

/-- The `C`-valued presheaf whose sections over `U` are the products of the fibres `Aₓ x` for
`x ∈ U`. -/
def pointwiseProductPresheaf_6_15_6 (Aₓ : X → C) : TopCat.Presheaf C X where
  obj U := ∏ᶜ fun x : U.unop ↦ Aₓ x.1
  map {_ _} i := Pi.map' i.unop (fun _ ↦ 𝟙 _)
  map_id U := by
    simp
  map_comp {U V W} i j := by
    simpa using
      (Pi.map'_comp_map' i.unop j.unop (fun _ ↦ 𝟙 _) (fun _ ↦ 𝟙 _)).symm

end HasProducts

section SheafComparison

variable (F : C ⥤ Type w) (Aₓ : X → C)
variable [HasLimitsOfSize.{u, u} C] [PreservesLimitsOfSize.{u, u} F]

private abbrev hasProductsOfBaseSize : HasProducts.{u} C := fun J ↦ by
  let _ : HasLimitsOfShape (Discrete J) C :=
    HasLimitsOfSize.has_limits_of_shape (Discrete J)
  infer_instance

local instance : HasProducts.{u} C := hasProductsOfBaseSize

/-- Helper for Example 6.15.6: each open set carries the relevant pointwise product in `C`. -/
local instance sheafComparisonSectionHasProduct (U : (Opens X)ᵒᵖ) :
    HasProduct (fun x : U.unop ↦ Aₓ x.1) := by
  change HasLimit (Discrete.functor (fun x : U.unop ↦ Aₓ x.1))
  let h : HasProductsOfShape U.unop C := hasProductsOfShape_of_hasProducts U.unop
  exact h.has_limit (Discrete.functor (fun x : U.unop ↦ Aₓ x.1))

/-- Helper for Example 6.15.6: over an open set `U`, the underlying type of the product object
`∏ x : U, Aₓ x` is canonically the dependent function type on `U`. -/
private noncomputable abbrev pointwiseProductPresheafCompUliftComponentIso
    (U : (Opens X)ᵒᵖ) :
    ((pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).obj U) ≅
      (∀ x : U.unop, ULift.{u} (F.obj (Aₓ x.1))) :=
  letI : HasProduct (fun x : U.unop ↦ Aₓ x.1) :=
    sheafComparisonSectionHasProduct (Aₓ := Aₓ) U
  letI : PreservesLimitsOfShape (Discrete U.unop) F :=
    PreservesLimitsOfSize.preservesLimitsOfShape (F := F)
  letI : PreservesLimitsOfShape (Discrete U.unop) uliftFunctor.{u, w} :=
    PreservesLimitsOfSize.preservesLimitsOfShape (F := uliftFunctor.{u, w})
  letI : PreservesLimitsOfShape (Discrete U.unop) (F ⋙ uliftFunctor.{u, w}) :=
    inferInstance
  -- Compose the preserved-product comparison with the canonical product-in-`Type`
  -- identification.
  (PreservesProduct.iso (F ⋙ uliftFunctor.{u, w}) (fun x : U.unop ↦ Aₓ x.1)) ≪≫
    Types.productIso (fun x : U.unop ↦ ULift.{u} (F.obj (Aₓ x.1)))

/-- Helper for Example 6.15.6: the component comparison identifies each restricted section by
reading off the coordinate selected by the inclusion of opens. -/
private theorem pointwiseProductPresheafCompUliftComponentIso_hom_apply
    (U : (Opens X)ᵒᵖ)
    (s : (pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).obj U)
    (x : U.unop) :
    (pointwiseProductPresheafCompUliftComponentIso F Aₓ U).hom s x =
      Pi.π (fun y : U.unop ↦ ULift.{u} (F.obj (Aₓ y.1))) x
        (piComparison (F ⋙ uliftFunctor.{u, w}) (fun y : U.unop ↦ Aₓ y.1) s) := by
  letI : HasProduct (fun y : U.unop ↦ Aₓ y.1) :=
    sheafComparisonSectionHasProduct (Aₓ := Aₓ) U
  letI : PreservesLimitsOfShape (Discrete U.unop) F :=
    PreservesLimitsOfSize.preservesLimitsOfShape (F := F)
  letI : PreservesLimitsOfShape (Discrete U.unop) uliftFunctor.{u, w} :=
    PreservesLimitsOfSize.preservesLimitsOfShape (F := uliftFunctor.{u, w})
  letI : PreservesLimitsOfShape (Discrete U.unop) (F ⋙ uliftFunctor.{u, w}) :=
    inferInstance
  -- Unfold the comparison iso and read off its `x`-coordinate.
  change
    (((PreservesProduct.iso (F ⋙ uliftFunctor.{u, w}) (fun y : U.unop ↦ Aₓ y.1)).hom ≫
          (Types.productIso (fun y : U.unop ↦ ULift.{u} (F.obj (Aₓ y.1)))).hom)
        s) x =
      Pi.π (fun y : U.unop ↦ ULift.{u} (F.obj (Aₓ y.1))) x
        (piComparison (F ⋙ uliftFunctor.{u, w}) (fun y : U.unop ↦ Aₓ y.1) s)
  simp [PreservesProduct.iso_hom]

/-- Helper for Example 6.15.6: the component comparison identifies each restricted section by
reading off the coordinate selected by the inclusion of opens. -/
private theorem pointwiseProductPresheafCompUlift_coordinate_naturality
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : (pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).obj U)
    (x : V.unop) :
    (pointwiseProductPresheafCompUliftComponentIso F Aₓ V).hom
        ((pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).map i s) x =
      ((pointwiseProductPresheafCompUliftComponentIso F Aₓ U).hom s) (i.unop x) := by
  -- Reduce both sides to the corresponding coordinates of the preserved-product comparison.
  rw [pointwiseProductPresheafCompUliftComponentIso_hom_apply (F := F) (Aₓ := Aₓ)]
  rw [pointwiseProductPresheafCompUliftComponentIso_hom_apply (F := F) (Aₓ := Aₓ)]
  -- The restriction map is `Pi.map'`, so after evaluating at one coordinate both sides become the
  -- same mapped projection.
  have h₁ :
      Pi.π (fun y : V.unop ↦ ULift.{u} (F.obj (Aₓ y.1))) x
          (piComparison (F ⋙ uliftFunctor.{u, w}) (fun y : V.unop ↦ Aₓ y.1)
            ((pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).map i s)) =
        ((F ⋙ uliftFunctor.{u, w}).map (Pi.π (fun y : V.unop ↦ Aₓ y.1) x))
          (((pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).map i) s) := by
    simpa using
      congr_fun
        (piComparison_comp_π (F ⋙ uliftFunctor.{u, w}) (fun y : V.unop ↦ Aₓ y.1) x)
        (((pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).map i) s)
  have h₂ :
      ((F ⋙ uliftFunctor.{u, w}).map (Pi.π (fun y : V.unop ↦ Aₓ y.1) x))
          (((pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).map i) s) =
        ((F ⋙ uliftFunctor.{u, w}).map
          ((pointwiseProductPresheaf_6_15_6 Aₓ).map i ≫ Pi.π (fun y : V.unop ↦ Aₓ y.1) x)) s := by
    -- Move the restriction morphism inside the functorial action.
    exact
      (FunctorToTypes.map_comp_apply
        (F := F ⋙ uliftFunctor.{u, w})
        ((pointwiseProductPresheaf_6_15_6 Aₓ).map i)
        (Pi.π (fun y : V.unop ↦ Aₓ y.1) x) s).symm
  have h₃ :
      ((F ⋙ uliftFunctor.{u, w}).map
        ((pointwiseProductPresheaf_6_15_6 Aₓ).map i ≫ Pi.π (fun y : V.unop ↦ Aₓ y.1) x)) s =
        ((F ⋙ uliftFunctor.{u, w}).map
          (Pi.π (fun y : U.unop ↦ Aₓ y.1) (i.unop x))) s := by
    -- Evaluate the `Pi.map'` restriction at the chosen coordinate.
    have hπ :
        (pointwiseProductPresheaf_6_15_6 Aₓ).map i ≫ Pi.π (fun y : V.unop ↦ Aₓ y.1) x =
          Pi.π (fun y : U.unop ↦ Aₓ y.1) (i.unop x) := by
      simpa [pointwiseProductPresheaf_6_15_6] using
        (Pi.map'_comp_π i.unop (fun _ ↦ 𝟙 _) x)
    simpa using congr_fun ((F ⋙ uliftFunctor.{u, w}).congr_map hπ) s
  have hlast :
      ((F ⋙ uliftFunctor.{u, w}).map
        (Pi.π (fun y : U.unop ↦ Aₓ y.1) (i.unop x))) s =
        Pi.π (fun y : U.unop ↦ ULift.{u} (F.obj (Aₓ y.1))) (i.unop x)
          (piComparison (F ⋙ uliftFunctor.{u, w}) (fun y : U.unop ↦ Aₓ y.1) s) := by
    simpa using
      (congr_fun
        (piComparison_comp_π (F ⋙ uliftFunctor.{u, w}) (fun y : U.unop ↦ Aₓ y.1)
          (i.unop x))
        s).symm
  exact h₁.trans (h₂.trans (h₃.trans hlast))

/-- Helper for Example 6.15.6: the underlying presheaf of the pointwise product presheaf is the
canonical presheaf of dependent functions with values in the underlying types. -/
private theorem pointwiseProductPresheafCompUliftIsoToTypes_naturality
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}).map i ≫
        (pointwiseProductPresheafCompUliftComponentIso F Aₓ V).hom =
      (pointwiseProductPresheafCompUliftComponentIso F Aₓ U).hom ≫
        (TopCat.presheafToTypes X (fun x : X ↦ ULift.{u} (F.obj (Aₓ x)))).map i := by
  ext s x
  -- Evaluate the naturality square on one section and one coordinate.
  simpa [TopCat.presheafToTypes_map] using
    pointwiseProductPresheafCompUlift_coordinate_naturality (F := F) (Aₓ := Aₓ) i s x

/-- Helper for Example 6.15.6: the underlying presheaf of the pointwise product presheaf is the
canonical presheaf of dependent functions with values in the underlying types. -/
private noncomputable abbrev pointwiseProductPresheafCompUliftIsoToTypes :
    (pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}) ≅
      TopCat.presheafToTypes X (fun x : X ↦ ULift.{u} (F.obj (Aₓ x))) :=
  NatIso.ofComponents
    (fun U ↦ pointwiseProductPresheafCompUliftComponentIso F Aₓ U)
    (fun {U V} i ↦
      pointwiseProductPresheafCompUliftIsoToTypes_naturality
        (F := F) (Aₓ := Aₓ) (U := U) (V := V) i)

/-- After composing with the forgetful functor and a universe lift, the pointwise product presheaf
is a sheaf of types. -/
-- Proof sketch: the composite
-- `pointwiseProductPresheaf_6_15_6 X Aₓ ⋙ F ⋙ uliftFunctor` is canonically identified objectwise with
-- the dependent-function presheaf
-- `U ↦ ∀ x : U, ULift (F.obj (Aₓ x.1))`; this is a sheaf by Example 6.7.5.
private theorem pointwiseProductPresheaf_comp_uliftFunctor_isSheaf
    : TopCat.Presheaf.IsSheaf
        (pointwiseProductPresheaf_6_15_6 Aₓ ⋙ F ⋙ uliftFunctor.{u, w}) := by
  -- Transfer the canonical sheaf proof for dependent functions across the comparison isomorphism.
  exact
    (TopCat.Presheaf.isSheaf_iso_iff (pointwiseProductPresheafCompUliftIsoToTypes F Aₓ)).2 <|
      TopCat.Presheaf.toTypes_isSheaf (X := X) (fun x : X ↦ ULift.{u} (F.obj (Aₓ x)))

-- Proof sketch: apply `TopCat.Presheaf.isSheaf_iff_isSheaf_comp` to the composite forgetful
-- functor `F ⋙ uliftFunctor`; the companion theorem above supplies the sheaf condition for the
-- resulting `Type`-valued presheaf.
/-- Example 6.15.6: let `(C, F)` be a type of algebraic structures, let `X` be a topological
space, and let `Aₓ : X → C`. Then the presheaf `U ↦ ∏ x : U, Aₓ x` with the evident restriction
maps is a sheaf. For the source application to algebraic structures, this conclusion is obtained
from the canonical comparison theorem using only limit preservation and reflection of
isomorphisms. -/
theorem pointwiseProductPresheaf_isSheaf
    [F.ReflectsIsomorphisms] : (pointwiseProductPresheaf_6_15_6 Aₓ).IsSheaf := by
  let _ : uliftFunctor.{u, w}.ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_of_full_and_faithful (uliftFunctor.{u, w})
  let _ : (F ⋙ uliftFunctor.{u, w}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_comp F uliftFunctor.{u, w}
  -- Check the sheaf condition after composing with the forgetful functor to underlying types.
  exact
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
      (F ⋙ uliftFunctor.{u, w}) (pointwiseProductPresheaf_6_15_6 Aₓ)).2 <|
      pointwiseProductPresheaf_comp_uliftFunctor_isSheaf F Aₓ

end SheafComparison
