module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap04.Definition_4_3_3
public import stacks_project.Chap04.Definition_4_38_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open CategoryOfElements Opposite Functor
open Functor.Fiber

/- Domain-style sampling for Example 4.38.5:
- primary domain: categories fibred in sets coming from the category-of-elements construction for
  a `Type`-valued presheaf.
- inspected owner-level declarations:
  `CategoryOfElements.π`,
  `FibredInSetsOver.ofFunctor`,
  `IsFibredInSets`.
- best owner abstraction: the source-facing theorem is the fibred-in-sets instance on the
  canonical projection `((π F).leftOp)`, while the natural downstream owner object is the bundled
  category `FibredInSetsOver C`.
- primitive data: the category-of-elements projection `((π F).leftOp)`.
- derived API: the fibred-in-sets instance; the bundled object is obtained directly via
  `FibredInSetsOver.ofFunctor ((π F).leftOp)`.

Source/core/bridge triage:
- `source-facing`: `presheaf_categoryOfElementsProjection_isFibredInSets`.
- `core/canonical`: `IsFibredInSets ((π F).leftOp)`.
- `bridge/view`: direct bundling by `FibredInSetsOver.ofFunctor ((π F).leftOp)`. -/

section

variable {C : Type u} [Category.{v} C]

-- Proof sketch: identify the textbook category `\mathcal S_F` with `F.Elementsᵒᵖ`; cartesian
-- lifts are induced by pullback along morphisms in the base, and each fiber is discrete because a
-- morphism over an identity is determined by equality of the corresponding elements.

private abbrev presheafCategoryOfElementsObj
    (F : Presheaf.{w} C) {U : C} (a : F.obj (op U)) :
    F.Elementsᵒᵖ :=
  op ⟨op U, a⟩

private abbrev presheafCategoryOfElementsPullbackObj
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) : F.Elementsᵒᵖ :=
  op ⟨op V, F.map f.op a⟩

private abbrev presheafCategoryOfElementsPullbackHom
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) :
    presheafCategoryOfElementsPullbackObj F f a ⟶ presheafCategoryOfElementsObj F a :=
  Quiver.Hom.op <| homMk _ _ f.op rfl

private theorem presheafCategoryOfElementsPullbackHom_isHomLift
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) :
    IsHomLift ((π F).leftOp) f
      (presheafCategoryOfElementsPullbackHom F f a) := by
  refine IsHomLift.of_fac' ((π F).leftOp) f _ rfl rfl ?_
  simp [presheafCategoryOfElementsPullbackHom]

private theorem presheafCategoryOfElementsPullbackHom_isStronglyCartesian
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) :
    IsStronglyCartesian ((π F).leftOp) f
      (presheafCategoryOfElementsPullbackHom F f a) := by
  refine
    { toIsHomLift := presheafCategoryOfElementsPullbackHom_isHomLift F f a
      universal_property' := ?_ }
  intro a' g φ' hφ'
  let hgf : ((π F).leftOp).obj a' ⟶ U := g ≫ f
  have hComp : hgf = ((π F).leftOp).map φ' :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ ((π F).leftOp) _ _ hgf φ' hφ'
  have hVal : φ'.unop.val = f.op ≫ g.op := by
    simpa [hgf] using congrArg Quiver.Hom.op hComp.symm
  refine ⟨Quiver.Hom.op (homMk _ _ g.op ?_), ⟨?_, ?_⟩, ?_⟩
  · simpa [FunctorToTypes.map_comp_apply, hVal] using φ'.unop.property
  · refine IsHomLift.of_fac' ((π F).leftOp) g _ rfl rfl ?_
    simp
  · exact Quiver.Hom.unop_inj <| ext F _ _ <| by
      simpa [presheafCategoryOfElementsPullbackHom] using hVal.symm
  · intro ψ hψ
    exact Quiver.Hom.unop_inj <| ext F _ _ <| by
      have hBase : g = ((π F).leftOp).map ψ :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ ((π F).leftOp) _ _ g ψ hψ.1
      simpa using congrArg Quiver.Hom.op hBase.symm

private theorem presheafCategoryOfElementsFiber_unop_val
    (F : Presheaf.{w} C) {U : C} {x y : ((π F).leftOp).Fiber U}
    (φ : x ⟶ y) :
    (fiberInclusion.map φ).unop.val =
      eqToHom ((congrArg Opposite.op y.2).trans (congrArg Opposite.op x.2).symm) := by
  have hFac :=
    @IsHomLift.fac' _ _ _ _ ((π F).leftOp) _ _ _ _ (𝟙 U)
      (fiberInclusion.map φ) φ.2
  simp at hFac
  simpa using congrArg Quiver.Hom.op hFac

/-- Example 4.38.5: for a presheaf of sets `F : Presheaf.{w} C`, the opposite category of elements
`F.Elementsᵒᵖ` with its canonical projection to `𝒞` is a category fibred in sets. This is the
mathlib-facing form of the textbook construction of `\mathcal S_F`. -/
theorem presheaf_categoryOfElementsProjection_isFibredInSets
    (F : Presheaf.{w} C) :
    IsFibredInSets ((π F).leftOp) := by
  letI : ((π F).leftOp).IsFibered := by
    refine IsFibered.of_exists_isStronglyCartesian ?_
    intro x V f
    refine ⟨presheafCategoryOfElementsPullbackObj F f x.unop.2,
      presheafCategoryOfElementsPullbackHom F f x.unop.2,
      presheafCategoryOfElementsPullbackHom_isStronglyCartesian F f x.unop.2⟩
  letI (U : C) : IsDiscrete (((π F).leftOp).Fiber U) := by
    refine
      { subsingleton := ?_
        eq_of_hom := ?_ }
    · intro x y
      constructor
      intro φ ψ
      apply hom_ext
      exact Quiver.Hom.unop_inj <| ext F _ _ <| by
        simp [presheafCategoryOfElementsFiber_unop_val F φ,
          presheafCategoryOfElementsFiber_unop_val F ψ]
    · intro x y φ
      apply fiberInclusion_obj_inj
      change x.1 = y.1
      apply congrArg Opposite.op
      symm
      refine Elements.ext _ _ ?_ ?_
      · exact (congrArg Opposite.op y.2).trans (congrArg Opposite.op x.2).symm
      · simpa [presheafCategoryOfElementsFiber_unop_val F φ] using
          (fiberInclusion.map φ).unop.property
  infer_instance

instance (F : Presheaf.{w} C) :
    IsFibredInSets ((π F).leftOp) :=
  presheaf_categoryOfElementsProjection_isFibredInSets F

end

end CategoryTheory
