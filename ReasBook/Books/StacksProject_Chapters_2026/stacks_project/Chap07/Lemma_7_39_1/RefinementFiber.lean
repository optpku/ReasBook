module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap04.Lemma_4_19_2
public import stacks_project.Chap07.«7_32_1_1»
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w w₁ q

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

namespace GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

noncomputable abbrev refinementFiberDiagram (S : ιᵒᵖ ⥤ C) (W : C) :
    ιᵒᵖᵒᵖ ⥤ Type (max u v w) :=
  S.op ⋙ shrinkYoneda.{max u v w}.obj W

variable {ι' : Type w} [Preorder ι'] {S : ιᵒᵖ ⥤ C}
  (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C) (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)

noncomputable abbrev refinementIndexFunctor :
    ιᵒᵖᵒᵖ ⥤ ι'ᵒᵖᵒᵖ :=
  show ιᵒᵖᵒᵖ ⥤ ι'ᵒᵖᵒᵖ from (j.toOrderHom.toFunctor).op.op

noncomputable abbrev refinementDiagramHom :
    S.op ⟶ refinementIndexFunctor j ⋙ T.op :=
  show S.op ⟶ refinementIndexFunctor j ⋙ T.op from
    NatTrans.op e.inv ≫ (Functor.opComp (j.toOrderHom.toFunctor).op T).hom

noncomputable def refinementFiberDiagramMap (W : C) :
    refinementFiberDiagram S W ⟶ refinementIndexFunctor j ⋙ refinementFiberDiagram T W :=
  Functor.whiskerRight (refinementDiagramHom j T e) (shrinkYoneda.{max u v w}.obj W)

/-- Helper for Lemma 7.39.1: the objectwise map on inverse-system fibers induced by a
refinement datum. -/
noncomputable def refinementFiberApp (W : C) :
    (fiber.{max u v w} S).obj W ⟶ (fiber.{max u v w} T).obj W :=
  colim.map (refinementFiberDiagramMap j T e W) ≫
    colimit.pre (refinementFiberDiagram T W) (refinementIndexFunctor j)

/-- Helper for Lemma 7.39.1: the refinement map sends a canonical fiber generator to the
corresponding refined generator. -/
theorem refinementFiberApp_fiberMk {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    refinementFiberApp j T e W (fiberMk.{max u v w} f) =
      (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} (e.inv.app U ≫ f)) := by
  -- First transport the generator through the colimit map induced by the refinement datum.
  rw [refinementFiberApp, show fiberMk.{max u v w} f =
    colimit.ι (S.op ⋙ shrinkYoneda.{max u v w}.obj W) (op U)
      ((shrinkYonedaObjObjEquiv.{max u v w}).symm f) by rfl]
  change colimit.pre (refinementFiberDiagram T W) (refinementIndexFunctor j)
      (colimMap (refinementFiberDiagramMap j T e W)
        (colimit.ι (S.op ⋙ shrinkYoneda.{max u v w}.obj W) (op U)
          ((shrinkYonedaObjObjEquiv.{max u v w}).symm f))) =
    (show (fiber.{max u v w} T).obj W from fiberMk.{max u v w} (e.inv.app U ≫ f))
  have hmap :
      colimMap (refinementFiberDiagramMap j T e W)
        (colimit.ι (S.op ⋙ shrinkYoneda.{max u v w}.obj W) (op U)
          ((shrinkYonedaObjObjEquiv.{max u v w}).symm f)) =
        colimit.ι ((refinementIndexFunctor j) ⋙ refinementFiberDiagram T W) (op U)
          ((refinementFiberDiagramMap j T e W).app (op U)
            ((shrinkYonedaObjObjEquiv.{max u v w}).symm f)) := by
    simpa using congrFun (ι_colimMap (refinementFiberDiagramMap j T e W) (op U))
      ((shrinkYonedaObjObjEquiv.{max u v w}).symm f)
  rw [hmap]
  -- The objectwise component is exactly postcomposition with `e.inv.app U`.
  refine (congrFun (colimit.ι_pre (refinementFiberDiagram T W) (refinementIndexFunctor j) (op U))
      ((refinementFiberDiagramMap j T e W).app (op U)
        ((shrinkYonedaObjObjEquiv.{max u v w}).symm f))).trans ?_
  simpa [fiberMk, refinementFiberDiagramMap, refinementDiagramHom, refinementFiberDiagram] using
    congrArg
      (colimit.ι (refinementFiberDiagram T W) ((refinementIndexFunctor j).obj (op U)))
      (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{max u v w} ((e.inv.app U).op) f)

/-- The natural transformation on inverse-system fiber functors induced by a refinement datum
`S ≅ (j.toOrderHom.toFunctor).op ⋙ T`. -/
noncomputable def refinementFiber :
    fiber.{max u v w} S ⟶ fiber.{max u v w} T where
  app := refinementFiberApp j T e
  naturality := by
    intro X Y f
    -- The refinement map is determined on the canonical fiber generators `fiberMk g`.
    ext x
    rcases fiberMk_jointly_surjective x with ⟨U, g, rfl⟩
    simp [refinementFiberApp_fiberMk]

@[simp]
theorem refinementFiber_app_fiberMk {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (refinementFiber j T e).app W (fiberMk f) =
      (show (fiber.{max u v w} T).obj W from fiberMk (e.inv.app U ≫ f)) := by
  -- Evaluate the colimit morphism defining `refinementFiber` on the generator `fiberMk f`.
  simpa [refinementFiber] using refinementFiberApp_fiberMk (j := j) (T := T) (e := e) f

section CrossUniverse

variable {ι₀ : Type w} [Preorder ι₀] {ι₁ : Type w₁} [Preorder ι₁]
variable [LocallySmall.{q} C]
variable [InitiallySmall.{q} ι₀ᵒᵖ] [InitiallySmall.{q} ι₁ᵒᵖ]
variable {S₀ : ι₀ᵒᵖ ⥤ C}
variable (j₀₁ : ι₀ ↪o ι₁) (T₁ : ι₁ᵒᵖ ⥤ C)
  (e₀₁ : S₀ ≅ (j₀₁.toOrderHom.toFunctor).op ⋙ T₁)

local instance sourceHasColimitsOfShape : HasColimitsOfShape ι₀ᵒᵖᵒᵖ (Type q) :=
  hasColimitsOfShape_of_finallySmall _ _

local instance targetHasColimitsOfShape : HasColimitsOfShape ι₁ᵒᵖᵒᵖ (Type q) :=
  hasColimitsOfShape_of_finallySmall _ _

noncomputable abbrev refinementFiberSourceDiagram (S : ι₀ᵒᵖ ⥤ C) (W : C) :
    ι₀ᵒᵖᵒᵖ ⥤ Type q :=
  S.op ⋙ shrinkYoneda.{q}.obj W

noncomputable abbrev refinementFiberTargetDiagram (T : ι₁ᵒᵖ ⥤ C) (W : C) :
    ι₁ᵒᵖᵒᵖ ⥤ Type q :=
  T.op ⋙ shrinkYoneda.{q}.obj W

noncomputable abbrev refinementIndexFunctorOfUniverses :
    ι₀ᵒᵖᵒᵖ ⥤ ι₁ᵒᵖᵒᵖ :=
  show ι₀ᵒᵖᵒᵖ ⥤ ι₁ᵒᵖᵒᵖ from (j₀₁.toOrderHom.toFunctor).op.op

noncomputable abbrev refinementDiagramHomOfUniverses :
    S₀.op ⟶ refinementIndexFunctorOfUniverses j₀₁ ⋙ T₁.op :=
  show S₀.op ⟶ refinementIndexFunctorOfUniverses j₀₁ ⋙ T₁.op from
    NatTrans.op e₀₁.inv ≫ (Functor.opComp (j₀₁.toOrderHom.toFunctor).op T₁).hom

noncomputable def refinementFiberDiagramMapOfUniverses (W : C) :
    refinementFiberSourceDiagram S₀ W ⟶
      refinementIndexFunctorOfUniverses j₀₁ ⋙ refinementFiberTargetDiagram T₁ W :=
  Functor.whiskerRight (refinementDiagramHomOfUniverses j₀₁ T₁ e₀₁) (shrinkYoneda.{q}.obj W)

noncomputable def refinementFiberAppOfUniverses (W : C) :
    (fiber.{q} S₀).obj W ⟶ (fiber.{q} T₁).obj W :=
  colim.map (refinementFiberDiagramMapOfUniverses j₀₁ T₁ e₀₁ W) ≫
    colimit.pre (refinementFiberTargetDiagram T₁ W) (refinementIndexFunctorOfUniverses j₀₁)

theorem refinementFiberAppOfUniverses_fiberMk {U : ι₀ᵒᵖ} {W : C}
    (f : S₀.obj U ⟶ W) :
    refinementFiberAppOfUniverses j₀₁ T₁ e₀₁ W (fiberMk.{q} f) =
      (show (fiber.{q} T₁).obj W from fiberMk.{q} (e₀₁.inv.app U ≫ f)) := by
  -- The cross-universe construction is the same colimit computation as `refinementFiber`, but
  -- with the source and target diagrams kept at the common fiber universe `q`.
  rw [refinementFiberAppOfUniverses, show fiberMk.{q} f =
    colimit.ι (S₀.op ⋙ shrinkYoneda.{q}.obj W) (op U)
      ((shrinkYonedaObjObjEquiv.{q}).symm f) by rfl]
  change colimit.pre (refinementFiberTargetDiagram T₁ W) (refinementIndexFunctorOfUniverses j₀₁)
      (colimMap (refinementFiberDiagramMapOfUniverses j₀₁ T₁ e₀₁ W)
        (colimit.ι (S₀.op ⋙ shrinkYoneda.{q}.obj W) (op U)
          ((shrinkYonedaObjObjEquiv.{q}).symm f))) =
    (show (fiber.{q} T₁).obj W from fiberMk.{q} (e₀₁.inv.app U ≫ f))
  have hmap :
      colimMap (refinementFiberDiagramMapOfUniverses j₀₁ T₁ e₀₁ W)
        (colimit.ι (S₀.op ⋙ shrinkYoneda.{q}.obj W) (op U)
          ((shrinkYonedaObjObjEquiv.{q}).symm f)) =
        colimit.ι ((refinementIndexFunctorOfUniverses j₀₁) ⋙
            refinementFiberTargetDiagram T₁ W) (op U)
          ((refinementFiberDiagramMapOfUniverses j₀₁ T₁ e₀₁ W).app (op U)
            ((shrinkYonedaObjObjEquiv.{q}).symm f)) := by
    simpa using congrFun
      (ι_colimMap (refinementFiberDiagramMapOfUniverses j₀₁ T₁ e₀₁ W) (op U))
      ((shrinkYonedaObjObjEquiv.{q}).symm f)
  rw [hmap]
  refine (congrFun
    (colimit.ι_pre (refinementFiberTargetDiagram T₁ W)
      (refinementIndexFunctorOfUniverses j₀₁) (op U))
      ((refinementFiberDiagramMapOfUniverses j₀₁ T₁ e₀₁ W).app (op U)
        ((shrinkYonedaObjObjEquiv.{q}).symm f))).trans ?_
  simpa [fiberMk, refinementFiberDiagramMapOfUniverses, refinementDiagramHomOfUniverses,
    refinementFiberSourceDiagram, refinementFiberTargetDiagram] using
    congrArg
      (colimit.ι (refinementFiberTargetDiagram T₁ W)
        ((refinementIndexFunctorOfUniverses j₀₁).obj (op U)))
      (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{q} ((e₀₁.inv.app U).op) f)

/-- Cross-universe version of `refinementFiber`: a refinement whose source and target index
types live in different universes still induces a natural map on inverse-system fibers, provided
both indexing categories are initially small in the chosen fiber universe `q`. -/
noncomputable def refinementFiberOfUniverses :
    fiber.{q} S₀ ⟶ fiber.{q} T₁ where
  app := refinementFiberAppOfUniverses j₀₁ T₁ e₀₁
  naturality := by
    intro X Y f
    -- As in the same-universe proof, naturality is checked on the canonical generators.
    ext x
    rcases fiberMk_jointly_surjective x with ⟨U, g, rfl⟩
    simp [refinementFiberAppOfUniverses_fiberMk]

@[simp]
theorem refinementFiberOfUniverses_app_fiberMk {U : ι₀ᵒᵖ} {W : C}
    (f : S₀.obj U ⟶ W) :
    (refinementFiberOfUniverses j₀₁ T₁ e₀₁).app W (fiberMk f) =
      (show (fiber.{q} T₁).obj W from fiberMk (e₀₁.inv.app U ≫ f)) := by
  -- Record the generator computation as public API, matching `refinementFiber_app_fiberMk`.
  simpa [refinementFiberOfUniverses] using
    refinementFiberAppOfUniverses_fiberMk (j₀₁ := j₀₁) (T₁ := T₁) (e₀₁ := e₀₁) f

end CrossUniverse

end GrothendieckTopology.Point.ofIsCofiltered

end CategoryTheory
