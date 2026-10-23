module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Lemma_4_40_2
public import stacks_project.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories
public import stacks_project.Chap04.Lemma_4_42_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver C}

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

variable {A : Type*} [Category A]
variable {B : Type*} [Category B]

/- Domain-style sampling for Lemma 4.42.4:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base and
  the induced functors on their fiber categories;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `sliceTwoFibreProductStructuredArrowEquivFiber`,
  `FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- best owner abstraction: the source-facing owner hom `F : X ⟶ Y`, together with its canonical
  slice base change `F.sliceTwoFibreProduct G` over `C/U`; the fiberwise statement should be
  derived from that owner data rather than from a parallel local slice wrapper;
- primitive data: the owner morphism `F` and, for a chosen `y ∈ Y_U`, the canonical Yoneda
  representing morphism `Gy : C/U ⟶ Y`;
- derived API: the slice object `F.sliceTwoFibreProduct G`, its fibred-in-setoids consequence via
  Lemma `4.40.2`, and the comparison equivalence of Lemma `4.42.1`.

Source/core/bridge triage:
- `source-facing`: `fiber_functor_faithful_of_is_representable`;
- `core/canonical`: `F.IsRepresentable`, `F.sliceTwoFibreProduct G`, and the owner theorem
  `isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- `bridge/view`: the Yoneda-selected morphism `Gy` and the equivalence
  `sliceTwoFibreProductStructuredArrowEquivFiber`. -/

/-- Helper for Lemma 4.42.4: the Yoneda inverse at `y ∈ Y_U` gives the canonical slice morphism
`C/U ⟶ Y` used to test representability near `y`. -/
private noncomputable abbrev yoneda_inverse_slice
    (U : C) (y : Y.p.Fiber U) :
    ofFunctor (Over.forget U) ⟶ Y :=
  ofAmbientHom ((Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.inverse.obj y)

/-- Helper for Lemma 4.42.4: a faithful functor into a thin category has a thin source. -/
private theorem isThin_of_faithful
    (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  intro a b
  refine ⟨?_⟩
  intro f g
  exact G.map_injective (Subsingleton.elim _ _)

/-- Helper for Lemma 4.42.4: the identity arrow `id_U : U/U` viewed as an object of the slice
fiber over `U`. -/
private abbrev id_slice_fiber_obj (U : C) : (Over.forget U).Fiber U :=
  ⟨Over.mk (𝟙 U), rfl⟩

/-- Helper for Lemma 4.42.4: evaluating the Yoneda-selected slice morphism at `id_U`
recovers the chosen object `y ∈ Y_U`. -/
private noncomputable def yoneda_inverse_fiber_iso
    (U : C) (y : Y.p.Fiber U) :
    ((fiberFunctor (yoneda_inverse_slice (Y := Y) U y) U).obj
      (id_slice_fiber_obj U)) ≅ y := by
  -- The Yoneda counit identifies evaluation of the inverse object at `id_U` with `y`.
  simpa [yoneda_inverse_slice, FibredInGroupoidsMor.fiberFunctor] using
    (Y.toFibredCategoryOver.yonedaEvaluationFunctor U).asEquivalence.counitIso.app y

/-- Helper for Lemma 4.42.4: representability of `F` forces every comma category
`((F_U x) ↓ F_U)` to be thin. -/
private theorem fiber_functor_image_structuredArrow_thin_of_is_representable
    (F : FibredInGroupoidsMor X Y)
    (hF : F.IsRepresentable)
    (U : C)
    (x : X.p.Fiber U) :
    Quiver.IsThin (StructuredArrow ((fiberFunctor F U).obj x) (fiberFunctor F U)) := by
  let y : Y.p.Fiber U := (fiberFunctor F U).obj x
  let Gy : ofFunctor (Over.forget U) ⟶ Y := yoneda_inverse_slice (Y := Y) U y
  let E :
      StructuredArrow ((fiberFunctor Gy U).obj (id_slice_fiber_obj U))
        (fiberFunctor F U) ≌
        ((F.sliceTwoFibreProduct Gy).p).Fiber (Over.mk (𝟙 U)) :=
    sliceTwoFibreProductStructuredArrowEquivFiber
      (G := FibredInGroupoidsMor.toBasedFunctor Gy)
      (F := FibredInGroupoidsMor.toBasedFunctor F)
      (f := Over.mk (𝟙 U))
  -- Representability of the chosen slice base change gives a thin fiber over `id_U`.
  letI :
      IsFibredInSetoids (F.sliceTwoFibreProduct Gy).p :=
    (FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable
      (F.sliceTwoFibreProduct Gy)).mp (hF Gy) |>.1
  have hThinSource :
      Quiver.IsThin (StructuredArrow
        ((fiberFunctor Gy U).obj (id_slice_fiber_obj U))
        (fiberFunctor F U)) := by
    -- Lemma `4.42.1` identifies that fiber with the relevant structured-arrow category.
    letI : Quiver.IsThin (((F.sliceTwoFibreProduct Gy).p).Fiber (Over.mk (𝟙 U))) :=
      inferInstance
    letI : E.functor.Faithful := by
      infer_instance
    exact isThin_of_faithful E.functor
  let E' :
      StructuredArrow ((fiberFunctor Gy U).obj (id_slice_fiber_obj U)) (fiberFunctor F U) ≌
        StructuredArrow ((fiberFunctor F U).obj x) (fiberFunctor F U) :=
    StructuredArrow.mapIso
      (yoneda_inverse_fiber_iso (Y := Y) U ((fiberFunctor F U).obj x))
  -- Transport thinness across the Yoneda comparison of the source object.
  letI :
      Quiver.IsThin (StructuredArrow
        ((fiberFunctor Gy U).obj (id_slice_fiber_obj U))
        (fiberFunctor F U)) :=
    hThinSource
  letI : E'.symm.functor.Faithful := by
    infer_instance
  exact isThin_of_faithful E'.symm.functor

/-- Helper for Lemma 4.42.4: if every structured-arrow category over an image object is thin,
then the functor is faithful. -/
private theorem faithful_of_image_structuredArrow_thin
    (G : A ⥤ B)
    (hThin : ∀ x : A, Quiver.IsThin (StructuredArrow (G.obj x) G)) :
    G.Faithful := by
  refine ⟨?_⟩
  intro a b f g hfg
  letI : Quiver.IsThin (StructuredArrow (G.obj a) G) := hThin a
  let source : StructuredArrow (G.obj a) G := StructuredArrow.mk (𝟙 (G.obj a))
  let target : StructuredArrow (G.obj a) G := StructuredArrow.mk (G.map f)
  let α : source ⟶ target := StructuredArrow.homMk f (by simp [source, target])
  let β : source ⟶ target := StructuredArrow.homMk g (by simpa [source, target] using hfg.symm)
  -- Thinness makes the two structured-arrow lifts coincide, hence their right components agree.
  have hαβ : α = β := Subsingleton.elim _ _
  simpa [α, β] using congrArg CommaMorphism.right hαβ

-- Proof sketch: for a fixed object `U : C`, Lemma `4.42.1` identifies the fiber over `𝟙 U` of
-- the representable base change `(C/U) ×_Y X → C/U` with the comma-style fiber category attached
-- to `F_U`. By Lemma `4.40.2`, a representable fibred category in groupoids is fibred in setoids,
-- so this fiber category is a setoid; that is exactly the faithfulness of `F_U`.
/-- Lemma 4.42.4: if a `1`-morphism `F : X ⟶ Y` of categories fibred in groupoids over `C` is
representable, then for every object `U : C` the induced functor `F_U : X_U ⥤ Y_U` between fiber
categories is faithful. -/
theorem fiber_functor_faithful_of_is_representable
    (F : FibredInGroupoidsMor X Y)
    (hF : F.IsRepresentable)
    (U : C) :
    (fiberFunctor F U).Faithful := by
  -- For each `x ∈ X_U`, representability makes the comma category `((F_U x) ↓ F_U)` thin.
  refine faithful_of_image_structuredArrow_thin (fiberFunctor F U) ?_
  intro x
  exact fiber_functor_image_structuredArrow_thin_of_is_representable F hF U x

end FibredInGroupoidsMor

end CategoryTheory
