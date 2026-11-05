module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Lemma_4_35_9
public import stacks_project.Chap04.Lemma_4_40_2
public import stacks_project.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories
public import stacks_project.Chap04.Lemma_4_42_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open Functor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsMor

open FibredInGroupoidsOver (ofFunctor)

variable {X Y : FibredInGroupoidsOver C}
variable {A : Type*} [Category A]
variable {B : Type*} [Category B]

/- Domain-style sampling for Lemma 4.42.5:
- primary domain: representable morphisms of categories fibred in groupoids over a fixed base;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.sliceTwoFibreProduct`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable`;
- best owner abstraction: the owner hom `F : X ⟶ Y` together with the canonical slice base-change
  object `F.sliceTwoFibreProduct G` attached to an actual slice morphism `G : C/U ⟶ Y`; the
  source-facing fibre-object formulation is recovered through Yoneda equivalence only as internal
  bridge data, not as a second public owner;
- primitive data: the owner morphism `F`, faithfulness of `F.toBasedFunctor`, and for each slice
  morphism `G : C/U ⟶ Y` representability of the canonical iso-class presheaf of
  `F.sliceTwoFibreProduct G`;
- derived API: the representability criterion from Lemma `4.40.2`, and the internal Yoneda bridge
  from a fiber object `y ∈ Y_U` to a slice morphism `G : C/U ⟶ Y`.

Source/core/bridge triage:
- `source-facing`: Lemma 4.42.5;
- `core/canonical`: `F.IsRepresentable`;
- `bridge/view`: the internal Yoneda-selected morphism `C/U ⟶ Y` attached to a fiber object
  `y ∈ Y_U`. -/

/-- Helper for Lemma 4.42.5: a faithful functor into a thin category has a thin source. -/
private theorem isThin_of_faithful
    (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A := by
  intro a b
  refine ⟨?_⟩
  intro f g
  exact G.map_injective (Subsingleton.elim _ _)

/-- Helper for Lemma 4.42.5: in a groupoid-valued faithful functor, every structured-arrow
category is thin because the target commutativity relation determines the lifted arrow uniquely. -/
private theorem structuredArrow_thin_of_faithful
    (b : B) (G : A ⥤ B) [G.Faithful] [IsGroupoid B] :
    Quiver.IsThin (StructuredArrow b G) := by
  intro X Y
  refine ⟨?_⟩
  intro f g
  apply StructuredArrow.hom_ext
  apply G.map_injective
  have hf :
      inv X.hom ≫ Y.hom = G.map f.right := by
    -- Precompose the commutativity relation with the inverse of `X.hom`.
    simpa [Category.assoc] using congrArg (fun k ↦ inv X.hom ≫ k) f.w
  have hg :
      inv X.hom ≫ Y.hom = G.map g.right := by
    -- The same normalization applies to any competing lift.
    simpa [Category.assoc] using congrArg (fun k ↦ inv X.hom ≫ k) g.w
  exact hf.symm.trans hg

/-- Helper for Lemma 4.42.5: fiberwise faithfulness forces every slice base change of `F` to be
fibred in setoids. -/
private theorem sliceTwoFibreProduct_isFibredInSetoids_of_fiberwise_faithful
    (F : FibredInGroupoidsMor X Y)
    (hFiber : ∀ V : C, (fiberFunctor F V).Faithful)
    {U : C} (G : ofFunctor (Over.forget U) ⟶ Y) :
    IsFibredInSetoids (F.sliceTwoFibreProduct G).p := by
  refine { fiber_isThin := ?_ }
  intro f
  let E :
      StructuredArrow ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl)) (fiberFunctor F f.left) ≌
        ((F.sliceTwoFibreProduct G).p).Fiber f := by
    -- Lemma `4.42.1` identifies the slice fiber with the structured-arrow category in the fiber.
    simpa [FibredInGroupoidsMor.sliceTwoFibreProduct] using
      (sliceTwoFibreProductStructuredArrowEquivFiber
        (G := FibredInGroupoidsMor.toBasedFunctor G)
        (F := FibredInGroupoidsMor.toBasedFunctor F)
        (f := f))
  letI : (fiberFunctor F f.left).Faithful := hFiber f.left
  letI :
      Quiver.IsThin
        (StructuredArrow ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl))
          (fiberFunctor F f.left)) :=
    structuredArrow_thin_of_faithful
      ((fiberFunctor G f.left).obj (Functor.Fiber.mk rfl))
      (fiberFunctor F f.left)
  -- Transport the thin structured-arrow description across the equivalence from Lemma `4.42.1`.
  exact isThin_of_faithful E.symm.functor

/-- Helper for Lemma 4.42.5: once the slice base change is fibred in setoids, Lemma `4.40.2`
turns representability of its iso-class presheaf into representability of the slice itself. -/
private theorem sliceTwoFibreProduct_isRepresentable_of_faithful
    (F : FibredInGroupoidsMor X Y)
    (hFiber : ∀ V : C, (fiberFunctor F V).Faithful)
    {U : C} (G : ofFunctor (Over.forget U) ⟶ Y)
    (hG : ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf).IsRepresentable) :
    (F.sliceTwoFibreProduct G).IsRepresentable := by
  -- Lemma `4.40.2` reduces representability to the setoid condition plus the given presheaf.
  exact
    (FibredInGroupoidsOver.isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable
      (F.sliceTwoFibreProduct G)).2
      ⟨sliceTwoFibreProduct_isFibredInSetoids_of_fiberwise_faithful F hFiber G, hG⟩

-- Proof sketch: fix `U : C` and `G : C/U ⟶ Y`. The category `F.sliceTwoFibreProduct G` is the
-- canonical slice base change of `F` along `G`, and its iso-class presheaf is exactly the owner
-- presheaf `fiberIsoClassPresheaf (F.sliceTwoFibreProduct G).p`. Under Yoneda, taking `G`
-- corresponding to `y ∈ Y_U` recovers the source presheaf of pairs
-- `(x, \phi : f^* y ⟶ F(x))`. Faithfulness of `F.toBasedFunctor` forces each such slice
-- projection to be fibred in setoids, and Lemma `4.40.2` upgrades representability of every
-- slice iso-class presheaf to representability of every slice base change, hence of `F`.
/-- Lemma 4.42.5: let `F : X ⟶ Y` be a morphism of categories fibred in groupoids over `C`.
Assume that the underlying based functor `F.toBasedFunctor` is faithful and that for every object
`U : C` and every slice morphism `G : C/U ⟶ Y`, the canonical presheaf of isomorphism classes of
objects in the slice base change `F.sliceTwoFibreProduct G` is representable. Via the Yoneda
equivalence for `Y_U`, this is exactly the source presheaf of isomorphism classes of pairs
`(x, \phi : f^* y ⟶ F(x))`. Then `F` is representable. -/
theorem isRepresentable_of_faithful_and_sliceTwoFibreProductIsoClassPresheaf_isRepresentable
    (F : FibredInGroupoidsMor X Y)
    (hFaithful : (toBasedFunctor F).Faithful)
    (hRepresentable :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ Y),
        ((F.sliceTwoFibreProduct G).p.fiberIsoClassPresheaf).IsRepresentable) :
    F.IsRepresentable := by
  -- Route correction: follow the source proof through slice fibers and Lemma `4.40.2`,
  -- rather than re-expressing representability through a separate Yoneda detour.
  rw [isRepresentable_iff_forall_sliceTwoFibreProduct_isRepresentable]
  have hFiber : ∀ U : C, (fiberFunctor F U).Faithful :=
    (faithful_iff_fiberwise (F := F)).1 hFaithful
  intro U G
  -- Each slice base change is representable once its fibers are setoids and its iso-class
  -- presheaf is representable by hypothesis.
  exact sliceTwoFibreProduct_isRepresentable_of_faithful F hFiber G (hRepresentable G)

end FibredInGroupoidsMor

end CategoryTheory
