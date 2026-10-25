module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Lemma_4_33_7
public import stacks_project.Chap04.Lemma_4_32_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver
open BasedFunctor
open Functor
open Functor.Fiber
open CategoryTheory.Limits
open Functor.IsHomLift

variable {C : Type u} [Category.{v} C]
variable {X Y : Type (max u v)} [Category.{v} X] [Category.{v} Y]
variable {pX : X ⥤ C} {pY : Y ⥤ C}

namespace FibredCategoryOver

/- Domain-style sampling for Lemma 4.42.1:
- primary domain: fibers of the left projection of the explicit slice `2`-fibre product.
- inspected owner-level declarations:
  `BasedFunctor.fiberFunctor`,
  `Fiber.inducedFunctor`,
  `CategoryOver.fibreOfPullback_equiv_pullbackOfFibres`,
  `explicitTwoFibreProductLeftProjection`,
  `StructuredArrow`.
- best owner abstraction: the core object here is the fiber of the owner projection
  `explicitTwoFibreProductLeftProjection G F`; over a fixed `f : Over U`, that fiber should be
  described by the canonical comma owner `StructuredArrow` in the fiber `pY.Fiber f.left`, not by
  a new slice-specific wrapper.
- primitive data: the based functors `G`, `F`, and the fixed slice object `f : Over U`.
- derived API: the canonical equivalence from that structured-arrow category to the corresponding
  fiber of the explicit `2`-fibre-product projection.

Source/core/bridge triage:
- `source-facing`: `sliceTwoFibreProductStructuredArrowEquivFiber`.
- `core/canonical`: `Functor.Fiber`, `BasedFunctor.fiberFunctor`,
  `CategoryOver.fibreOfPullback_equiv_pullbackOfFibres`,
  `explicitTwoFibreProductLeftProjection`, and `StructuredArrow`.
- `bridge/view`: the internal comparison functors
  `sliceTwoFibreProductStructuredArrowToExplicit` and
  `sliceTwoFibreProductStructuredArrowToFiber`. -/

end FibredCategoryOver

section SliceTwoFibreProductStructuredArrow

variable {U : C}
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)

/-- The canonical functor from the structured-arrow category to the total explicit
`2`-fibre product, with constant left projection `f`. -/
noncomputable def sliceTwoFibreProductStructuredArrowToExplicit
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ⥤
      (explicitTwoFibreProduct G F).obj where
  obj A := by
    letI : IsFibredInGroupoids (BasedCategory.ofFunctor pY).p := by
      change IsFibredInGroupoids pY
      infer_instance
    letI : IsIso A.hom := IsFibredInGroupoids.hom_isIso f.left A.hom
    exact
      { U := f.left
        obj :=
          { fst := Fiber.mk rfl
            snd := A.right
            iso := asIso A.hom } }
  map {A B} α := by
    letI : (Over.forget U).IsHomLift (𝟙 f.left) (𝟙 f) := IsHomLift.id rfl
    letI : pX.IsHomLift (𝟙 f.left) α.right.1 := α.right.2
    exact
      { base := 𝟙 f.left
        a := (Fiber.homMk (Over.forget U) f.left (𝟙 f)).1
        a_over := (Fiber.homMk (Over.forget U) f.left (𝟙 f)).2
        b := (Fiber.homMk pX f.left α.right.1).1
        b_over := (Fiber.homMk pX f.left α.right.1).2
        comm := by
          -- The left component is forced to be `𝟙 f`, so the pullback square is exactly the
          -- structured-arrow compatibility equation.
          refine ⟨?_⟩
          change G.map (𝟙 f) ≫ B.hom.1 = A.hom.1 ≫ F.map α.right.1
          have hα : B.hom.1 = A.hom.1 ≫ ((F.fiberFunctor f.left).map α.right).1 := by
            simpa using (congrArg Subtype.val (StructuredArrow.w α)).symm
          have hg : G.map (𝟙 f) = 𝟙 _ := by
            exact G.toFunctor.map_id f
          rw [hg, Category.id_comp]
          simpa using hα }
  map_id A := by
    cases A
    rfl
  map_comp α β := by
    apply ExplicitTwoFibreProductHom.ext
    · change 𝟙 f = 𝟙 f ≫ 𝟙 f
      simp
    · letI : pX.IsHomLift (𝟙 f.left) α.right.1 := α.right.2
      letI : pX.IsHomLift (𝟙 f.left) β.right.1 := β.right.2
      rfl

theorem sliceTwoFibreProductStructuredArrowToExplicit_comp_projection
    [IsFibredInGroupoids pY] (f : Over U) :
    sliceTwoFibreProductStructuredArrowToExplicit G F f ⋙
        (explicitTwoFibreProductLeftProjection G F).toFunctor =
      (Functor.const
        (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left))).obj
        f :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ α ↦ by
    change 𝟙 f = eqToHom (by simp) ≫ 𝟙 f ≫ eqToHom (by simp)
    simp)

/-- The canonical functor from the structured-arrow category
`(G(f) ↓ F_V)` to the fiber over `f` of the explicit `2`-fibre-product projection. -/
noncomputable def sliceTwoFibreProductStructuredArrowToFiber
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ⥤
      ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f :=
  Fiber.inducedFunctor
    (sliceTwoFibreProductStructuredArrowToExplicit_comp_projection G F f)

/-- Helper for Lemma 4.42.1: forgetting the redundant outer fibre equality turns an object of the
fibre of the left projection into the corresponding structured arrow. -/
private def fiberOfSliceTwoFibreProduct_to_structuredArrow_obj
    [IsFibredInGroupoids pY] (f : Over U) :
    ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f →
      StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)
  | ⟨⟨_, ⟨⟨_, rfl⟩, x, i⟩⟩, rfl⟩ => StructuredArrow.mk (Y := x) i.hom

/-- Helper for Lemma 4.42.1: the left component of a morphism in the fibre of the left projection
lies over the identity of `f.left`. -/
private theorem fiberOfSliceTwoFibreProduct_left_over_id
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (Over.forget U).IsHomLift (𝟙 f.left) φ.1.a := by
  -- After normalizing the outer fibre equalities, the projection-to-slice lift is literally over
  -- `𝟙 f`, so the left component lies over `𝟙 f.left`.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, φ =>
      letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
        simpa using φ.1.a_over
      letI : (explicitTwoFibreProductLeftProjection G F).toFunctor.IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      have ha : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      simpa [ha] using (show (Over.forget U).IsHomLift (𝟙 f.left) (𝟙 f) from IsHomLift.id rfl)

/-- Helper for Lemma 4.42.1: the right component of a morphism in the fibre of the left
projection lies over the identity of `f.left`. -/
private theorem fiberOfSliceTwoFibreProduct_right_over_id
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    pX.IsHomLift (𝟙 f.left) φ.1.b := by
  -- The right component lies over the same base map as the left one, and that base map is
  -- `𝟙 f.left` after strictifying the left slice component.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, φ =>
      letI : pX.IsHomLift φ.1.base φ.1.b := by
        simpa using φ.1.b_over
      letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
        simpa using φ.1.a_over
      letI : (explicitTwoFibreProductLeftProjection G F).toFunctor.IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      have ha : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      have hbase : φ.1.base = 𝟙 f.left := by
        simpa [ha] using (IsHomLift.fac (Over.forget U) φ.1.base φ.1.a)
      simpa [hbase] using φ.1.b_over

/-- Helper for Lemma 4.42.1: a morphism in the outer fibre induces the corresponding morphism
between the right fibre objects appearing in the structured-arrow description. -/
private def fiberOfSliceTwoFibreProduct_right_fiber_hom
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P).right ⟶
      (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f Q).right :=
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩, φ =>
      letI : pX.IsHomLift (𝟙 f.left) φ.1.b :=
        fiberOfSliceTwoFibreProduct_right_over_id (G := G) (F := F) φ
      Fiber.homMk pX f.left φ.1.b

/-- Helper for Lemma 4.42.1: after strictifying the left slice component to `𝟙 f`, the
commutative square of a morphism in the explicit pullback becomes the structured-arrow triangle
in the fibre over `f.left`. -/
private theorem slice_two_fibre_product_fiber_structured_arrow_triangle
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P).hom ≫
        (F.fiberFunctor f.left).map
          (fiberOfSliceTwoFibreProduct_right_fiber_hom (G := G) (F := F) φ) =
      (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f Q).hom := by
  -- Strictify the left component to `𝟙 f` and then read `φ.1.comm.w` in the fibre of `pY`.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, xP, iP⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, xQ, iQ⟩⟩, rfl⟩, φ =>
      letI : (Over.forget U).IsHomLift φ.1.base φ.1.a := by
        simpa using φ.1.a_over
      letI : ((explicitTwoFibreProductLeftProjection G F).toFunctor).IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      have ha : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      have hg : G.toFunctor.map φ.1.a = 𝟙 _ := by
        rw [ha]
        exact Functor.map_id G.toFunctor f
      letI : pX.IsHomLift (𝟙 f.left) φ.1.b :=
        fiberOfSliceTwoFibreProduct_right_over_id (G := G) (F := F) φ
      let φright : xP ⟶ xQ := by
        simpa using (Fiber.homMk pX f.left φ.1.b)
      -- Compare the underlying morphisms in the fibre of `pY` after rewriting the left leg to
      -- `𝟙 f`.
      apply Functor.Fiber.hom_ext
      change
        fiberInclusion.map (iP.hom ≫ (F.fiberFunctor f.left).map φright) =
          fiberInclusion.map iQ.hom
      suffices
          fiberInclusion.map (iP.hom ≫ (F.fiberFunctor f.left).map φright) =
            G.toFunctor.map φ.1.a ≫ fiberInclusion.map iQ.hom by
        simpa [hg] using this
      simpa [ExplicitTwoFibreProductObject.comparison, φright] using φ.1.comm.w.symm

/-- Helper for Lemma 4.42.1: a morphism in the fibre of the left projection induces a morphism
between the corresponding structured arrows. -/
private def fiberOfSliceTwoFibreProduct_to_structuredArrow_map
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P ⟶
      fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f Q :=
  StructuredArrow.homMk
    (fiberOfSliceTwoFibreProduct_right_fiber_hom (G := G) (F := F) φ)
    (slice_two_fibre_product_fiber_structured_arrow_triangle (G := G) (F := F) φ)

/-- Helper for Lemma 4.42.1: the concrete inverse functor preserves identities. -/
private theorem fiberOfSliceTwoFibreProduct_to_structuredArrow_map_id
    [IsFibredInGroupoids pY]
    {f : Over U} (P : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) (𝟙 P) =
      𝟙 (fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f P) := by
  -- Normalize to the right fibre component and compare in the structured-arrow category.
  match P with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩ =>
      apply StructuredArrow.hom_ext
      apply Functor.Fiber.hom_ext
      rfl

/-- Helper for Lemma 4.42.1: the concrete inverse functor preserves composition. -/
private theorem fiberOfSliceTwoFibreProduct_to_structuredArrow_map_comp
    [IsFibredInGroupoids pY]
    {f : Over U}
    {P Q R : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) (φ ≫ ψ) =
      fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) φ ≫
        fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) ψ := by
  -- Normalize to the right fibre component and use that composition in the fibre is componentwise.
  match P, Q, R, φ, ψ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      ⟨⟨_, ⟨⟨_, rfl⟩, _, _⟩⟩, rfl⟩,
      φ, ψ =>
        apply StructuredArrow.hom_ext
        apply Functor.Fiber.hom_ext
        rfl

/-- Helper for Lemma 4.42.1: forgetting the redundant outer fibre equality gives the concrete
quasi-inverse from the fibre of the left projection to the structured-arrow category. -/
private def fiberOfSliceTwoFibreProduct_to_structuredArrow
    [IsFibredInGroupoids pY] (f : Over U) :
    ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f ⥤
      StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) where
  obj := fiberOfSliceTwoFibreProduct_to_structuredArrow_obj G F f
  map := fiberOfSliceTwoFibreProduct_to_structuredArrow_map G F
  map_id := fiberOfSliceTwoFibreProduct_to_structuredArrow_map_id G F
  map_comp := fiberOfSliceTwoFibreProduct_to_structuredArrow_map_comp G F

/-- Helper for Lemma 4.42.1: the canonical functor to the fibre followed by the concrete
quasi-inverse is the identity on the structured-arrow category. -/
private theorem sliceTwoFibreProductStructuredArrow_comp_inverse
    [IsFibredInGroupoids pY] (f : Over U) :
    sliceTwoFibreProductStructuredArrowToFiber G F f ⋙
        fiberOfSliceTwoFibreProduct_to_structuredArrow G F f =
      𝟭 (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)) := by
  -- Compare the right fibre morphisms componentwise and then transport the ordinary equality into
  -- the heterogeneous morphism clause required by `Functor.hext`.
  refine Functor.hext (fun A ↦ rfl) ?_
  intro A B α
  cases A
  cases B
  have hmap :
      (sliceTwoFibreProductStructuredArrowToFiber G F f ⋙
          fiberOfSliceTwoFibreProduct_to_structuredArrow G F f).map α =
        (𝟭
          (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl))
            (F.fiberFunctor f.left))).map α := by
    apply StructuredArrow.hom_ext
    apply Functor.Fiber.hom_ext
    rfl
  exact hmap ▸ HEq.rfl

/-- Helper for Lemma 4.42.1: rebuilding the explicit pullback object from a stored comparison
isomorphism replaces `i` by `asIso i.hom`, and these are definitionally the same isomorphism. -/
private theorem slice_two_fibre_product_rebuild_comparison_iso
    [IsFibredInGroupoids pY]
    {f : Over U} {x : pX.Fiber f.left}
    (i : (G.fiberFunctor f.left).obj (Fiber.mk rfl) ≅ (F.fiberFunctor f.left).obj x) :
    asIso i.hom = i := by
  -- Rebuilding from the stored comparison morphism does not change the underlying isomorphism.
  ext
  simp [asIso_hom]

/-- Helper for Lemma 4.42.1: the components of an equality morphism in the explicit
`2`-fibre product are the corresponding equality morphisms on the two fibre factors. -/
private theorem explicitTwoFibreProduct_eqToHom_components
    {P Q : ExplicitTwoFibreProductObject G F} (h : P = Q) :
    ((eqToHom h : P ⟶ Q).a = eqToHom (by cases h; rfl)) ∧
      ((eqToHom h : P ⟶ Q).b = eqToHom (by cases h; rfl)) := by
  -- Equality morphisms in the explicit pullback are defined componentwise.
  cases h
  constructor <;> rfl

/-- Helper for Lemma 4.42.1: forgetting an equality morphism in a fibre recovers the equality
morphism on the underlying ambient objects. -/
private theorem fiber_eqToHom_map
    {S : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber S}
    (h : P = Q) :
    fiberInclusion.map (eqToHom h) = eqToHom (congrArg Subtype.val h) := by
  -- The equality morphism in a fibre is defined by the same underlying ambient morphism.
  cases h
  rfl

/-- Helper for Lemma 4.42.1: the forward-then-backward composite fixes each object of the outer
fibre once the rebuilt comparison isomorphism is normalized back to the stored one. -/
private theorem fiberOfSliceTwoFibreProduct_comp_forward_obj
    [IsFibredInGroupoids pY]
    {f : Over U} (P : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
        sliceTwoFibreProductStructuredArrowToFiber G F f).obj P = P := by
  -- Unfold the composite object and rewrite the rebuilt comparison `asIso i.hom` back to `i`.
  match P with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, i⟩⟩, rfl⟩ =>
      -- Compare only the underlying explicit pullback object; the subtype proof is then irrelevant.
      apply Subtype.ext
      change
        (({ U := f.left
            obj :=
              { fst := Fiber.mk rfl
                snd := _
                iso := asIso i.hom } } :
            ExplicitTwoFibreProductObject G F) =
          { U := f.left
            obj :=
              { fst := Fiber.mk rfl
                snd := _
                iso := i } })
      rw [slice_two_fibre_product_rebuild_comparison_iso (G := G) (F := F) (f := f) i]

/-- Helper for Lemma 4.42.1: after normalizing the rebuilt comparison isomorphisms on objects,
the backward composite acts on morphisms by the original fibre morphism. -/
private theorem fiberOfSliceTwoFibreProduct_comp_forward_map_heq
    [IsFibredInGroupoids pY]
    {f : Over U} {P Q : ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f}
    (φ : P ⟶ Q) :
    (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
        sliceTwoFibreProductStructuredArrowToFiber G F f).map φ ≍ φ := by
  -- Route correction: first rewrite the `HEq` target into an ordinary conjugation statement using
  -- the normalized object equalities, then compare the explicit pullback morphisms componentwise.
  match P, Q, φ with
  | ⟨⟨_, ⟨⟨_, rfl⟩, _, iP⟩⟩, rfl⟩, ⟨⟨_, ⟨⟨_, rfl⟩, _, iQ⟩⟩, rfl⟩, φ =>
      have hP :
          (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
              sliceTwoFibreProductStructuredArrowToFiber G F f).obj
              ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iP } }, rfl⟩ =
            ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iP } }, rfl⟩ := by
        exact fiberOfSliceTwoFibreProduct_comp_forward_obj (G := G) (F := F)
          ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iP } }, rfl⟩
      have hQ :
          (fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
              sliceTwoFibreProductStructuredArrowToFiber G F f).obj
              ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iQ } }, rfl⟩ =
            ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iQ } }, rfl⟩ := by
        exact fiberOfSliceTwoFibreProduct_comp_forward_obj (G := G) (F := F)
          ⟨{ U := f.left, obj := { fst := Fiber.mk rfl, snd := _, iso := iQ } }, rfl⟩
      rw [← conj_eqToHom_iff_heq
        ((fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
            sliceTwoFibreProductStructuredArrowToFiber G F f).map φ)
        φ hP hQ]
      -- After forgetting to the ambient explicit pullback, the remaining comparison is ordinary
      -- equality of explicit pullback morphisms.
      apply Functor.Fiber.hom_ext
      rw [show
          fiberInclusion.map
              ((fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
                  sliceTwoFibreProductStructuredArrowToFiber G F f).map φ) =
            (sliceTwoFibreProductStructuredArrowToExplicit G F f).map
              (fiberOfSliceTwoFibreProduct_to_structuredArrow_map (G := G) (F := F) φ) by
        rfl]
      have hPa : (fiberInclusion.map (eqToHom hP)).a = 𝟙 f := by
        rw [fiber_eqToHom_map (G := G) (F := F) hP]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hP)).1
      have hPb : (fiberInclusion.map (eqToHom hP)).b = 𝟙 _ := by
        rw [fiber_eqToHom_map (G := G) (F := F) hP]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hP)).2
      have hQa : (fiberInclusion.map (eqToHom hQ.symm)).a = 𝟙 f := by
        rw [fiber_eqToHom_map (G := G) (F := F) hQ.symm]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hQ.symm)).1
      have hQb : (fiberInclusion.map (eqToHom hQ.symm)).b = 𝟙 _ := by
        rw [fiber_eqToHom_map (G := G) (F := F) hQ.symm]
        simpa using
          (explicitTwoFibreProduct_eqToHom_components
            (G := G) (F := F) (congrArg Subtype.val hQ.symm)).2
      letI : ((explicitTwoFibreProductLeftProjection G F).toFunctor).IsHomLift (𝟙 f) φ.1 := by
        simpa using φ.2
      letI : pX.IsHomLift (𝟙 f.left) φ.1.b :=
        fiberOfSliceTwoFibreProduct_right_over_id (G := G) (F := F) φ
      have hφa : φ.1.a = 𝟙 f := by
        simpa [explicitTwoFibreProductLeftProjection, explicitTwoFibreProduct] using
          (IsHomLift.fac' ((explicitTwoFibreProductLeftProjection G F).toFunctor) (𝟙 f) φ.1)
      apply ExplicitTwoFibreProductHom.ext
      · -- The left slice component is forced to be `𝟙 f`, so the conjugated comparison is a short
        -- identity computation in `Over U`.
        change
          𝟙 f =
            (fiberInclusion.map (eqToHom hP)).a ≫
              φ.1.a ≫ (fiberInclusion.map (eqToHom hQ.symm)).a
        rw [hPa, hQa, hφa]
        calc
          𝟙 f = 𝟙 f ≫ 𝟙 f := by simp
          _ = 𝟙 f ≫ 𝟙 f ≫ 𝟙 f := by simp
      · -- The right fibre component is the original fibre morphism, up to the identity
        -- conjugations coming from `hP` and `hQ`.
        change
          ((Fiber.homMk pX f.left φ.1.b).1) =
            (fiberInclusion.map (eqToHom hP)).b ≫
              φ.1.b ≫ (fiberInclusion.map (eqToHom hQ.symm)).b
        rw [hPb, hQb]
        calc
          (Fiber.homMk pX f.left φ.1.b).1 = φ.1.b := by rfl
          _ = 𝟙 _ ≫ φ.1.b := by simp
          _ = 𝟙 _ ≫ φ.1.b ≫ 𝟙 _ := by simp

/-- Helper for Lemma 4.42.1: the concrete quasi-inverse followed by the canonical functor back to
the outer fibre is the identity on that fibre. -/
private theorem fiberOfSliceTwoFibreProduct_comp_forward
    [IsFibredInGroupoids pY] (f : Over U) :
    fiberOfSliceTwoFibreProduct_to_structuredArrow G F f ⋙
        sliceTwoFibreProductStructuredArrowToFiber G F f =
      𝟭 (((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) := by
  -- Normalize the rebuilt comparison isomorphism and then compare fibre morphisms componentwise.
  refine Functor.hext
    (fun P ↦ fiberOfSliceTwoFibreProduct_comp_forward_obj (G := G) (F := F) P)
    ?_
  intro P Q φ
  -- The dependent map clause is handled separately so the final `Functor.hext` proof stays flat.
  exact fiberOfSliceTwoFibreProduct_comp_forward_map_heq (G := G) (F := F) φ

-- Proof sketch: an object of the fiber over `f : V ⟶ U` in the explicit `2`-fibre-product
-- already has left leg equal to `f`, so the remaining data are exactly an object
-- `x ∈ X_V` together with a morphism `G(f) ⟶ F(x)` in `Y_V`, i.e. a structured arrow from the
-- canonical fibre object `G(f)` to the induced fibre functor `F_V`.
/-- Lemma 4.42.1: for a functor `G : C/U ⥤ Y` over `C` and a functor `F : X ⥤ Y` over `C`, the
fiber over `f : V ⟶ U` of the explicit `2`-fibre-product projection
`(C/U) ×_Y X ⟶ C/U` is canonically equivalent to the structured-arrow category
`StructuredArrow (G(f)) (F_V)`, where `G(f)` is regarded as an object of `Y_V` and `F_V` is the
induced functor `X_V ⥤ Y_V`. Equivalently, its objects are pairs `(x, φ)` with `x ∈ X_V` and
`φ : G(f) ⟶ F(x)` in `Y_V`. -/
theorem sliceTwoFibreProductStructuredArrowToFiber_isEquivalence
    [IsFibredInGroupoids pY] (f : Over U) :
    (sliceTwoFibreProductStructuredArrowToFiber G F f).IsEquivalence := by
  -- Route correction: the source proof identifies the outer fibre by strictifying the fixed left
  -- projection to `f` and then forgetting the redundant equality.
  let H := fiberOfSliceTwoFibreProduct_to_structuredArrow G F f
  have hη :
      sliceTwoFibreProductStructuredArrowToFiber G F f ⋙ H =
        𝟭 (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left)) :=
    sliceTwoFibreProductStructuredArrow_comp_inverse G F f
  have hε :
      H ⋙ sliceTwoFibreProductStructuredArrowToFiber G F f =
        𝟭 (((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f) :=
    fiberOfSliceTwoFibreProduct_comp_forward G F f
  exact
    Functor.IsEquivalence.mk'
      H
      (eqToIso hη.symm)
      (eqToIso hε)

/-- The canonical equivalence in Lemma 4.42.1 between the structured-arrow category
`StructuredArrow (G(f)) (F_V)` and the fiber over `f` of the left projection
`(C/U) ×_Y X ⟶ C/U`. -/
noncomputable def sliceTwoFibreProductStructuredArrowEquivFiber
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ≌
      ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f :=
  letI : (sliceTwoFibreProductStructuredArrowToFiber G F f).IsEquivalence :=
    sliceTwoFibreProductStructuredArrowToFiber_isEquivalence G F f
  (sliceTwoFibreProductStructuredArrowToFiber G F f).asEquivalence

end SliceTwoFibreProductStructuredArrow

end CategoryTheory
