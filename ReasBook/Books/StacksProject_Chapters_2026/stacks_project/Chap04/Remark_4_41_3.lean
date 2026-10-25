module

public import stacks_project.Chap04.Example_4_37_1
public import stacks_project.Chap04.Definition_4_36_2
public import stacks_project.Chap04.Lemma_4_36_3
public import stacks_project.Chap04.Lemma_4_34_1
public import stacks_project.Chap04.Lemma_4_35_9
public import stacks_project.Chap04.Lemma_4_41_2_2_Yoneda_lemma

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u vW uW vX vY vZ uX uY uZ

namespace CategoryTheory

open BasedCategory
open Functor
open Opposite
open Pseudofunctor
open Pseudofunctor.CoGrothendieck
open scoped Bicategory

variable {C : Type v₁} [Category.{v₁} C]
variable {S : Type v₁} [Category.{v₁} S]

/- Domain-style sampling for Remark 4.41.3:
- primary domain: the `2`-Yoneda split model for a category fibred in groupoids over a fixed base.
- inspected owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `FibredInGroupoidsMor.ofBasedFunctor`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `BasedCategory.ofFunctor`,
  `Pseudofunctor.CoGrothendieck.forget`,
  `Pseudofunctor.CoGrothendieck.groupoidPresheafProjection_isFibredInGroupoids`.
- best owner abstraction: the split model is the bundled object
  `twoYonedaSplitModel p : FibredInGroupoidsOver C`, and the comparison to the original fibred
  category should be exposed by the owner morphism
  `twoYonedaSplitModel p ⟶ FibredInGroupoidsOver.ofFunctor p`, with equivalence expressed by
  `FibredInGroupoidsMor.IsEquivalenceOverBase`.
- primitive data: the groupoid-valued presheaf `twoYonedaGroupoidPresheaf p` and its
  co-Grothendieck projection.
- derived API: the bundled split model and the canonical owner morphism to
  `FibredInGroupoidsOver.ofFunctor p`.

Source/core/bridge triage:
- `source-facing`: the split model `S'` and the comparison functor `G : S' ⥤ S` from the remark.
- `core/canonical`: `FibredInGroupoidsOver C`, its owner homs `X ⟶ Y`, and
  `FibredInGroupoidsMor.IsEquivalenceOverBase`.
- `bridge/view`: the explicit co-Grothendieck presentation and the evaluation-at-identity formula
  for the underlying functor over `C`.
-/

abbrev twoYonedaSliceChange {U V : C} (f : U ⟶ V) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor (Over.forget V) :=
  { toFunctor := Over.map f
    w := Over.mapForget_eq f }

/-- The tautological slice arrow from the precomposed identity object over `U` to the identity
object over `V`. -/
private abbrev twoYonedaTautologicalSliceHom {U V : C} (f : U ⟶ V) :
    (twoYonedaSliceChange f).obj (Over.mk (𝟙 U)) ⟶ Over.mk (𝟙 V) :=
  Over.homMk
    (U := (twoYonedaSliceChange f).obj (Over.mk (𝟙 U)))
    (V := Over.mk (𝟙 V)) f (by simp [twoYonedaSliceChange])

def precomposeBasedFunctor
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (φ : X ⥤ᵇ Y) :
    (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) where
  obj F := BasedFunctor.comp φ F
  map τ := BasedCategory.whiskerLeft φ τ
  map_id := by
    intro F
    ext a
    simp [BasedCategory.whiskerLeft]
  map_comp := by
    intro F G H τ σ
    ext a
    simp [BasedCategory.whiskerLeft]

private def postcomposeBasedFunctor
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} (φ : Y ⥤ᵇ Z) :
    (X ⥤ᵇ Y) ⥤ (X ⥤ᵇ Z) where
  obj F := BasedFunctor.comp F φ
  map τ := BasedCategory.whiskerRight τ φ
  map_id := by
    intro F
    ext a
    simp [BasedCategory.whiskerRight]
  map_comp := by
    intro F G H τ σ
    ext a
    simp [BasedCategory.whiskerRight]

/-- Helper for Remark 4.41.3: two based functors are equal once their underlying functors agree.
-/
private theorem basedFunctor_ext
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {F G : X ⥤ᵇ Y} (h : F.toFunctor = G.toFunctor) :
    F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Helper for Remark 4.41.3: the component of an equality-induced morphism between based
functors is the corresponding equality-induced morphism on evaluated objects. -/
private theorem basedFunctor_eqToHom_app
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {F G : X ⥤ᵇ Y} (h : F = G) (a : X.obj) :
    (eqToHom h).app a = eqToHom (congrArg (fun H : X ⥤ᵇ Y ↦ H.obj a) h) := by
  -- Equality of based functors is strict, so its component at `a` is the corresponding objectwise
  -- transport.
  cases h
  rfl

/-- Helper for Remark 4.41.3: the slice-change based functor for `𝟙 U` is the identity based
functor on `C/U`. -/
private theorem twoYonedaSliceChange_id (U : C) :
    twoYonedaSliceChange (𝟙 U) = BasedFunctor.id (BasedCategory.ofFunctor (Over.forget U)) := by
  -- Forget to the underlying slice functor, where `Over.mapId_eq` is the strict identity law.
  apply basedFunctor_ext
  simpa [twoYonedaSliceChange, BasedFunctor.id] using Over.mapId_eq U

/-- Helper for Remark 4.41.3: slice change is strictly functorial under composition. -/
private theorem twoYonedaSliceChange_comp
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    twoYonedaSliceChange (f ≫ g) =
      BasedFunctor.comp (twoYonedaSliceChange f) (twoYonedaSliceChange g) := by
  -- Forget to the underlying slice functors and use `Over.mapComp_eq`.
  apply basedFunctor_ext
  simpa [twoYonedaSliceChange, BasedFunctor.comp] using Over.mapComp_eq f g

/-- Helper for Remark 4.41.3: precomposition by the identity based functor is the identity on the
category of based functors. -/
private theorem precomposeBasedFunctor_id
    {X : BasedCategory.{vX, uX} C} {Z : BasedCategory.{vZ, uZ} C} :
    precomposeBasedFunctor (BasedFunctor.id X) = 𝟭 (X ⥤ᵇ Z) := by
  -- Route correction: once the slice-change functor is identified strictly with the identity,
  -- precomposition is definitionally the identity on objects and whiskering by identities on
  -- morphisms.
  refine CategoryTheory.Functor.ext (fun F ↦ rfl) (fun F G τ ↦ ?_)
  ext a
  simp [precomposeBasedFunctor, BasedCategory.whiskerLeft]

/-- Helper for Remark 4.41.3: precomposition turns composition of based functors into composition
of precomposition functors in the opposite order. -/
private theorem precomposeBasedFunctor_comp
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} {W : BasedCategory.{vW, uW} C}
    (φ : X ⥤ᵇ Y) (ψ : Y ⥤ᵇ Z) :
    precomposeBasedFunctor (Z := W) (BasedFunctor.comp φ ψ) =
      (precomposeBasedFunctor (Z := W) ψ) ⋙ (precomposeBasedFunctor (Z := W) φ) := by
  -- Objectwise this is associativity of based-functor composition; on morphisms it is the
  -- corresponding associativity of left whiskering.
  refine CategoryTheory.Functor.ext (fun F ↦ rfl) (fun F G τ ↦ ?_)
  ext a
  simp [precomposeBasedFunctor, BasedCategory.whiskerLeft]

/-- Helper for Remark 4.41.3: postcomposition by the identity based functor is the identity on
the category of based functors. -/
private theorem postcomposeBasedFunctor_id
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C} :
    postcomposeBasedFunctor (X := X) (BasedFunctor.id Y) = 𝟭 (X ⥤ᵇ Y) := by
  -- Postcomposing by the identity does not change objects or morphisms.
  refine CategoryTheory.Functor.ext (fun F ↦ rfl) (fun F G τ ↦ ?_)
  ext a
  simp [postcomposeBasedFunctor, BasedCategory.whiskerRight]

/-- Helper for Remark 4.41.3: postcomposition turns composition of based functors into composition
of postcomposition functors in the usual order. -/
private theorem postcomposeBasedFunctor_comp
    {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
    {Z : BasedCategory.{vZ, uZ} C} {W : BasedCategory.{vW, uW} C}
    (φ : Y ⥤ᵇ Z) (ψ : Z ⥤ᵇ W) :
    postcomposeBasedFunctor (X := X) (BasedFunctor.comp φ ψ) =
      postcomposeBasedFunctor (X := X) φ ⋙ postcomposeBasedFunctor ψ := by
  -- Objectwise this is associativity of based-functor composition; on morphisms it is the
  -- corresponding associativity of right whiskering.
  refine CategoryTheory.Functor.ext (fun F ↦ rfl) (fun F G τ ↦ ?_)
  ext a
  simp [postcomposeBasedFunctor, BasedCategory.whiskerRight]

/-- Helper for Remark 4.41.3: the tautological slice morphism over `𝟙 U` is the identity of
`Over.mk (𝟙 U)`. -/
private theorem over_homMk_id (U : C) :
    Over.homMk (U := Over.mk (𝟙 U)) (V := Over.mk (𝟙 U)) (𝟙 U) (by simp) =
      𝟙 (Over.mk (𝟙 U)) := by
  apply Over.OverMorphism.ext
  simp

/-- Helper for Remark 4.41.3: the tautological slice morphism over a composite factors through the
intermediate slice object. -/
private theorem over_homMk_comp
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    Over.homMk (U := Over.mk (f ≫ g)) (V := Over.mk (𝟙 W)) (f ≫ g) (by simp) =
      Over.homMk (U := Over.mk (f ≫ g)) (V := Over.mk g) f (by simp) ≫
        Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 W)) g (by simp) := by
  apply Over.OverMorphism.ext
  simp

/-- Helper for Remark 4.41.3: the tautological slice morphism `Over.homMk f` is a lift of `f`
for the slice projection. -/
private theorem over_homMk_isHomLift
    {U V : C} (f : U ⟶ V) :
    (Over.forget V).IsHomLift f
      (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 V)) f (by simp)) := by
  -- The slice projection remembers exactly the underlying arrow in `C`.
  refine IsHomLift.of_fac' (Over.forget V) f
      (Over.homMk (U := Over.mk f) (V := Over.mk (𝟙 V)) f (by simp)) rfl rfl ?_
  simp

noncomputable instance
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    IsGroupoid (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) where
  all_isIso := by
    intro F G τ
    letI : ∀ a : Over U, IsIso (τ.toNatTrans.app a) := fun a ↦ by
      letI : p.IsHomLift (𝟙 ((Over.forget U).obj a)) (τ.toNatTrans.app a) := τ.isHomLift' a
      haveI :
          IsIso
            (Fiber.homMk p ((Over.forget U).obj a) (τ.toNatTrans.app a)) :=
        IsFibredInGroupoids.hom_isIso ((Over.forget U).obj a)
          (Fiber.homMk p ((Over.forget U).obj a) (τ.toNatTrans.app a))
      haveI : IsIso (τ.toNatTrans.app a) := by
        simpa using
          (inferInstance :
            IsIso
              (Fiber.fiberInclusion.map
                (Fiber.homMk p ((Over.forget U).obj a) (τ.toNatTrans.app a))))
      infer_instance
    let τ' : F.toFunctor ⟶ G.toFunctor := τ.toNatTrans
    have hτ : IsIso τ' := NatIso.isIso_of_isIso_app τ'
    letI := hτ
    exact BasedNatIso.isIso_of_toNatTrans_isIso τ

noncomputable instance (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    Groupoid (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :=
  Groupoid.ofIsGroupoid

noncomputable abbrev twoYonedaGroupoidPresheafValue
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :=
  Grpd.of (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p)

abbrev twoYonedaGroupoidPresheafMap
    (p : S ⥤ C) [IsFibredInGroupoids p] {U V : C} (f : U ⟶ V) :
    twoYonedaGroupoidPresheafValue p V ⥤
      twoYonedaGroupoidPresheafValue p U :=
  show twoYonedaGroupoidPresheafValue p V ⥤ twoYonedaGroupoidPresheafValue p U from
    precomposeBasedFunctor (twoYonedaSliceChange f)

-- Proof sketch: `Over.map (𝟙 U)` is naturally isomorphic to the identity on `C/U`, so
-- precomposition with it is naturally isomorphic to the identity on the over-base functor
-- category.
theorem twoYonedaGroupoidPresheafMap_id
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : Cᵒᵖ) :
    twoYonedaGroupoidPresheafMap p (𝟙 (unop U)) = 𝟭 _ := by
  -- Rewrite the slice-change functor to the identity and then use the generic precomposition law.
  calc
    twoYonedaGroupoidPresheafMap p (𝟙 (unop U)) =
        precomposeBasedFunctor (twoYonedaSliceChange (𝟙 (unop U))) := rfl
    _ = precomposeBasedFunctor (BasedFunctor.id (BasedCategory.ofFunctor (Over.forget (unop U)))) := by
      rw [twoYonedaSliceChange_id]
    _ = 𝟭 _ := precomposeBasedFunctor_id

-- Proof sketch: `Over.map` is functorial in the base morphism, so precomposition with
-- `Over.map ((f ≫ g).unop)` agrees with successive precomposition by `Over.map g.unop` and then
-- `Over.map f.unop`.
theorem twoYonedaGroupoidPresheafMap_comp
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    twoYonedaGroupoidPresheafMap p ((f ≫ g).unop) =
      twoYonedaGroupoidPresheafMap p f.unop ⋙
        twoYonedaGroupoidPresheafMap p g.unop := by
  -- Rewrite the slice change for `(f ≫ g).unop` to the iterated slice change and then use the
  -- generic contravariance of precomposition.
  simpa [twoYonedaGroupoidPresheafMap] using
    (calc
      precomposeBasedFunctor (twoYonedaSliceChange ((f ≫ g).unop)) =
          precomposeBasedFunctor
            (BasedFunctor.comp (twoYonedaSliceChange g.unop) (twoYonedaSliceChange f.unop)) := by
            rw [show (f ≫ g).unop = g.unop ≫ f.unop by rfl, twoYonedaSliceChange_comp]
      _ =
          precomposeBasedFunctor (twoYonedaSliceChange f.unop) ⋙
            precomposeBasedFunctor (twoYonedaSliceChange g.unop) := by
            simpa [BasedFunctor.comp] using
              (precomposeBasedFunctor_comp
                (W := BasedCategory.ofFunctor p)
                (φ := twoYonedaSliceChange g.unop)
                (ψ := twoYonedaSliceChange f.unop)))

/-- The contravariant groupoid-valued functor `U ↦ Mor_{Cat/C}(C/U, S)` attached to a category
fibred in groupoids `p : S ⥤ C`. -/
noncomputable def twoYonedaGroupoidPresheaf
    (p : S ⥤ C) [IsFibredInGroupoids p] : Cᵒᵖ ⥤ Grpd where
  obj U := twoYonedaGroupoidPresheafValue p (unop U)
  map f := twoYonedaGroupoidPresheafMap p f.unop
  map_id := twoYonedaGroupoidPresheafMap_id p
  map_comp := fun f g ↦ twoYonedaGroupoidPresheafMap_comp p f g

noncomputable abbrev twoYonedaCatPresheaf
    (p : S ⥤ C) [IsFibredInGroupoids p] :=
  twoYonedaGroupoidPresheaf p ⋙ Grpd.forgetToCat

noncomputable abbrev twoYonedaSplitCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :=
  CoGrothendieck ((twoYonedaCatPresheaf p).toPseudofunctor')

noncomputable abbrev twoYonedaSplitProjection
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitCategory p ⥤ C :=
  CoGrothendieck.forget ((twoYonedaCatPresheaf p).toPseudofunctor')

private noncomputable instance twoYonedaSplitProjection_instIsFibredInGroupoids
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    IsFibredInGroupoids (twoYonedaSplitProjection p) := by
  simpa [twoYonedaSplitProjection, twoYonedaCatPresheaf] using
    groupoidPresheafProjection_isFibredInGroupoids (twoYonedaGroupoidPresheaf p)

noncomputable abbrev twoYonedaSplitToOriginalObj
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitCategory p → S :=
  fun X ↦
      ((X.2 : BasedCategory.ofFunctor (Over.forget X.1) ⥤ᵇ BasedCategory.ofFunctor p)).obj
        (Over.mk (𝟙 X.1))

noncomputable abbrev twoYonedaSplitToOriginalMap
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p}
    (φ : X ⟶ Y) :
    twoYonedaSplitToOriginalObj p X ⟶ twoYonedaSplitToOriginalObj p Y :=
  ((φ.2 :
      (X.2 : BasedCategory.ofFunctor (Over.forget X.1) ⥤ᵇ BasedCategory.ofFunctor p) ⟶
        (twoYonedaGroupoidPresheafMap p φ.1).obj
          (Y.2 : BasedCategory.ofFunctor (Over.forget Y.1) ⥤ᵇ BasedCategory.ofFunctor p)).app
      (Over.mk (𝟙 X.1))) ≫
    ((Y.2 : BasedCategory.ofFunctor (Over.forget Y.1) ⥤ᵇ BasedCategory.ofFunctor p).map
      (Over.homMk φ.1))

/-- Helper for Remark 4.41.3: the tautological slice arrow over `𝟙 X.base` is sent by `X.fiber`
to the identity of the evaluated object. -/
private theorem twoYonedaSplit_identity_slice_map
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    X.2.map
        (Over.homMk (U := Over.mk (𝟙 X.1)) (V := Over.mk (𝟙 X.1)) (𝟙 X.1) (by simp)) =
      𝟙 (twoYonedaSplitToOriginalObj p X) := by
  -- Once the slice arrow is identified with the literal identity, functoriality of `X.fiber`
  -- turns it into the identity morphism on the evaluated object.
  rw [over_homMk_id]
  exact X.2.map_id (Over.mk (𝟙 X.1))

/-- Helper for Remark 4.41.3: precomposing the identity arrow of `X.base` along itself leaves the
tautological slice object unchanged. -/
private theorem twoYonedaSplit_identity_precomposed_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    (twoYonedaSliceChange (𝟙 X.1)).obj (Over.mk (𝟙 X.1)) = Over.mk (𝟙 X.1) := by
  -- The slice-change functor `Over.map (𝟙 X.base)` sends `id_X` to `id_X`.
  change Over.mk ((𝟙 X.1) ≫ 𝟙 X.1) = Over.mk (𝟙 X.1)
  simp

/-- Helper for Remark 4.41.3: evaluating the identity morphism in the split model at
`Over.mk (𝟙 X.base)` and then applying the tautological slice map gives the identity on
`X(𝟙 X.base)`. -/
private theorem twoYonedaSplit_identity_component_app
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber).app
        (Over.mk (𝟙 X.base))) ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).hom.toNatTrans.app
            X.fiber).app (Over.mk (𝟙 X.base))) =
      𝟙 (X.fiber.obj (Over.mk (𝟙 X.base))) := by
  -- Route correction: compute the CoGrothendieck identity component through the strict `mapId`
  -- transport and evaluate the owner identity `inv ≫ hom = 𝟙` at the tautological slice object.
  simpa using
    congrArg
      (fun τ ↦ τ.app (Over.mk (𝟙 X.base)))
      (Cat.Hom.inv_hom_id_toNatTrans_app
        (((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩))
        X.fiber)

/-- Helper for Remark 4.41.3: naturality of the fiber component `ψ.2` at the tautological slice
morphism over `φ.1`. -/
private theorem twoYonedaSplit_naturality_over_homMk
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Y.2.map (Over.homMk (U := Over.mk φ.1) (V := Over.mk (𝟙 Y.1)) φ.1 (by simp)) ≫
        ψ.2.app (Over.mk (𝟙 Y.1)) =
      ψ.2.app (Over.mk φ.1) ≫
        (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.1.op.toLoc).toFunctor.obj Z.2).map
          (Over.homMk (U := Over.mk φ.1) (V := Over.mk (𝟙 Y.1)) φ.1 (by simp)) := by
  -- This is the naturality equation needed to move the middle evaluation from `Over.mk φ.1` back
  -- to `Over.mk (𝟙 Y.1)`.
  exact
    ψ.2.naturality (Over.homMk (U := Over.mk φ.1) (V := Over.mk (𝟙 Y.1)) φ.1 (by simp))

/-- Helper for Remark 4.41.3: precomposing the identity object of `C/X.base` along `φ.base`
produces the slice object classified by `φ.base`. -/
private theorem twoYonedaSplit_precomposed_identity_obj
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    (twoYonedaSliceChange φ.base).obj (Over.mk (𝟙 X.base)) = Over.mk φ.base := by
  -- `Over.map φ.base` sends `id_X` to the arrow `𝟙 X ≫ φ.base = φ.base`.
  change Over.mk ((𝟙 X.base) ≫ φ.base) = Over.mk φ.base
  simp

/-- Helper for Remark 4.41.3: the raw tautological slice arrow attached to `φ.base` factors
through the explicit transport from the precomposed identity object to `Over.mk φ.base`. -/
private theorem twoYonedaSplit_raw_slice_tail
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    Y.fiber.map (Over.homMk φ.base) =
      Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
        Y.fiber.map
          (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
            φ.base (by simp)) := by
  -- Reduce the omitted source object of `Over.homMk φ.base` to the literal slice object
  -- `Over.mk φ.base`, then apply functoriality of `Y.fiber`.
  cases X with
  | mk U FX =>
      cases Y with
      | mk V FY =>
          have hMor :
              Over.homMk (U := Over.mk ((𝟙 U) ≫ φ.base)) (V := Over.mk (𝟙 V)) φ.base (by simp) =
                eqToHom (show Over.mk ((𝟙 U) ≫ φ.base) = Over.mk φ.base by simp) ≫
                  Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 V)) φ.base (by simp) := by
            apply Over.OverMorphism.ext
            simp
          calc
            FY.map (Over.homMk φ.base) =
                FY.map
                  (eqToHom (show Over.mk ((𝟙 U) ≫ φ.base) = Over.mk φ.base by simp) ≫
                    Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 V)) φ.base (by simp)) := by
              exact congrArg FY.map hMor
            _ =
                FY.map (eqToHom (show Over.mk ((𝟙 U) ≫ φ.base) = Over.mk φ.base by simp)) ≫
                  FY.map
                    (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 V)) φ.base (by simp)) := by
              exact FY.map_comp _ _

/-- Helper for Remark 4.41.3: the base arrow underlying the tautological slice map over
`𝟙 X.base` composes to `𝟙 X.base`. -/
private theorem twoYonedaSplit_identity_base_comp
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    (𝟙 X.base) ≫ (𝟙 X.base) = 𝟙 X.base := by
  -- This is the strict identity law in the base category.
  simp

/-- Helper for Remark 4.41.3: evaluating `X.fiber` on the identity-precomposition object yields
the same object as evaluation at the tautological slice `Over.mk (𝟙 X.base)`. -/
private theorem twoYonedaSplit_identity_precomposed_obj_image
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    X.fiber.obj ((twoYonedaSliceChange (𝟙 X.base)).obj (Over.mk (𝟙 X.base))) =
      twoYonedaSplitToOriginalObj p X := by
  -- This is the objectwise image of `twoYonedaSplit_identity_precomposed_obj`.
  simpa [twoYonedaSplitToOriginalObj] using
    congrArg X.fiber.obj (twoYonedaSplit_identity_precomposed_obj p X)

/-- Helper for Remark 4.41.3: the strict action of the `2`-Yoneda presheaf on the identity
base map fixes the chosen fiber object `X.fiber`. -/
private theorem twoYonedaSplit_identity_action_on_fiber
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    ((twoYonedaCatPresheaf p).toPseudofunctor'.map (𝟙 ⟨op X.base⟩)).toFunctor.obj X.fiber =
      X.fiber := by
  -- The underlying contravariant functor is strictly unital, so evaluating it at `X.fiber`
  -- yields the identity based functor.
  simpa [twoYonedaCatPresheaf, twoYonedaGroupoidPresheafMap, precomposeBasedFunctor,
    twoYonedaSliceChange] using
    congrArg (fun F ↦ F.obj X.fiber) (twoYonedaGroupoidPresheafMap_id p ⟨op X.base⟩)

/-- Helper for Remark 4.41.3: the `mapId.hom` transport of `Functor.toPseudofunctor'`, evaluated
at the tautological slice object, is the objectwise equality transport coming from the strict
identity action on `X.fiber`. -/
private theorem twoYonedaSplit_mapId_hom_app_eqToHom
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).hom.toNatTrans.app X.fiber).app
        (Over.mk (𝟙 X.base))) =
      X.fiber.map (eqToHom (twoYonedaSplit_identity_precomposed_obj p X)) := by
  -- Unfold `Functor.toPseudofunctor'` only once: the `mapId.hom` component is exactly the
  -- equality transport coming from strict unitality of the presheaf action on `X.fiber`.
  cases X with
  | mk U FX =>
      simpa [Functor.toPseudofunctor', twoYonedaCatPresheaf, twoYonedaSliceChange,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_map] using
        (basedFunctor_eqToHom_app
          (twoYonedaSplit_identity_action_on_fiber p { base := U, fiber := FX })
          (Over.mk (𝟙 U)))

/-- Helper for Remark 4.41.3: the `mapId.hom` transport of `Functor.toPseudofunctor'`, evaluated
at the tautological slice object, is exactly the transported identity slice morphism. -/
private theorem twoYonedaSplit_mapId_hom_app_at_tautological_slice
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).hom.toNatTrans.app X.fiber).app
        (Over.mk (𝟙 X.base))) =
        X.fiber.map (eqToHom (twoYonedaSplit_identity_precomposed_obj p X)) ≫
        X.fiber.map
          (Over.homMk (U := Over.mk (𝟙 X.base)) (V := Over.mk (𝟙 X.base))
            (𝟙 X.base) (twoYonedaSplit_identity_base_comp p X)) := by
  -- Unfold `Functor.toPseudofunctor'`: its `mapId` component is the strict `eqToIso (by simp)`
  -- comparison, so evaluating at `X.fiber` and then at `Over.mk (𝟙 X.base)` yields the
  -- transported identity slice map on the nose.
  calc
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).hom.toNatTrans.app X.fiber).app
        (Over.mk (𝟙 X.base))) =
        X.fiber.map (eqToHom (twoYonedaSplit_identity_precomposed_obj p X)) :=
      twoYonedaSplit_mapId_hom_app_eqToHom p X
    _ =
        X.fiber.map (eqToHom (twoYonedaSplit_identity_precomposed_obj p X)) ≫
          X.fiber.map
            (Over.homMk (U := Over.mk (𝟙 X.base)) (V := Over.mk (𝟙 X.base))
              (𝟙 X.base) (twoYonedaSplit_identity_base_comp p X)) := by
      rw [twoYonedaSplit_identity_slice_map p X]
      symm
      exact Category.comp_id (X.fiber.map (eqToHom (twoYonedaSplit_identity_precomposed_obj p X)))

/-- Helper for Remark 4.41.3: the raw tautological slice arrow for the identity morphism factors
through the object-transport from identity precomposition, followed by the literal identity slice
arrow on `Over.mk (𝟙 X.base)`. -/
private theorem twoYonedaSplit_identity_raw_slice_tail
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    X.fiber.map (twoYonedaTautologicalSliceHom (𝟙 X.base)) =
      X.fiber.map (eqToHom (twoYonedaSplit_identity_precomposed_obj p X)) ≫
        X.fiber.map
          (Over.homMk (U := Over.mk (𝟙 X.base)) (V := Over.mk (𝟙 X.base))
            (𝟙 X.base) (twoYonedaSplit_identity_base_comp p X)) := by
  -- After reducing the source slice object of `Over.homMk (𝟙 X.base)`, this is just the functorial
  -- image of the strict factorization of that arrow through the identity slice object.
  cases X with
  | mk U FX =>
      have hMor :
          twoYonedaTautologicalSliceHom (𝟙 U) =
            eqToHom (show Over.mk ((𝟙 U) ≫ 𝟙 U) = Over.mk (𝟙 U) by simp) ≫
              Over.homMk (U := Over.mk (𝟙 U)) (V := Over.mk (𝟙 U)) (𝟙 U) (by simp) := by
        apply Over.OverMorphism.ext
        simp [twoYonedaTautologicalSliceHom, twoYonedaSliceChange]
      calc
        FX.map (twoYonedaTautologicalSliceHom (𝟙 U)) = FX.map
            (eqToHom (show Over.mk ((𝟙 U) ≫ 𝟙 U) = Over.mk (𝟙 U) by simp) ≫
              Over.homMk (U := Over.mk (𝟙 U)) (V := Over.mk (𝟙 U)) (𝟙 U) (by simp)) := by
          exact congrArg FX.map hMor
        _ =
            FX.map (eqToHom (show Over.mk ((𝟙 U) ≫ 𝟙 U) = Over.mk (𝟙 U) by simp)) ≫
              FX.map (Over.homMk (U := Over.mk (𝟙 U)) (V := Over.mk (𝟙 U)) (𝟙 U) (by simp)) := by
          exact FX.map_comp _ _

/-- Helper for Remark 4.41.3: the underlying comparison map on the identity morphism in the split
model is the evaluated `mapId.inv` component followed by the tautological slice map. -/
private theorem twoYonedaSplit_identity_map_at_tautological_slice
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    twoYonedaSplitToOriginalMap p (𝟙 X) =
      ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber).app
          (Over.mk (𝟙 X.base))) ≫
        X.fiber.map (twoYonedaTautologicalSliceHom (𝟙 X.base)) := by
  -- This is the exact owner-level normal form obtained by unfolding the CoGrothendieck identity
  -- and the evaluation-at-identity comparison map.
  rfl

theorem twoYonedaSplitToOriginalUnderlying_map_id
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∀ X : twoYonedaSplitCategory p,
      twoYonedaSplitToOriginalMap p (𝟙 X) =
        𝟙 (twoYonedaSplitToOriginalObj p X) := by
  intro X
  -- Route correction: insert the identity-precomposition transport so the raw tautological slice
  -- map becomes exactly the `mapId.hom` component handled by the already-proved unit equation.
  rw [twoYonedaSplit_identity_map_at_tautological_slice]
  have hTail :
      X.fiber.map (twoYonedaTautologicalSliceHom (𝟙 X.base)) =
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).hom.toNatTrans.app
            X.fiber).app (Over.mk (𝟙 X.base))) := by
    exact
      (twoYonedaSplit_identity_raw_slice_tail p X).trans
        (twoYonedaSplit_mapId_hom_app_at_tautological_slice p X).symm
  change
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber).app
          (Over.mk (𝟙 X.base))) ≫
        X.fiber.map (twoYonedaTautologicalSliceHom (𝟙 X.base)) =
      𝟙 (X.fiber.obj (Over.mk (𝟙 X.base)))
  erw [hTail]
  simpa [Category.assoc] using
    twoYonedaSplit_identity_component_app p X

/-- Helper for Remark 4.41.3: successive precomposition of `id_X` by `φ.base` and `ψ.base`
produces the slice object classified by `φ.base ≫ ψ.base`. -/
private theorem twoYonedaSplit_precomposed_composite_obj
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (Over.map ψ.base).obj ((Over.map φ.base).obj (Over.mk (𝟙 X.base))) =
      Over.mk (φ.base ≫ ψ.base) := by
  -- Repeated postcomposition carries `id_X` to the composite `φ.base ≫ ψ.base`.
  change Over.mk (((𝟙 X.base) ≫ φ.base) ≫ ψ.base) = Over.mk (φ.base ≫ ψ.base)
  simp

/-- Helper for Remark 4.41.3: precomposing `id_X` directly by the composite `φ.base ≫ ψ.base`
produces the slice object classified by that composite. -/
private theorem twoYonedaSplit_precomposed_composite_direct_obj
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (twoYonedaSliceChange (φ.base ≫ ψ.base)).obj (Over.mk (𝟙 X.base)) =
      Over.mk (φ.base ≫ ψ.base) := by
  -- Direct precomposition by the composite sends `id_X` to `φ.base ≫ ψ.base`.
  change Over.mk ((𝟙 X.base) ≫ (φ.base ≫ ψ.base)) = Over.mk (φ.base ≫ ψ.base)
  simp

/-- Helper for Remark 4.41.3: the based-functor compatibility of `Y.fiber` computes the base
projection of the tautological slice arrow over `φ.base`. -/
private theorem twoYonedaSplit_base_map_over_homMk
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    p.map
        (Y.2.map
          (Over.homMk (U := Over.mk φ.1) (V := Over.mk (𝟙 Y.1)) φ.1 (by simp))) =
      eqToHom (Y.2.w_obj (Over.mk φ.1)) ≫
        φ.1 ≫
          eqToHom (Y.2.w_obj (Over.mk (𝟙 Y.1))).symm := by
  -- The source and target object equalities are exactly the `w_obj` identities for `Y.2`.
  simpa using
    Functor.congr_hom Y.2.w
      (Over.homMk (U := Over.mk φ.1) (V := Over.mk (𝟙 Y.1)) φ.1 (by simp))

/-- Helper for Remark 4.41.3: the strict action of the `2`-Yoneda presheaf on a composite base
map agrees with iterated action on `Z.fiber`. -/
private theorem twoYonedaSplit_composite_action_on_fiber
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ((twoYonedaCatPresheaf p).toPseudofunctor'.map (ψ.base.op.toLoc ≫ φ.base.op.toLoc)).toFunctor.obj
        Z.fiber =
      ((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
        (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber) := by
  -- Strict functoriality of the underlying presheaf identifies direct precomposition by
  -- `φ.base ≫ ψ.base` with iterated precomposition by `ψ.base` and then `φ.base`.
  simpa [twoYonedaCatPresheaf, twoYonedaGroupoidPresheafMap, precomposeBasedFunctor,
    twoYonedaSliceChange] using
    congrArg (fun F ↦ F.obj Z.fiber) (twoYonedaGroupoidPresheafMap_comp p ψ.base.op φ.base.op)

/-- Helper for Remark 4.41.3: the `mapComp.inv` transport identifies the two-step precomposition
object with the direct precomposition object at `Over.mk (𝟙 X.base)`. -/
private theorem twoYonedaSplit_mapComp_inv_app_eq
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
        Z.fiber).app (Over.mk (𝟙 X.base))) ≫
        Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)) =
      Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_obj p φ ψ)) := by
  cases X with
  | mk U FX =>
      cases Y with
      | mk V FY =>
          cases Z with
          | mk W FZ =>
              -- Unfold `Functor.toPseudofunctor'` at the tautological slice object: the
              -- `mapComp.inv` component is the objectwise transport from iterated to direct
              -- precomposition.
              let hObj :
                  (((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
                      (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                        FZ)).obj (Over.mk (𝟙 U)) =
                    (((twoYonedaCatPresheaf p).toPseudofunctor'.map
                        (ψ.base.op.toLoc ≫ φ.base.op.toLoc)).toFunctor.obj FZ).obj
                      (Over.mk (𝟙 U)) :=
                congrArg
                  (fun H : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p ↦
                    H.obj (Over.mk (𝟙 U)))
                  (twoYonedaSplit_composite_action_on_fiber p φ ψ).symm
              have hApp :
                  ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc
                      φ.base.op.toLoc).inv.toNatTrans.app FZ).app (Over.mk (𝟙 U))) =
                    eqToHom hObj := by
                simpa [Functor.toPseudofunctor', twoYonedaCatPresheaf, twoYonedaSliceChange,
                  Cat.Hom₂.eqToHom_toNatTrans, eqToHom_map] using
                  (basedFunctor_eqToHom_app
                    (F := ((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
                      (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                        FZ))
                    (G := ((twoYonedaCatPresheaf p).toPseudofunctor'.map
                      (ψ.base.op.toLoc ≫ φ.base.op.toLoc)).toFunctor.obj FZ)
                    (h := (twoYonedaSplit_composite_action_on_fiber p φ ψ).symm)
                    (a := Over.mk (𝟙 U)))
              have hTrans :
                  hObj.trans
                      (congrArg FZ.obj
                        (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)) =
                    congrArg FZ.obj (twoYonedaSplit_precomposed_composite_obj p φ ψ) := by
                simp [twoYonedaCatPresheaf]
              rw [hApp]
              change eqToHom hObj ≫
                  FZ.toFunctor.map (eqToHom (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)) =
                FZ.toFunctor.map (eqToHom (twoYonedaSplit_precomposed_composite_obj p φ ψ))
              rw [eqToHom_map, eqToHom_map]
              change eqToHom hObj ≫
                  eqToHom
                    (congrArg FZ.obj (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)) =
                eqToHom (congrArg FZ.obj (twoYonedaSplit_precomposed_composite_obj p φ ψ))
              rw [← hTrans]
              exact
                (eqToHom_trans hObj
                  (congrArg FZ.obj (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)))

/-- Helper for Remark 4.41.3: evaluating the twice-precomposed fiber object at `Over.mk (𝟙 X)`
is the same as evaluating the once-precomposed fiber object at `Over.mk φ`. -/
private theorem twoYonedaSplit_iterated_precomposition_obj
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
        (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber)).obj
        (Over.mk (𝟙 X.base))) =
      (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber).obj
        (Over.mk φ.base) := by
  -- This is the objectwise form of the statement that `Over.map φ.base` sends `id_X` to `φ.base`.
  simpa [twoYonedaCatPresheaf, twoYonedaGroupoidPresheafMap, precomposeBasedFunctor,
    twoYonedaSliceChange] using
    congrArg
      (fun a : Over Y.base ↦
        (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber).obj
          a)
      (twoYonedaSplit_precomposed_identity_obj p φ)

/-- Helper for Remark 4.41.3: whiskering `ψ.fiber` along the slice-change for `φ.base`, then
evaluating at the tautological slice object of `X`, is the same as evaluating `ψ.fiber` at the
slice object classified by `φ.base`, with the canonical object transport inserted explicitly. -/
private theorem twoYonedaSplit_mapped_component_app_at_identity_normal_form
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber).app
        (Over.mk (𝟙 X.base))) =
      eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
        ψ.fiber.app (Over.mk φ.base) ≫
          eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm := by
  -- Evaluate the whiskered component at `Over.mk (𝟙 X.base)`, then rewrite it by naturality along
  -- the equality identifying the precomposed slice object with `Over.mk φ.base`.
  apply (cancel_mono (eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ))).1
  calc
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber).app
        (Over.mk (𝟙 X.base))) ≫
        eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ) =
      ψ.fiber.app ((Over.map φ.base).obj (Over.mk (𝟙 X.base))) ≫
        eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ) := by
      rfl
    _ =
      eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
        ψ.fiber.app (Over.mk φ.base) := by
      simpa [Category.assoc, eqToHom_map] using
        (ψ.fiber.naturality (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ))).symm
    _ =
      (eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
          ψ.fiber.app (Over.mk φ.base) ≫
            eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm) ≫
        eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ) := by
      simp [Category.assoc]

/-- Helper for Remark 4.41.3: after inserting the explicit source transport from
`twoYonedaSplit_raw_slice_tail`, the remaining comparison with `ψ` is exactly the naturality
square of `ψ.fiber` under the tautological slice morphism over `φ.base`. -/
private theorem twoYonedaSplit_map_comp_naturality_tail
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ((Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
        Y.fiber.map
          (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
            φ.base (by simp))) ≫
        ψ.fiber.app (Over.mk (𝟙 Y.base))) =
        Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
          ψ.fiber.app (Over.mk φ.base) ≫
            (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                Z.fiber).map
              (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
                φ.base (by simp)) := by
  -- This is exactly the naturality square of `ψ.fiber`, with the already-isolated transport from
  -- `twoYonedaSplit_raw_slice_tail` left untouched on the outside.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫ k)
      (twoYonedaSplit_naturality_over_homMk (p := p) (φ := φ) (ψ := ψ))

/-- Helper for Remark 4.41.3: in the precomposed slice over `Z`, the tautological slice morphism
over `φ.base` followed by the tautological slice morphism over `ψ.base` is exactly the
tautological slice morphism over `φ.base ≫ ψ.base`. -/
private theorem twoYonedaSplit_precomposed_slice_tail
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber).map
        (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
          φ.base (by simp))) ≫
      Z.fiber.map
        (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
          ψ.base (by simp)) =
    Z.fiber.map
      (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
        (φ.base ≫ ψ.base) (by simp)) := by
  -- Unfold the precomposition action once and then identify the composite of tautological slice
  -- arrows by extensionality in the slice category.
  rw [show
      ((((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber).map
          (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
            φ.base (by simp))) =
        Z.fiber.map
          ((Over.map ψ.base).map
            (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
              φ.base (by simp))) by
        rfl]
  have hComp :
      Z.fiber.map
          ((Over.map ψ.base).map
            (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
              φ.base (by simp))) ≫
        Z.fiber.map
          (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
            ψ.base (by simp)) =
      Z.fiber.map
        (((Over.map ψ.base).map
            (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
              φ.base (by simp))) ≫
          Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
            ψ.base (by simp)) := by
    simpa using
      (Z.fiber.map_comp
        ((Over.map ψ.base).map
          (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
            φ.base (Category.comp_id φ.base)))
        (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
          ψ.base ((Category.comp_id ψ.base).trans (Category.id_comp ψ.base).symm))).symm
  exact hComp.trans <| by
    exact congrArg Z.fiber.map <| by
      apply Over.OverMorphism.ext
      rfl

/-- Helper for Remark 4.41.3: evaluating the three composable pseudonatural-transformation
components at the tautological slice object is strict pointwise composition. -/
private theorem twoYonedaSplit_map_comp_component_app
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ.fiber ≫
        ((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
          Z.fiber))).app (Over.mk (𝟙 X.base)) =
      φ.fiber.app (Over.mk (𝟙 X.base)) ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber).app
          (Over.mk (𝟙 X.base))) ≫
          ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
            Z.fiber).app (Over.mk (𝟙 X.base))) := by
  -- This is the strict `comp_app` formula for the three pointwise components.
  rfl

/-- Helper for Remark 4.41.3: the raw tautological slice arrow for `φ.base ≫ ψ.base` factors
through the literal slice object `Over.mk (φ.base ≫ ψ.base)`. -/
private theorem twoYonedaSplit_composite_raw_slice_tail
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Z.fiber.map (Over.homMk (φ.base ≫ ψ.base)) =
      Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)) ≫
        Z.fiber.map
          (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
            (φ.base ≫ ψ.base) (by simp)) := by
  -- Reduce the omitted source object of the raw tautological slice arrow to the literal source
  -- `Over.mk (φ.base ≫ ψ.base)` and then apply functoriality of `Z.fiber`.
  cases X with
  | mk U FX =>
      cases Y with
      | mk V FY =>
          cases Z with
          | mk W FZ =>
              have hMor :
                  Over.homMk (U := Over.mk ((𝟙 U) ≫ (φ.base ≫ ψ.base))) (V := Over.mk (𝟙 W))
                      (φ.base ≫ ψ.base) (by simp) =
                    eqToHom
                      (show Over.mk ((𝟙 U) ≫ (φ.base ≫ ψ.base)) = Over.mk (φ.base ≫ ψ.base) by
                        simp) ≫
                      Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 W))
                        (φ.base ≫ ψ.base) (by simp) := by
                apply Over.OverMorphism.ext
                simp
              calc
                FZ.map (Over.homMk (φ.base ≫ ψ.base)) =
                  FZ.map
                    (eqToHom
                      (show Over.mk ((𝟙 U) ≫ (φ.base ≫ ψ.base)) = Over.mk (φ.base ≫ ψ.base) by
                        simp) ≫
                      Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 W))
                        (φ.base ≫ ψ.base) (by simp)) := by
                  exact congrArg FZ.map hMor
                _ =
                    FZ.map
                      (eqToHom
                        (show Over.mk ((𝟙 U) ≫ (φ.base ≫ ψ.base)) = Over.mk (φ.base ≫ ψ.base) by
                          simp)) ≫
                      FZ.map
                        (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 W))
                          (φ.base ≫ ψ.base) (by simp)) := by
                  exact FZ.map_comp _ _

/-- Helper for Remark 4.41.3: the transport from the iterated precomposition object to the
literal composite slice object cancels after applying `Z.fiber`. -/
private theorem twoYonedaSplit_iterated_transport_cancel
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm ≫
      Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_obj p φ ψ)) =
        𝟙 (((((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
          Z.fiber).obj (Over.mk φ.base))) := by
  -- The object equality transported by `mapComp.inv` is exactly the equality already recorded in
  -- `twoYonedaSplit_iterated_precomposition_obj`, so the two transports cancel.
  rw [eqToHom_map]
  have hComp :
      (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm.trans
          (congrArg Z.fiber.obj (twoYonedaSplit_precomposed_composite_obj p φ ψ)) = rfl := by
    apply Subsingleton.elim
  calc
    eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm ≫
        eqToHom (congrArg Z.fiber.obj (twoYonedaSplit_precomposed_composite_obj p φ ψ)) =
      eqToHom
        ((twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm.trans
          (congrArg Z.fiber.obj (twoYonedaSplit_precomposed_composite_obj p φ ψ))) := by
        rw [eqToHom_trans]
    _ = eqToHom rfl := by
      cases hComp
      rfl
    _ = 𝟙 _ := by
      simp

/-- Helper for Remark 4.41.3: the comparison map on a composite in the split model unfolds to the
expected CoGrothendieck composite evaluated at the tautological slice object. -/
private theorem twoYonedaSplitToOriginal_map_comp_left_expansion
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    twoYonedaSplitToOriginalMap p (φ ≫ ψ) =
      (φ ≫ ψ).fiber.app (Over.mk (𝟙 X.base)) ≫
        Z.fiber.map (twoYonedaTautologicalSliceHom (φ ≫ ψ).base) := by
  -- This is the defining formula for `twoYonedaSplitToOriginalMap` specialized to a composite
  -- morphism in the split model.
  rfl

/-- Helper for Remark 4.41.3: after postcomposing with the tautological slice map over `ψ.base`,
the middle tail of `map_comp` is exactly the naturality square of `ψ.fiber`. -/
private theorem twoYonedaSplit_map_comp_tail_after_naturality
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    φ.fiber.app (Over.mk (𝟙 X.base)) ≫
      Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
        ψ.fiber.app (Over.mk φ.base) ≫
          (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj Z.fiber).map
            (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base)) φ.base (by simp)) ≫
          Z.fiber.map
            (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
              ψ.base (by simp)) =
      φ.fiber.app (Over.mk (𝟙 X.base)) ≫
        ((Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
          Y.fiber.map
            (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
              φ.base (by simp))) ≫
          ψ.fiber.app (Over.mk (𝟙 Y.base))) ≫
          Z.fiber.map
            (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
              ψ.base (by simp)) := by
  -- This is exactly `twoYonedaSplit_map_comp_naturality_tail`, postcomposed by the final
  -- tautological slice morphism over `ψ.base` and reassociated.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ φ.fiber.app (Over.mk (𝟙 X.base)) ≫ k ≫
        Z.fiber.map
          (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
            ψ.base ((Category.comp_id ψ.base).trans (Category.id_comp ψ.base).symm)))
      (twoYonedaSplit_map_comp_naturality_tail (p := p) (φ := φ) (ψ := ψ)).symm

/-- Helper for Remark 4.41.3: the left-hand side of `map_comp` first reduces to the explicit
normal form obtained by evaluating the pointwise composite at `Over.mk (𝟙 X.base)` and then
rewriting the whiskered middle component by its tautological-slice formula. -/
private theorem twoYonedaSplit_map_comp_first_normal_form
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ.fiber ≫
        ((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
          Z.fiber))).app (Over.mk (𝟙 X.base)) ≫
      Z.fiber.map
        (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ (φ.base ≫ ψ.base))) (V := Over.mk (𝟙 Z.base))
          (φ.base ≫ ψ.base) (by simp)) =
      (φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          (eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm) ≫
            ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
              Z.fiber).app (Over.mk (𝟙 X.base)))) ≫
        Z.fiber.map
          (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ (φ.base ≫ ψ.base))) (V := Over.mk (𝟙 Z.base))
            (φ.base ≫ ψ.base) (by simp)) := by
  -- This is the stable prefix of the `map_comp` rewrite chain: first expose pointwise
  -- composition, then replace the whiskered middle component by the explicit tautological-slice
  -- evaluation formula.
  rw [twoYonedaSplit_map_comp_component_app, twoYonedaSplit_mapped_component_app_at_identity_normal_form]
  rfl

/-- Helper for Remark 4.41.3: once the fixed prefix of the `map_comp` comparison is in place, the
remaining composite slice tail can be rewritten using the literal two-step precomposed slice tail.
-/
private theorem twoYonedaSplit_prefixed_precomposed_slice_tail
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    φ.fiber.app (Over.mk (𝟙 X.base)) ≫
      Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
        ψ.fiber.app (Over.mk φ.base) ≫
          Z.fiber.map
            (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
              (φ.base ≫ ψ.base) (by simp)) =
      φ.fiber.app (Over.mk (𝟙 X.base)) ≫
        Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
          ψ.fiber.app (Over.mk φ.base) ≫
            (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                Z.fiber).map
              (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
                φ.base (by simp)) ≫
            Z.fiber.map
              (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                ψ.base (by simp)) := by
  -- Pull the verified prefix out of the way and apply the dedicated precomposed-slice comparison.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫ k)
      (twoYonedaSplit_precomposed_slice_tail (p := p) (φ := φ) (ψ := ψ)).symm

/-- Helper for Remark 4.41.3: the final owner-level composite in the split-model comparison
reassociates to the iterated evaluation expression on the right-hand side of `map_comp`. -/
private theorem twoYonedaSplit_map_comp_reassociation
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y Z : twoYonedaSplitCategory p} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ.fiber ≫
        ((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
          Z.fiber))).app (Over.mk (𝟙 X.base)) ≫
      Z.fiber.map
        (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ (φ.base ≫ ψ.base))) (V := Over.mk (𝟙 Z.base))
          (φ.base ≫ ψ.base) (by simp)) =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          Y.fiber.map
            (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ φ.base)) (V := Over.mk (𝟙 Y.base))
              φ.base (by simp)) ≫
            ψ.fiber.app (Over.mk (𝟙 Y.base)) ≫
              Z.fiber.map
                (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                  ψ.base (by simp)) := by
  -- Route correction: first isolate the `mapComp.inv` and transport tail into a literal
  -- composite-slice map, then collapse the transport pair and finish with the already-proved
  -- precomposed-tail and naturality comparisons.
  calc
    (φ.fiber ≫
        ((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.map ψ.fiber ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
          Z.fiber))).app (Over.mk (𝟙 X.base)) ≫
      Z.fiber.map
        (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ (φ.base ≫ ψ.base))) (V := Over.mk (𝟙 Z.base))
          (φ.base ≫ ψ.base) (by simp)) =
        (φ.fiber.app (Over.mk (𝟙 X.base)) ≫
            (eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
              ψ.fiber.app (Over.mk φ.base) ≫
                eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm) ≫
              ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
                Z.fiber).app (Over.mk (𝟙 X.base)))) ≫
          Z.fiber.map
            (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ (φ.base ≫ ψ.base))) (V := Over.mk (𝟙 Z.base))
              (φ.base ≫ ψ.base) (by simp)) := by
      exact twoYonedaSplit_map_comp_first_normal_form p φ ψ
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm ≫
                ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
                  Z.fiber).app (Over.mk (𝟙 X.base))) ≫
                Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_direct_obj p φ ψ)) ≫
                Z.fiber.map
                  (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                    (φ.base ≫ ψ.base) (by simp)) := by
      -- Replace the raw composite tautological slice arrow by the literal composite slice arrow,
      -- keeping the fixed prefix untouched.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (φ.fiber.app (Over.mk (𝟙 X.base)) ≫
                (eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
                  ψ.fiber.app (Over.mk φ.base) ≫
                    eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm) ≫
                  ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapComp ψ.base.op.toLoc φ.base.op.toLoc).inv.toNatTrans.app
                    Z.fiber).app (Over.mk (𝟙 X.base)))) ≫ k)
          (twoYonedaSplit_composite_raw_slice_tail (p := p) (φ := φ) (ψ := ψ))
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm ≫
                Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_obj p φ ψ)) ≫
                Z.fiber.map
                  (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                    (φ.base ≫ ψ.base) (by simp)) := by
      -- The `mapComp.inv` component now lines up with the explicit direct-composite transport.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            φ.fiber.app (Over.mk (𝟙 X.base)) ≫
              eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
                ψ.fiber.app (Over.mk φ.base) ≫
                  eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm ≫
                    k ≫
                    Z.fiber.map
                      (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                        (φ.base ≫ ψ.base) (by simp)))
          (twoYonedaSplit_mapComp_inv_app_eq (p := p) (φ := φ) (ψ := ψ))
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              (eqToHom (twoYonedaSplit_iterated_precomposition_obj p φ ψ).symm ≫
                Z.fiber.map (eqToHom (twoYonedaSplit_precomposed_composite_obj p φ ψ))) ≫
              Z.fiber.map
                (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                  (φ.base ≫ ψ.base) (by simp)) := by
      -- Reassociate so the transport pair appears as a single middle factor.
      simp
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              𝟙 ((((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                Z.fiber).obj (Over.mk φ.base)) ≫
              Z.fiber.map
                (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                  (φ.base ≫ ψ.base) (by simp)) := by
      -- Now apply the dedicated transport-cancellation lemma to that grouped factor.
      rw [twoYonedaSplit_iterated_transport_cancel (p := p) (φ := φ) (ψ := ψ)]
      rfl
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          eqToHom (congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              Z.fiber.map
                (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                  (φ.base ≫ ψ.base) (by simp)) := by
      -- Then remove the identity.
      simp
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              Z.fiber.map
                (Over.homMk (U := Over.mk (φ.base ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                  (φ.base ≫ ψ.base) (by simp)) := by
      -- Replace the objectwise `eqToHom` by the functorial image of the source transport.
      rw [eqToHom_map]
      rfl
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
            ψ.fiber.app (Over.mk φ.base) ≫
              (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                  Z.fiber).map
                (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
                  φ.base (by simp)) ≫
                Z.fiber.map
                  (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                    ψ.base (by simp)) := by
      -- Rewrite the literal composite slice arrow into the two-step slice tail over `φ` and `ψ`.
      exact twoYonedaSplit_prefixed_precomposed_slice_tail p φ ψ
    _ =
        φ.fiber.app (Over.mk (𝟙 X.base)) ≫
          Y.fiber.map
            (Over.homMk (U := Over.mk ((𝟙 X.base) ≫ φ.base)) (V := Over.mk (𝟙 Y.base))
              φ.base (by simp)) ≫
            ψ.fiber.app (Over.mk (𝟙 Y.base)) ≫
              Z.fiber.map
                (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                  ψ.base (by simp)) := by
      -- First use the naturality square of `ψ.fiber`, then collapse the prefixed raw slice tail.
      have hNaturality :
          φ.fiber.app (Over.mk (𝟙 X.base)) ≫
            Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
              ψ.fiber.app (Over.mk φ.base) ≫
                (((twoYonedaCatPresheaf p).toPseudofunctor'.map ψ.base.op.toLoc).toFunctor.obj
                    Z.fiber).map
                  (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
                    φ.base (by simp)) ≫
                Z.fiber.map
                  (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                    ψ.base (by simp)) =
            φ.fiber.app (Over.mk (𝟙 X.base)) ≫
              ((Y.fiber.map (eqToHom (twoYonedaSplit_precomposed_identity_obj p φ)) ≫
                Y.fiber.map
                  (Over.homMk (U := Over.mk φ.base) (V := Over.mk (𝟙 Y.base))
                    φ.base (by simp))) ≫
                ψ.fiber.app (Over.mk (𝟙 Y.base))) ≫
                Z.fiber.map
                  (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                    ψ.base (by simp)) := by
        simpa [Category.assoc] using twoYonedaSplit_map_comp_tail_after_naturality p φ ψ
      refine hNaturality.trans ?_
      refine (congrArg
          (fun k ↦
            φ.fiber.app (Over.mk (𝟙 X.base)) ≫
              (k ≫ ψ.fiber.app (Over.mk (𝟙 Y.base))) ≫
                Z.fiber.map
                  (Over.homMk (U := Over.mk ((𝟙 Y.base) ≫ ψ.base)) (V := Over.mk (𝟙 Z.base))
                    ψ.base (by simp)))
          (twoYonedaSplit_raw_slice_tail (p := p) (φ := φ)).symm).trans ?_
      simp [Category.assoc]
      rfl

theorem twoYonedaSplitToOriginalUnderlying_map_comp
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∀ {X Y Z : twoYonedaSplitCategory p}
      (φ : X ⟶ Y) (ψ : Y ⟶ Z),
      twoYonedaSplitToOriginalMap p (φ ≫ ψ) =
        twoYonedaSplitToOriginalMap p φ ≫ twoYonedaSplitToOriginalMap p ψ := by
  intro X Y Z φ ψ
  -- Route correction: work directly with the CoGrothendieck composition formula and then rewrite
  -- its last owner-level composite by the dedicated reassociation lemma proved above.
  rw [twoYonedaSplitToOriginal_map_comp_left_expansion]
  simpa [twoYonedaSplitToOriginalMap, Category.assoc] using
    twoYonedaSplit_map_comp_reassociation p φ ψ

noncomputable def twoYonedaSplitToOriginalUnderlying
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitCategory p ⥤ S where
  obj := twoYonedaSplitToOriginalObj p
  map φ := twoYonedaSplitToOriginalMap p φ
  map_id := twoYonedaSplitToOriginalUnderlying_map_id p
  map_comp := fun φ ψ ↦ twoYonedaSplitToOriginalUnderlying_map_comp p φ ψ

/-- Helper for Remark 4.41.3: the vertical component of a morphism in the split model, evaluated
at the tautological slice object, is a lift over the base arrow `φ.base` with the expected source
and target coordinate changes. -/
private theorem twoYonedaSplit_component_app_base
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    p.map (φ.2.app (Over.mk (𝟙 X.base))) =
      eqToHom (X.2.w_obj (Over.mk (𝟙 X.base))) ≫
        𝟙 X.base ≫
          eqToHom
            ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
                Y.fiber).w_obj (Over.mk (𝟙 X.base))).symm := by
  -- The component `φ.2.app (Over.mk (𝟙 X.base))` is itself a lift over `φ.base`.
  let hLift : p.IsHomLift (𝟙 X.base) (φ.2.app (Over.mk (𝟙 X.base))) :=
    φ.2.isHomLift' (Over.mk (𝟙 X.base))
  letI : p.IsHomLift (𝟙 X.base) (φ.2.app (Over.mk (𝟙 X.base))) := hLift
  simpa only [toPseudofunctor'_obj, comp_obj, toPseudofunctor'_map, Quiver.Hom.toLoc_as,
    Functor.comp_map] using
    IsHomLift.fac' p (𝟙 X.base) (φ.2.app (Over.mk (𝟙 X.base)))

/-- Helper for Remark 4.41.3: evaluating a split-model object at the tautological slice object
lands over its base object. -/
private theorem twoYonedaSplitToOriginalObj_base
    (p : S ⥤ C) [IsFibredInGroupoids p] (X : twoYonedaSplitCategory p) :
    p.obj (twoYonedaSplitToOriginalObj p X) = X.base := by
  -- This is exactly the based-functor compatibility of `X.fiber` at `Over.mk (𝟙 X.base)`.
  exact X.fiber.w_obj (Over.mk (𝟙 X.base))

/-- Helper for Remark 4.41.3: after precomposing `Y.fiber` along `φ.base`, evaluating at the
tautological slice object yields the same object as evaluating `Y.fiber` at `Over.mk φ.base`. -/
private theorem twoYonedaSplit_precomposed_obj_eq
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
        Y.fiber).obj (Over.mk (𝟙 X.base))) =
      Y.fiber.obj (Over.mk φ.base) := by
  -- Unfolding the strict pseudofunctor map shows that the precomposed based functor is
  -- literally `Y.fiber` evaluated on `Over.map φ.base`, and `Over.map φ.base (id_X) = φ.base`.
  simpa [twoYonedaCatPresheaf, twoYonedaGroupoidPresheafMap, precomposeBasedFunctor,
    twoYonedaSliceChange] using
    congrArg Y.fiber.obj (twoYonedaSplit_precomposed_identity_obj p φ)

/-- Helper for Remark 4.41.3: after precomposing `Y.fiber` along a base arrow `f`, the base
equality at the tautological slice transports to the direct evaluation base equality at
`Over.mk f`. -/
private theorem twoYonedaSplit_precomposed_w_obj_transport_base
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (X Y : twoYonedaSplitCategory p) (f : X.base ⟶ Y.base) :
    congrArg (Functor.obj p)
        (show ((((twoYonedaCatPresheaf p).toPseudofunctor'.map f.op.toLoc).toFunctor.obj
            Y.fiber).obj (Over.mk (𝟙 X.base))) = Y.fiber.obj (Over.mk f) by
          simpa [twoYonedaCatPresheaf] using
            congrArg Y.fiber.obj
              (show ((twoYonedaSliceChange f).obj (Over.mk (𝟙 X.base))) = Over.mk f by
                change Over.mk ((𝟙 X.base) ≫ f) = Over.mk f
                simp)) ▸
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.map f.op.toLoc).toFunctor.obj Y.fiber).w_obj
          (Over.mk (𝟙 X.base))) =
      Y.fiber.w_obj (Over.mk f) := by
  -- After unfolding the precomposition functor, both base equalities are definitionally the same.
  cases X with
  | mk U FX =>
      cases Y with
      | mk V FY =>
          simp [twoYonedaCatPresheaf]

/-- Helper for Remark 4.41.3: evaluating the precomposed fiber object at `Over.mk (𝟙 X.base)`
still lies over `X.base`. -/
private theorem twoYonedaSplit_precomposed_obj_base
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    p.obj
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
            Y.fiber).obj (Over.mk (𝟙 X.base))) =
      X.base := by
  -- This is exactly the base-compatibility field of the precomposed based functor at `id_X`.
  exact
    ((((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
        Y.fiber).w_obj (Over.mk (𝟙 X.base)))

/-- Helper for Remark 4.41.3: evaluating `Y.fiber` at the slice object classified by `φ.base`
lies over the domain of `φ.base`. -/
private theorem twoYonedaSplit_evaluated_slice_obj_base
    (p : S ⥤ C) [IsFibredInGroupoids p]
    {X Y : twoYonedaSplitCategory p} (φ : X ⟶ Y) :
    p.obj (Y.fiber.obj (Over.mk φ.base)) = X.base := by
  -- This is the usual based-functor compatibility of `Y.fiber` evaluated at `Over.mk φ.base`.
  exact Y.fiber.w_obj (Over.mk φ.base)

/-- Helper for Remark 4.41.3: the base formula for the vertical component of a split-model
morphism, rewritten in the same coordinates as the tautological slice arrow over `φ.base`. -/
theorem twoYonedaSplitToOriginalUnderlying_w
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    twoYonedaSplitToOriginalUnderlying p ⋙ p = twoYonedaSplitProjection p := by
  -- Route correction: rather than chasing the remaining base transports manually, package the
  -- tautological slice arrow as an explicit hom-lift and read off the base formula of the whole
  -- composite from `IsHomLift.fac'`.
  refine Functor.ext (fun X ↦ ?_) (fun X Y φ ↦ ?_)
  · -- On objects, evaluation at `Over.mk (𝟙 U)` lands over the base object `U`.
    simpa [twoYonedaSplitToOriginalUnderlying, twoYonedaSplitProjection] using
      twoYonedaSplitToOriginalObj_base p X
  · -- The first factor of `twoYonedaSplitToOriginalMap` is vertical over `𝟙 X.base`.
    let hOver :
        (twoYonedaSliceChange φ.base).obj (Over.mk (𝟙 X.base)) ⟶ Over.mk (𝟙 Y.base) :=
      Over.homMk
        (U := (twoYonedaSliceChange φ.base).obj (Over.mk (𝟙 X.base)))
        (V := Over.mk (𝟙 Y.base)) φ.base (by simp [twoYonedaSliceChange])
    let hComponent : p.IsHomLift (𝟙 X.base) (φ.2.app (Over.mk (𝟙 X.base))) :=
      φ.2.isHomLift' (Over.mk (𝟙 X.base))
    let hSlice :
        p.IsHomLift φ.base (Y.fiber.map hOver) := by
      have hOverLift : (Over.forget Y.base).IsHomLift φ.base hOver := by
        refine IsHomLift.of_fac' (Over.forget Y.base) φ.base hOver rfl rfl ?_
        simp [hOver, twoYonedaSliceChange]
      exact (Y.fiber.isHomLift_iff φ.base hOver).2 hOverLift
    let ψ : twoYonedaSplitToOriginalObj p
        { base := X.base
          fiber :=
            (((twoYonedaCatPresheaf p).toPseudofunctor'.map φ.base.op.toLoc).toFunctor.obj
              Y.fiber) } ⟶ twoYonedaSplitToOriginalObj p Y :=
      Y.fiber.map hOver
    let hMap :
        p.IsHomLift φ.base (φ.2.app (Over.mk (𝟙 X.base)) ≫ ψ) := by
      letI : p.IsHomLift (𝟙 X.base) (φ.2.app (Over.mk (𝟙 X.base))) := hComponent
      letI : p.IsHomLift φ.base ψ := by simpa [ψ] using hSlice
      have hComp :
          p.IsHomLift ((𝟙 X.base) ≫ φ.base) (φ.2.app (Over.mk (𝟙 X.base)) ≫ ψ) :=
        IsHomLift.comp p (𝟙 X.base) φ.base (φ.2.app (Over.mk (𝟙 X.base))) ψ
      simpa using hComp
    -- The comparison functor is over `C`, so its map is exactly the base arrow `φ.base`.
    letI : p.IsHomLift φ.base (φ.2.app (Over.mk (𝟙 X.base)) ≫ ψ) := hMap
    change
      p.map (φ.2.app (Over.mk (𝟙 X.base)) ≫ ψ) =
        eqToHom (twoYonedaSplitToOriginalObj_base p X) ≫
          φ.base ≫
            eqToHom (twoYonedaSplitToOriginalObj_base p Y).symm
    simpa [twoYonedaSplitToOriginalUnderlying, twoYonedaSplitProjection,
      twoYonedaSplitToOriginalObj_base, hOver, ψ, Category.assoc] using
      IsHomLift.fac' p φ.base (φ.2.app (Over.mk (𝟙 X.base)) ≫ ψ)

/-- The split fibred-in-groupoids model over `C` attached to the `2`-Yoneda groupoid presheaf. -/
noncomputable def twoYonedaSplitModel
    (p : S ⥤ C) [IsFibredInGroupoids p] : FibredInGroupoidsOver C :=
  FibredInGroupoidsOver.ofFunctor (twoYonedaSplitProjection p)

private noncomputable instance twoYonedaSplitProjection_instIsSplitFibredCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    Functor.IsSplitFibredCategory (twoYonedaSplitProjection p) := by
  change Functor.IsSplitFibredCategory
    (CoGrothendieck.forget ((twoYonedaCatPresheaf p).toPseudofunctor'))
  refine ⟨⟨twoYonedaCatPresheaf p, BasedFunctor.id _, BasedFunctor.id _, ?_⟩⟩
  exact ⟨rfl, rfl⟩

noncomputable instance twoYonedaSplitModel_instIsSplitFibredCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    Functor.IsSplitFibredCategory ((twoYonedaSplitModel p).p) := by
  change Functor.IsSplitFibredCategory (twoYonedaSplitProjection p)
  infer_instance

/-- The canonical functor over `C` from the split `2`-Yoneda model to the original category
fibred in groupoids. It sends `(U, x)` to `x(𝟙 U)`. -/
noncomputable def twoYonedaSplitToOriginal
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredInGroupoidsMor (twoYonedaSplitModel p) (FibredInGroupoidsOver.ofFunctor p) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := twoYonedaSplitToOriginalUnderlying p
      w := twoYonedaSplitToOriginalUnderlying_w p }

/-- Helper for Remark 4.41.3: the canonical identification of the split-model fiber with the raw
presheaf value is itself an equivalence. -/
private theorem twoYonedaSplit_inducedFunctor_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (HasFibers.inducedFunctor (twoYonedaSplitProjection p) U).IsEquivalence := by
  infer_instance

/-- Helper for Remark 4.41.3: every based functor from the slice `C/U` into `p` preserves
strongly cartesian morphisms because every morphism in a category fibred in groupoids is strongly
cartesian. -/
private theorem twoYonedaSplit_preserves_strongly_cartesian
    (p : S ⥤ C) [IsFibredInGroupoids p] {U : C}
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    F.PreservesStronglyCartesian := by
  -- The target owner already supplies strong cartesianness for every mapped morphism.
  intro a b φ _
  exact (inferInstance : IsFibredInGroupoids p).isStronglyCartesian_map (F.map φ)

/-- Helper for Remark 4.41.3: any based functor into a category fibred in groupoids preserves
strongly cartesian morphisms, independently of its source category over `C`. -/
private theorem twoYonedaSplit_any_preserves_strongly_cartesian
    {X : BasedCategory.{vX, uX} C}
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (F : X ⥤ᵇ BasedCategory.ofFunctor p) :
    F.PreservesStronglyCartesian := by
  -- In a fibred groupoid, the target owner already marks every morphism as strongly cartesian.
  intro a b φ _
  exact (inferInstance : IsFibredInGroupoids p).isStronglyCartesian_map (F.map φ)

/-- Helper for Remark 4.41.3: convert a based natural transformation into the corresponding
morphism in the owner hom-category of fibred categories. -/
private abbrev twoYonedaSplit_fibredCategoryMorHomOfBasedNatTrans
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    F ⟶ G :=
  ⟨ObjectProperty.homMk η, trivial⟩

/-- Helper for Remark 4.41.3: forgetting the owner wrapper around a morphism built from a based
natural transformation recovers the original transformation. -/
@[simp] private theorem twoYonedaSplit_fibredCategoryMorHomOfBasedNatTrans_hom_hom
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor F ⟶ FibredCategoryMor.toBasedFunctor G) :
    (twoYonedaSplit_fibredCategoryMorHomOfBasedNatTrans η).hom.hom = η :=
  rfl

/-- Helper for Remark 4.41.3: an isomorphism of underlying based functors induces the
corresponding isomorphism in the owner hom-category of fibred categories. -/
private noncomputable def twoYonedaSplit_fibredCategoryMorIsoOfBasedFunctorIso
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Helper for Remark 4.41.3: forgetting the owner wrapper around the forward map of an
isomorphism induced from a based-functor isomorphism recovers the original forward map. -/
@[simp] private theorem twoYonedaSplit_fibredCategoryMorIsoOfBasedFunctorIso_hom_hom
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    (twoYonedaSplit_fibredCategoryMorIsoOfBasedFunctorIso e).hom.hom.hom = e.hom :=
  rfl

/-- Helper for Remark 4.41.3: forgetting the owner wrapper around the inverse map of an
isomorphism induced from a based-functor isomorphism recovers the original inverse map. -/
@[simp] private theorem twoYonedaSplit_fibredCategoryMorIsoOfBasedFunctorIso_inv_hom_hom
    {X Y : FibredCategoryOver C}
    {F G : X ⟶ Y}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    (twoYonedaSplit_fibredCategoryMorIsoOfBasedFunctorIso e).inv.hom.hom = e.inv :=
  rfl

/-
The following generated universe-transport route through `AsSmall` is left here as disabled
development history. It tries to reduce the target owner to the universe expected by the imported
2-Yoneda theorem, but `AsSmall` does not lower the hom universe. The active proof below uses the
source statement's small universe profile and compares raw evaluation directly with the owner
evaluation functor of `FibredCategoryOver.ofFunctor p`.

/-- Helper for Remark 4.41.3: enlarge the slice category `C/U` to the ambient hom universe using
`AsSmall`, so owner morphisms into the original fibred category live in a single universe. -/
private abbrev twoYonedaSplit_owner_slice_lift (U : C) :=
  AsSmall.{max (max u v₁) v₂} (Over U)

/-- Helper for Remark 4.41.3: the lifted slice category still projects to `C` through the ordinary
slice forgetful functor after forgetting the `ULiftHom` wrapper. -/
private abbrev twoYonedaSplit_owner_slice_lift_forget (U : C) :
    twoYonedaSplit_owner_slice_lift U ⥤ C :=
  (AsSmall.down : twoYonedaSplit_owner_slice_lift U ⥤ Over U) ⋙ Over.forget U

/-- Helper for Remark 4.41.3: forget the `ULiftHom` wrapper on the lifted slice category as a
based functor over `C`. -/
private abbrev twoYonedaSplit_owner_slice_lift_down (U : C) :
    BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget U) ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget U) :=
  { toFunctor := (AsSmall.down : twoYonedaSplit_owner_slice_lift U ⥤ Over U)
    w := rfl }

/-- Helper for Remark 4.41.3: the ordinary slice category includes into the lifted slice model as
a based functor over `C`. -/
private abbrev twoYonedaSplit_owner_slice_lift_up (U : C) :
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget U) :=
  { toFunctor := (AsSmall.up : Over U ⥤ twoYonedaSplit_owner_slice_lift U)
    w := rfl }

/-- Helper for Remark 4.41.3: inserting the `ULiftHom` wrapper and then forgetting it is the
identity based functor on the ordinary slice model. -/
private theorem twoYonedaSplit_owner_slice_lift_down_up (U : C) :
    BasedFunctor.comp (twoYonedaSplit_owner_slice_lift_up U)
        (twoYonedaSplit_owner_slice_lift_down U) =
      BasedFunctor.id (BasedCategory.ofFunctor (Over.forget U)) := by
  -- `AsSmall.up ⋙ AsSmall.down` is strict identity on the ordinary slice category.
  apply basedFunctor_ext
  rfl

/-- Helper for Remark 4.41.3: forgetting the lifted slice and then reinserting the `ULiftHom`
wrapper is the identity based functor on the lifted slice model. -/
private theorem twoYonedaSplit_owner_slice_lift_up_down (U : C) :
    BasedFunctor.comp
        (show
          BasedCategory.ofFunctor
              (((AsSmall.down : twoYonedaSplit_owner_slice_lift U ⥤ Over U) ⋙ Over.forget U)) ⥤ᵇ
            BasedCategory.ofFunctor (Over.forget U) from
          twoYonedaSplit_owner_slice_lift_down U)
        (show
          BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
            BasedCategory.ofFunctor
              (((AsSmall.down : twoYonedaSplit_owner_slice_lift U ⥤ Over U) ⋙ Over.forget U)) from
          twoYonedaSplit_owner_slice_lift_up U) =
      BasedFunctor.id
        (BasedCategory.ofFunctor
          (((AsSmall.down : twoYonedaSplit_owner_slice_lift U ⥤ Over U) ⋙ Over.forget U))) := by
  -- `AsSmall.down ⋙ AsSmall.up` is strict identity on the lifted slice category as well.
  apply basedFunctor_ext
  rfl

/-- Helper for Remark 4.41.3: shrink the target category to `AsSmall S` without changing the
projection to `C`. This is the target-side universe reduction candidate for a later owner-level
transport. -/
private abbrev twoYonedaSplit_target_small
    (p : S ⥤ C) :
    AsSmall.{max (max u v₁) v₂} S ⥤ C :=
  (AsSmall.down : AsSmall.{max (max u v₁) v₂} S ⥤ S) ⋙ p

/-- Helper for Remark 4.41.3: forget the target-side `AsSmall` wrapper as a based functor over
`C`. -/
private abbrev twoYonedaSplit_target_small_down
    (p : S ⥤ C) :
    BasedCategory.ofFunctor (twoYonedaSplit_target_small p) ⥤ᵇ
      BasedCategory.ofFunctor p :=
  { toFunctor := (AsSmall.down : AsSmall.{max (max u v₁) v₂} S ⥤ S)
    w := rfl }

/-- Helper for Remark 4.41.3: insert the target-side `AsSmall` wrapper as a based functor over
`C`. -/
private abbrev twoYonedaSplit_target_small_up
    (p : S ⥤ C) :
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p) :=
  { toFunctor := (AsSmall.up : S ⥤ AsSmall.{max (max u v₁) v₂} S)
    w := rfl }

/-- Helper for Remark 4.41.3: inserting the target-side `AsSmall` wrapper and then forgetting it
is the strict identity on the original target. -/
private theorem twoYonedaSplit_target_small_down_up
    (p : S ⥤ C) :
    BasedFunctor.comp
        (twoYonedaSplit_target_small_down p)
        (twoYonedaSplit_target_small_up p) =
      BasedFunctor.id
        (BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) := by
  -- `AsSmall.up ⋙ AsSmall.down` is strict identity on the target category.
  apply basedFunctor_ext
  rfl

/-- Helper for Remark 4.41.3: forgetting the target-side `AsSmall` wrapper and then reinserting
it is the strict identity on the shrunken target. -/
private theorem twoYonedaSplit_target_small_up_down
    (p : S ⥤ C) :
    BasedFunctor.comp
        (twoYonedaSplit_target_small_up p)
        (twoYonedaSplit_target_small_down p) =
      BasedFunctor.id (BasedCategory.ofFunctor p) := by
  -- `AsSmall.down ⋙ AsSmall.up` is strict identity on the shrunken target as well.
  apply basedFunctor_ext
  rfl

/-- Helper for Remark 4.41.3: the enlarged slice model still evaluates the lifted identity object
back to the ordinary identity object `id_U : U/U`. -/
private theorem twoYonedaSplit_owner_slice_lift_identity_obj
    (U : C) :
    (twoYonedaSplit_owner_slice_lift_down U).obj
        ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U))) =
      Over.mk (𝟙 U) := by
  -- The `AsSmall` round trip is strict on the ordinary slice object `Over.mk (𝟙 U)`.
  rfl

/-- Helper for Remark 4.41.3: evaluation of a raw split-model object at `id_U : U/U` gives the
fiber object appearing in the comparison functor `G_U`. -/
private noncomputable def twoYonedaSplit_rawEvaluationFunctor
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    twoYonedaGroupoidPresheafValue p U ⥤ p.Fiber U where
  obj F :=
    ⟨F.obj (Over.mk (𝟙 U)), by
      -- The based-functor compatibility identifies the base of `F(id_U)` with `U`.
      let h :
          p.obj (F.obj (Over.mk (𝟙 U))) =
            (Over.forget U).obj (Over.mk (𝟙 U)) :=
        F.w_obj (Over.mk (𝟙 U))
      simpa using h⟩
  map {F G} τ :=
    let _ : p.IsHomLift (𝟙 U) (τ.toNatTrans.app (Over.mk (𝟙 U))) :=
      τ.isHomLift' (Over.mk (𝟙 U))
    Functor.Fiber.homMk p U (τ.toNatTrans.app (Over.mk (𝟙 U)))
  map_id := by
    intro F
    -- Evaluation at `id_U` turns the identity natural transformation into the identity in the
    -- fiber over `U`.
    apply Functor.Fiber.hom_ext
    rfl
  map_comp := by
    intro F G H τ σ
    -- Evaluation at `id_U` is compatible with composition of based natural transformations.
    apply Functor.Fiber.hom_ext
    rfl

/-- Helper for Remark 4.41.3: the underlying morphism of raw evaluation on a based natural
transformation is its component at the tautological slice object `id_U : U/U`. -/
@[simp] private theorem twoYonedaSplit_rawEvaluationFunctor_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : twoYonedaGroupoidPresheafValue p U} (τ : F ⟶ G) :
    Functor.Fiber.fiberInclusion.map ((twoYonedaSplit_rawEvaluationFunctor p U).map τ) =
      τ.toNatTrans.app (Over.mk (𝟙 U)) :=
  rfl

/-- Helper for Remark 4.41.3: after postcomposing with the target-side insertion `S ⥤ AsSmall S`,
evaluation at `id_U : U/U` is computed by applying `AsSmall.up` to the original evaluated object.
-/
private theorem twoYonedaSplit_target_small_postcompose_eval_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    ((postcomposeBasedFunctor
        (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p)).obj F).obj (Over.mk (𝟙 U)) =
      (twoYonedaSplit_target_small_up p).obj (F.obj (Over.mk (𝟙 U))) := by
  -- Postcomposition only changes the target value by applying `AsSmall.up`.
  rfl

/-- Helper for Remark 4.41.3: on a based natural transformation, postcomposing with the
target-side insertion changes the component at `id_U : U/U` by applying `AsSmall.up.map`. -/
private theorem twoYonedaSplit_target_small_postcompose_map_app
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p} (η : F ⟶ G) :
    (((postcomposeBasedFunctor
        (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p)).map η).app (Over.mk (𝟙 U))) =
      (twoYonedaSplit_target_small_up p).map (η.toNatTrans.app (Over.mk (𝟙 U))) := by
  -- Right whiskering by `AsSmall.up` acts objectwise on the original component.
  rfl

/-- Helper for Remark 4.41.3: precomposition with
`twoYonedaSplit_owner_slice_lift_down U : AsSmall (C/U) ⥤ C/U` transports raw split-model
objects from the ordinary slice to the lifted slice. -/
private noncomputable abbrev twoYonedaSplit_owner_slice_precompose
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) ⥤
      (BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U) ⥤ᵇ
        BasedCategory.ofFunctor p) :=
  let X : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
    BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
  let Y : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
  let Z : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C := BasedCategory.ofFunctor p
  show (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) from
    precomposeBasedFunctor (X := X) (Y := Y) (Z := Z)
      (twoYonedaSplit_owner_slice_lift_down U)

/-- Helper for Remark 4.41.3: the ordinary slice presentation `C/U ⥤ᵇ p` of the raw `2`-Yoneda
fiber. -/
private abbrev twoYonedaSplit_ordinary_slice_functor_category
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :=
  BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p

/-- Helper for Remark 4.41.3: the lifted-slice presentation `AsSmall (C/U) ⥤ᵇ p` used to pin the
owner universes. -/
private abbrev twoYonedaSplit_lifted_slice_functor_category
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :=
  BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U) ⥤ᵇ
    BasedCategory.ofFunctor p

/-- Helper for Remark 4.41.3: precomposition with the lift-down functor is an equivalence, with
quasi-inverse given by precomposition with the lift-up functor. -/
private theorem twoYonedaSplit_owner_slice_precompose_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_owner_slice_precompose p U).IsEquivalence := by
  -- The quasi-inverse is precomposition with the strict lift-up functor on the enlarged slice.
  let X : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
  let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
    BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
  let Z : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C := BasedCategory.ofFunctor p
  let F : (X ⥤ᵇ Z) ⥤ (Y ⥤ᵇ Z) :=
    show (X ⥤ᵇ Z) ⥤ (Y ⥤ᵇ Z) from twoYonedaSplit_owner_slice_precompose p U
  let G :
      (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) :=
    show (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) from
      precomposeBasedFunctor (X := X) (Y := Y) (Z := Z)
        (twoYonedaSplit_owner_slice_lift_up U)
  suffices hF : F.IsEquivalence by
    simpa [F] using hF
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- The unit is the strict identity coming from `lift_up ⋙ lift_down = 𝟭` on the ordinary slice.
    apply eqToIso
    calc
      𝟭 (X ⥤ᵇ Z) = precomposeBasedFunctor (X := X) (Y := X) (Z := Z) (BasedFunctor.id X) := by
                symm
                exact precomposeBasedFunctor_id
      _ = precomposeBasedFunctor
            (BasedFunctor.comp (twoYonedaSplit_owner_slice_lift_up U)
              (twoYonedaSplit_owner_slice_lift_down U)) := by
                rw [twoYonedaSplit_owner_slice_lift_down_up]
      _ = F ⋙ G := by
            simpa [F, twoYonedaSplit_owner_slice_precompose, G] using
              (precomposeBasedFunctor_comp
                (W := Z)
                (φ := twoYonedaSplit_owner_slice_lift_up U)
                (ψ := twoYonedaSplit_owner_slice_lift_down U))
  · -- The counit is the strict identity coming from `lift_down ⋙ lift_up = 𝟭` on the lifted slice.
    apply eqToIso
    calc
      G ⋙ F
          = precomposeBasedFunctor
              (BasedFunctor.comp (twoYonedaSplit_owner_slice_lift_down U)
                (twoYonedaSplit_owner_slice_lift_up U)) := by
                  simpa [F, twoYonedaSplit_owner_slice_precompose, G] using
                    (precomposeBasedFunctor_comp
                      (W := Z)
                      (φ := twoYonedaSplit_owner_slice_lift_down U)
                      (ψ := twoYonedaSplit_owner_slice_lift_up U)).symm
      _ = precomposeBasedFunctor
            (X := Y) (Y := Y) (Z := Z) (BasedFunctor.id Y) := by
                rw [twoYonedaSplit_owner_slice_lift_up_down]
      _ = 𝟭 (Y ⥤ᵇ Z) := by
                exact precomposeBasedFunctor_id

/-- Helper for Remark 4.41.3: precomposing with `lift_down` does not change the value of a raw
split-model object at the lifted identity object. -/
private theorem twoYonedaSplit_owner_slice_precompose_eval_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : twoYonedaSplit_ordinary_slice_functor_category p U) :
    ((twoYonedaSplit_owner_slice_precompose p U).obj F).obj
        ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U))) =
      F.obj (Over.mk (𝟙 U)) := by
  -- Evaluate the precomposed lifted-slice functor at the lifted identity object and then forget
  -- the `ULiftHom` wrapper back to `id_U : U/U`.
  simpa [twoYonedaSplit_owner_slice_precompose, precomposeBasedFunctor, BasedFunctor.comp,
    twoYonedaSplit_owner_slice_lift_identity_obj]

/-- Helper for Remark 4.41.3: on a based natural transformation, precomposition with `lift_down`
evaluated at the lifted identity object recovers the original component at `id_U : U/U`. -/
private theorem twoYonedaSplit_owner_slice_precompose_map_app
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : twoYonedaSplit_ordinary_slice_functor_category p U} (τ : F ⟶ G) :
    (((twoYonedaSplit_owner_slice_precompose p U).map τ).toNatTrans.app
        ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U)))) =
      τ.toNatTrans.app (Over.mk (𝟙 U)) := by
  -- Left whiskering only changes the source object by `lift_down`, and that source object is
  -- exactly `id_U : U/U` after forgetting the `ULiftHom` wrapper.
  simpa [twoYonedaSplit_owner_slice_precompose, precomposeBasedFunctor, BasedCategory.whiskerLeft,
    twoYonedaSplit_owner_slice_lift_identity_obj]

/-- Helper for Remark 4.41.3: after precomposing with `lift_down`, evaluating at the lifted
identity object gives the same object of the fiber over `U` as raw evaluation at `id_U : U/U`.
-/
private theorem twoYonedaSplit_owner_slice_precompose_eval_fiber_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : twoYonedaSplit_ordinary_slice_functor_category p U) :
    (twoYonedaSplit_rawEvaluationFunctor p U).obj F =
      ⟨((twoYonedaSplit_owner_slice_precompose p U).obj F).obj
          ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U))), by
        -- The lifted identity object still lies over `U`, and objectwise precomposition recovers
        -- the original value at `id_U : U/U`.
        calc
          p.obj (((twoYonedaSplit_owner_slice_precompose p U).obj F).obj
              ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U)))) =
              p.obj (F.obj (Over.mk (𝟙 U))) := by
                rw [twoYonedaSplit_owner_slice_precompose_eval_obj p U F]
          _ = U := by
                change p.obj (F.obj (Over.mk (𝟙 U))) =
                  (Over.forget U).obj (Over.mk (𝟙 U))
                exact F.w_obj (Over.mk (𝟙 U))⟩ := by
  -- Equality in the fiber is detected after forgetting to the total category.
  apply Functor.Fiber.fiberInclusion_obj_inj
  change F.obj (Over.mk (𝟙 U)) =
      ((twoYonedaSplit_owner_slice_precompose p U).obj F).obj
        ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U)))
  symm
  exact twoYonedaSplit_owner_slice_precompose_eval_obj p U F

/-- Helper for Remark 4.41.3: after precomposing with `lift_down`, the component of a based
natural transformation at the lifted identity object is still a lift over `𝟙 U`. -/
private theorem twoYonedaSplit_owner_slice_precompose_eval_isHomLift
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : twoYonedaSplit_ordinary_slice_functor_category p U} (τ : F ⟶ G) :
    p.IsHomLift (𝟙 U)
      (((twoYonedaSplit_owner_slice_precompose p U).map τ).toNatTrans.app
        ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U)))) := by
  -- Evaluating the whiskered transformation at the lifted identity object preserves the same base
  -- arrow, and that base is definitionally `𝟙 U` after forgetting the `ULiftHom` wrapper.
  simpa [twoYonedaSplit_owner_slice_lift_identity_obj] using
    (((twoYonedaSplit_owner_slice_precompose p U).map τ).isHomLift'
      ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U))))

/-- Helper for Remark 4.41.3: postcomposition with the target-side insertion
`twoYonedaSplit_target_small_up p : S ⥤ AsSmall S` is an equivalence on ordinary-slice functor
categories. -/
private theorem twoYonedaSplit_target_small_postcompose_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (postcomposeBasedFunctor
      (X := BasedCategory.ofFunctor (Over.forget U))
      (twoYonedaSplit_target_small_up p)).IsEquivalence := by
  -- The quasi-inverse is postcomposition with `twoYonedaSplit_target_small_down p`.
  let X : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
  let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C := BasedCategory.ofFunctor p
  let Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p)
  let F : (X ⥤ᵇ Y) ⥤ (X ⥤ᵇ Z) :=
    show (X ⥤ᵇ Y) ⥤ (X ⥤ᵇ Z) from
      postcomposeBasedFunctor (X := X) (twoYonedaSplit_target_small_up p)
  let G : (X ⥤ᵇ Z) ⥤ (X ⥤ᵇ Y) :=
    show (X ⥤ᵇ Z) ⥤ (X ⥤ᵇ Y) from
      postcomposeBasedFunctor (X := X) (twoYonedaSplit_target_small_down p)
  suffices hF : F.IsEquivalence by
    simpa [F] using hF
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- The unit is strict because `up ≫ down = 𝟭` on the original target.
    apply eqToIso
    calc
      𝟭 (X ⥤ᵇ Y) = postcomposeBasedFunctor (X := X) (BasedFunctor.id Y) := by
        symm
        exact postcomposeBasedFunctor_id
      _ = postcomposeBasedFunctor (X := X)
            (BasedFunctor.comp (twoYonedaSplit_target_small_up p)
              (twoYonedaSplit_target_small_down p)) := by
                rw [twoYonedaSplit_target_small_up_down]
      _ = F ⋙ G := by
            simpa [F, G] using
              (postcomposeBasedFunctor_comp
                (X := X)
                (φ := twoYonedaSplit_target_small_up p)
                (ψ := twoYonedaSplit_target_small_down p))
  · -- The counit is strict because `down ≫ up = 𝟭` on the shrunken target.
    apply eqToIso
    calc
      G ⋙ F =
          postcomposeBasedFunctor (X := X)
            (BasedFunctor.comp (twoYonedaSplit_target_small_down p)
              (twoYonedaSplit_target_small_up p)) := by
                simpa [F, G] using
                  (postcomposeBasedFunctor_comp
                    (X := X)
                    (φ := twoYonedaSplit_target_small_down p)
                    (ψ := twoYonedaSplit_target_small_up p)).symm
      _ = postcomposeBasedFunctor (X := X) (BasedFunctor.id Z) := by
            rw [twoYonedaSplit_target_small_down_up]
      _ = 𝟭 (X ⥤ᵇ Z) := by
            exact postcomposeBasedFunctor_id

/-- Helper for Remark 4.41.3: forgetting the target-side `AsSmall` wrapper induces an
equivalence on the fiber over `U`. -/
private theorem twoYonedaSplit_target_small_down_fiberFunctor_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    ((twoYonedaSplit_target_small_down p).fiberFunctor U).IsEquivalence := by
  -- The based functors `up` and `down` already form an equivalence over the base, so they induce
  -- an equivalence on each fiber.
  refine BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
    (twoYonedaSplit_target_small_down p) ?_ U
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (twoYonedaSplit_target_small_up p) ?_ ?_
  · simpa using eqToIso (twoYonedaSplit_target_small_down_up p).symm
  · simpa using eqToIso (twoYonedaSplit_target_small_up_down p)

/-- Helper for Remark 4.41.3: forgetting the target-side `AsSmall` wrapper is an equivalence over
the base category. -/
private theorem twoYonedaSplit_target_small_down_isEquivalenceOverBase
    (p : S ⥤ C) :
    (twoYonedaSplit_target_small_down p).IsEquivalenceOverBase := by
  -- The strict identities `up ≫ down = 𝟭` and `down ≫ up = 𝟭` already package the required
  -- equivalence-over-base data.
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (twoYonedaSplit_target_small_up p) ?_ ?_
  · simpa using eqToIso (twoYonedaSplit_target_small_down_up p).symm
  · simpa using eqToIso (twoYonedaSplit_target_small_up_down p)

/-- Helper for Remark 4.41.3: inserting the target-side `AsSmall` wrapper is also an equivalence
over the base category. -/
private theorem twoYonedaSplit_target_small_up_isEquivalenceOverBase
    (p : S ⥤ C) :
    (twoYonedaSplit_target_small_up p).IsEquivalenceOverBase := by
  -- This is the same equivalence-over-base data viewed from the opposite direction.
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    (twoYonedaSplit_target_small_down p) ?_ ?_
  · simpa using eqToIso (twoYonedaSplit_target_small_up_down p).symm
  · simpa using eqToIso (twoYonedaSplit_target_small_down_up p)

/-- Helper for Remark 4.41.3: the target-side `AsSmall` model remains fibred over `C`. -/
private theorem twoYonedaSplit_target_small_isFibered
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (twoYonedaSplit_target_small p).IsFibered := by
  -- Transport fibredness across the strict equivalence-over-base
  -- `twoYonedaSplit_target_small_up p : S ⥤ᵇ AsSmall S`.
  have hp : (BasedCategory.ofFunctor p).p.IsFibered := by
    simpa [BasedCategory.ofFunctor] using (inferInstance : p.IsFibered)
  exact
    (BasedFunctor.isFibered_iff_of_equivalence_over_base
      (twoYonedaSplit_target_small_up p)
      (twoYonedaSplit_target_small_up_isEquivalenceOverBase p)).mp hp

/-- Helper for Remark 4.41.3: the target-side `AsSmall` model is again fibred in groupoids. -/
private theorem twoYonedaSplit_target_small_isFibredInGroupoids
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    IsFibredInGroupoids (twoYonedaSplit_target_small p) := by
  -- After transporting fibredness, each fiber is a groupoid because `twoYonedaSplit_target_small_up p`
  -- is an equivalence on every fiber.
  refine isFibredInGroupoids_of_isFibered_and_fiber_groupoid
    (twoYonedaSplit_target_small p)
    (twoYonedaSplit_target_small_isFibered p) ?_
  intro U
  letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
    simpa using (inferInstance : IsGroupoid (p.Fiber U))
  exact
    BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase
      (twoYonedaSplit_target_small_up p)
      (twoYonedaSplit_target_small_up_isEquivalenceOverBase p)
      U

/-- Helper for Remark 4.41.3: the shrunken target carries the induced fibred-in-groupoids
instance. -/
private noncomputable instance twoYonedaSplit_target_small_instIsFibredInGroupoids
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    IsFibredInGroupoids (twoYonedaSplit_target_small p) :=
  twoYonedaSplit_target_small_isFibredInGroupoids p

/-- Helper for Remark 4.41.3: the target-side insertion `S ⥤ AsSmall S` also induces an
equivalence on the fiber over `U`. -/
private theorem twoYonedaSplit_target_small_up_fiberFunctor_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    ((twoYonedaSplit_target_small_up p).fiberFunctor U).IsEquivalence := by
  -- The target-side insertion is already an equivalence over the base, so each induced fiber
  -- functor is an equivalence as well.
  exact
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (twoYonedaSplit_target_small_up p)
      (twoYonedaSplit_target_small_up_isEquivalenceOverBase p)
      U

/-- Helper for Remark 4.41.3: the target-side raw-evaluation comparison is natural in a based
natural transformation on the ordinary slice. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_comparison_naturality
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : F ⟶ G) :
    (postcomposeBasedFunctor (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p) ⋙
          twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).map η ≫
        eqToHom rfl =
        eqToHom rfl ≫
        (twoYonedaSplit_rawEvaluationFunctor p U ⋙
          (twoYonedaSplit_target_small_up p).fiberFunctor U).map η := by
  -- After forgetting from the fiber, both sides are the same whiskered component at `id_U : U/U`.
  apply Functor.Fiber.hom_ext
  simp [Functor.comp_map]
  rw [twoYonedaSplit_target_small_postcompose_map_app]
  simpa using
    congrArg ((twoYonedaSplit_target_small_up p).map)
      (twoYonedaSplit_rawEvaluationFunctor_map_hom p U η).symm

/-- Helper for Remark 4.41.3: postcomposing a raw split-model object with the target-side
insertion `S ⥤ AsSmall S` commutes with raw evaluation at `id_U : U/U`. -/
private noncomputable def twoYonedaSplit_target_small_rawEvaluation_comparison
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    postcomposeBasedFunctor (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p) ⋙
          twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U ≅
      twoYonedaSplit_rawEvaluationFunctor p U ⋙
        (twoYonedaSplit_target_small_up p).fiberFunctor U :=
  NatIso.ofComponents
    (fun F ↦ eqToIso rfl)
    (twoYonedaSplit_target_small_rawEvaluation_comparison_naturality (p := p) (U := U))

/-- Helper for Remark 4.41.3: if raw evaluation is an equivalence for the shrunken target
`AsSmall S`, the target-side `AsSmall` transport carries that equivalence back to the original
target `S`. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_transport_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hsmall : (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence) :
    (twoYonedaSplit_rawEvaluationFunctor p U ⋙
      (twoYonedaSplit_target_small_up p).fiberFunctor U).IsEquivalence := by
  -- First compose the shrunken-target raw evaluation equivalence with postcomposition by
  -- `S ⥤ AsSmall S`.
  letI : (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence :=
    hsmall
  letI :
      (postcomposeBasedFunctor (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p)).IsEquivalence :=
    twoYonedaSplit_target_small_postcompose_isEquivalence p U
  have hleft :
      (postcomposeBasedFunctor (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p) ⋙
          twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence := by
    let Epost :=
      (postcomposeBasedFunctor (X := BasedCategory.ofFunctor (Over.forget U))
        (twoYonedaSplit_target_small_up p)).asEquivalence
    let Eeval :=
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).asEquivalence
    exact (Epost.trans Eeval).isEquivalence_functor
  -- Then rewrite the transported functor back to the original raw evaluation.
  exact
    (Functor.isEquivalence_iff_of_iso
      (twoYonedaSplit_target_small_rawEvaluation_comparison p U)).1 hleft

/-- Helper for Remark 4.41.3: if raw evaluation is an equivalence for the shrunken target
`AsSmall S`, the target-side `AsSmall` transport carries that equivalence back to the original
target `S`. -/
private theorem twoYonedaSplit_rawEvaluation_isEquivalence_of_target_small
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hsmall : (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence) :
    (twoYonedaSplit_rawEvaluationFunctor p U).IsEquivalence := by
  -- First package the shrunken-target equivalence after postcomposition by `S ⥤ AsSmall S`.
  have htransport :
      (twoYonedaSplit_rawEvaluationFunctor p U ⋙
        (twoYonedaSplit_target_small_up p).fiberFunctor U).IsEquivalence :=
    twoYonedaSplit_target_small_rawEvaluation_transport_isEquivalence p U hsmall
  -- Then cancel the fiber equivalence induced by `S ⥤ AsSmall S`.
  have hfiber :
      ((twoYonedaSplit_target_small_up p).fiberFunctor U).IsEquivalence :=
    twoYonedaSplit_target_small_up_fiberFunctor_isEquivalence p U
  exact
    @Functor.isEquivalence_of_comp_right _ _ _ _ _ _
      (twoYonedaSplit_rawEvaluationFunctor p U)
      ((twoYonedaSplit_target_small_up p).fiberFunctor U)
      hfiber
      htransport

/-- Helper for Remark 4.41.3: any based functor into a fibred-in-groupoids target preserves
strongly cartesian morphisms. -/
private theorem twoYonedaSplit_preserves_strongly_cartesian_into_groupoid_target
    {T : Type uY} [Category.{vY} T]
    {X : BasedCategory.{vX, uX} C}
    (q : T ⥤ C) [IsFibredInGroupoids q]
    (F : X ⥤ᵇ BasedCategory.ofFunctor q) :
    F.PreservesStronglyCartesian := by
  -- In a fibred groupoid, every morphism of the total category is strongly cartesian.
  intro a b φ _
  exact (inferInstance : IsFibredInGroupoids q).isStronglyCartesian_map (F.map φ)

/-- Helper for Remark 4.41.3: postcomposition with the target-side insertion `S ⥤ AsSmall S`
is an equivalence on based-functor categories for any source over `C`. -/
private theorem twoYonedaSplit_target_small_postcompose_any_isEquivalence
    {X : BasedCategory.{vX, uX} C}
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (postcomposeBasedFunctor (X := X) (twoYonedaSplit_target_small_up p)).IsEquivalence := by
  -- The quasi-inverse is postcomposition with `twoYonedaSplit_target_small_down p`,
  -- independently of the source category over `C`.
  let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C := BasedCategory.ofFunctor p
  let Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p)
  let F : (X ⥤ᵇ Y) ⥤ (X ⥤ᵇ Z) :=
    show (X ⥤ᵇ Y) ⥤ (X ⥤ᵇ Z) from
      postcomposeBasedFunctor (X := X) (twoYonedaSplit_target_small_up p)
  let G : (X ⥤ᵇ Z) ⥤ (X ⥤ᵇ Y) :=
    show (X ⥤ᵇ Z) ⥤ (X ⥤ᵇ Y) from
      postcomposeBasedFunctor (X := X) (twoYonedaSplit_target_small_down p)
  suffices hF : F.IsEquivalence by
    simpa [F] using hF
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- The unit is strict because `up ≫ down = 𝟭` on the original target.
    apply eqToIso
    calc
      𝟭 (X ⥤ᵇ Y) = postcomposeBasedFunctor (X := X) (BasedFunctor.id Y) := by
        symm
        exact postcomposeBasedFunctor_id
      _ = postcomposeBasedFunctor (X := X)
            (BasedFunctor.comp (twoYonedaSplit_target_small_up p)
              (twoYonedaSplit_target_small_down p)) := by
                rw [twoYonedaSplit_target_small_up_down]
      _ = F ⋙ G := by
            simpa [F, G] using
              (postcomposeBasedFunctor_comp
                (X := X)
                (φ := twoYonedaSplit_target_small_up p)
                (ψ := twoYonedaSplit_target_small_down p))
  · -- The counit is strict because `down ≫ up = 𝟭` on the shrunken target.
    apply eqToIso
    calc
      G ⋙ F =
          postcomposeBasedFunctor (X := X)
            (BasedFunctor.comp (twoYonedaSplit_target_small_down p)
              (twoYonedaSplit_target_small_up p)) := by
                simpa [F, G] using
                  (postcomposeBasedFunctor_comp
                    (X := X)
                    (φ := twoYonedaSplit_target_small_down p)
                    (ψ := twoYonedaSplit_target_small_up p)).symm
      _ = postcomposeBasedFunctor (X := X) (BasedFunctor.id Z) := by
            rw [twoYonedaSplit_target_small_down_up]
      _ = 𝟭 (X ⥤ᵇ Z) := by
            exact postcomposeBasedFunctor_id

/-- Helper for Remark 4.41.3: precomposition with `twoYonedaSplit_owner_slice_lift_down U`
is an equivalence on the based-functor category with target `AsSmall S`. -/
private theorem twoYonedaSplit_owner_slice_precompose_target_small_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    let X : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
    let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
      BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
    let Z : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)
    (show (X ⥤ᵇ Z) ⥤ (Y ⥤ᵇ Z) from
      precomposeBasedFunctor (X := Y) (Y := X) (Z := Z)
        (twoYonedaSplit_owner_slice_lift_down U)).IsEquivalence := by
  -- The quasi-inverse is precomposition with the strict lift-up functor on the enlarged slice.
  let X : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
  let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
    BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
  let Z : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
    BasedCategory.ofFunctor (twoYonedaSplit_target_small p)
  let F : (X ⥤ᵇ Z) ⥤ (Y ⥤ᵇ Z) :=
    show (X ⥤ᵇ Z) ⥤ (Y ⥤ᵇ Z) from
      precomposeBasedFunctor (X := Y) (Y := X) (Z := Z)
        (twoYonedaSplit_owner_slice_lift_down U)
  let G : (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) :=
    show (Y ⥤ᵇ Z) ⥤ (X ⥤ᵇ Z) from
      precomposeBasedFunctor (X := X) (Y := Y) (Z := Z)
        (twoYonedaSplit_owner_slice_lift_up U)
  suffices hF : F.IsEquivalence by
    simpa [F] using hF
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- The unit is strict because `lift_up ⋙ lift_down = 𝟭` on the ordinary slice.
    apply eqToIso
    calc
      𝟭 (X ⥤ᵇ Z) = precomposeBasedFunctor (X := X) (Y := X) (Z := Z) (BasedFunctor.id X) := by
        symm
        exact precomposeBasedFunctor_id
      _ = precomposeBasedFunctor
            (X := X) (Y := X) (Z := Z)
            (BasedFunctor.comp (twoYonedaSplit_owner_slice_lift_up U)
              (twoYonedaSplit_owner_slice_lift_down U)) := by
              rw [twoYonedaSplit_owner_slice_lift_down_up]
      _ = F ⋙ G := by
            simpa [F, G] using
              (precomposeBasedFunctor_comp
                (W := Z)
                (φ := twoYonedaSplit_owner_slice_lift_up U)
                (ψ := twoYonedaSplit_owner_slice_lift_down U))
  · -- The counit is strict because `lift_down ⋙ lift_up = 𝟭` on the lifted slice.
    apply eqToIso
    calc
      G ⋙ F =
          precomposeBasedFunctor
            (X := Y) (Y := Y) (Z := Z)
            (BasedFunctor.comp (twoYonedaSplit_owner_slice_lift_down U)
              (twoYonedaSplit_owner_slice_lift_up U)) := by
                simpa [F, G] using
                  (precomposeBasedFunctor_comp
                    (W := Z)
                    (φ := twoYonedaSplit_owner_slice_lift_down U)
                    (ψ := twoYonedaSplit_owner_slice_lift_up U)).symm
      _ = precomposeBasedFunctor (X := Y) (Y := Y) (Z := Z) (BasedFunctor.id Y) := by
            rw [twoYonedaSplit_owner_slice_lift_up_down]
      _ = 𝟭 (Y ⥤ᵇ Z) := by
            exact precomposeBasedFunctor_id

/-- Helper for Remark 4.41.3: the slice-side insertion `C/U ⥤ AsSmall (C/U)` is also an
equivalence over the base category `C`. -/
private theorem twoYonedaSplit_owner_slice_lift_up_isEquivalenceOverBase
    (U : C) :
    let X : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
    let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
      BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
    (show X ⥤ᵇ Y from twoYonedaSplit_owner_slice_lift_up U).IsEquivalenceOverBase := by
  -- This is the same strict `AsSmall` equivalence-over-base, viewed from the opposite direction.
  let X : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
  let Y : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
    BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
  let hup : X ⥤ᵇ Y := show X ⥤ᵇ Y from twoYonedaSplit_owner_slice_lift_up U
  let hdown : Y ⥤ᵇ X := show Y ⥤ᵇ X from twoYonedaSplit_owner_slice_lift_down U
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    hdown ?_ ?_
  · simpa [hup, hdown] using eqToIso (twoYonedaSplit_owner_slice_lift_down_up U).symm
  · simpa [hup, hdown] using eqToIso (twoYonedaSplit_owner_slice_lift_up_down U)

/-- Helper for Remark 4.41.3: forgetting the lifted slice back to the ordinary slice is also an
equivalence over the base category `C`. -/
private theorem twoYonedaSplit_owner_slice_lift_down_isEquivalenceOverBase
    (U : C) :
    let X : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
      BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
    let Y : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
    (show X ⥤ᵇ Y from twoYonedaSplit_owner_slice_lift_down U).IsEquivalenceOverBase := by
  -- This is the same strict `AsSmall` equivalence-over-base, viewed in the opposite direction.
  let X : BasedCategory.{max (max u v₁) v₂, max (max u v₁) v₂} C :=
    BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U)
  let Y : BasedCategory.{v₁, max u v₁} C := BasedCategory.ofFunctor (Over.forget U)
  let hdown : X ⥤ᵇ Y := show X ⥤ᵇ Y from twoYonedaSplit_owner_slice_lift_down U
  let hup : Y ⥤ᵇ X := show Y ⥤ᵇ X from twoYonedaSplit_owner_slice_lift_up U
  refine BasedFunctor.IsEquivalenceOverBase.mkPrime
    hup ?_ ?_
  · simpa [hup, hdown] using eqToIso (twoYonedaSplit_owner_slice_lift_up_down U).symm
  · simpa [hup, hdown] using eqToIso (twoYonedaSplit_owner_slice_lift_down_up U)

/-- Helper for Remark 4.41.3: forgetting the lifted slice induces an equivalence on each fiber
over an object of `C`. -/
private theorem twoYonedaSplit_owner_slice_lift_down_fiberFunctor_isEquivalence
    (U V : C) :
    ((twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U).fiberFunctor V).IsEquivalence := by
  -- Fiberwise equivalence follows from the already-packaged equivalence-over-base data.
  exact
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U)
      (twoYonedaSplit_owner_slice_lift_down_isEquivalenceOverBase.{v₁, v₂, u} U)
      V

/-- Helper for Remark 4.41.3: after transporting the target to `AsSmall S`, precomposition with
`lift_down` still evaluates the lifted identity object back to the original raw value at
`id_U : U/U`. -/
private theorem twoYonedaSplit_owner_slice_precompose_target_small_eval_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    ((show
        (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
            BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
          (BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U) ⥤ᵇ
            BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) from
        precomposeBasedFunctor
          (X := BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U))
          (Y := BasedCategory.ofFunctor (Over.forget U))
          (Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p))
          (twoYonedaSplit_owner_slice_lift_down U)).obj F).obj
      ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U))) =
      F.obj (Over.mk (𝟙 U)) := by
  -- This is exactly the generic evaluation formula, specialized to the shrunken target.
  simpa using
    twoYonedaSplit_owner_slice_precompose_eval_obj
      (p := twoYonedaSplit_target_small p) U F

/-- Helper for Remark 4.41.3: after transporting the target to `AsSmall S`, precomposition with
`lift_down` also preserves the component of a based natural transformation at the tautological
identity object. -/
private theorem twoYonedaSplit_owner_slice_precompose_target_small_map_app
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (τ : F ⟶ G) :
    (((show
        (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
            BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
          (BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U) ⥤ᵇ
            BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) from
        precomposeBasedFunctor
          (X := BasedCategory.ofFunctor (twoYonedaSplit_owner_slice_lift_forget U))
          (Y := BasedCategory.ofFunctor (Over.forget U))
          (Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p))
          (twoYonedaSplit_owner_slice_lift_down U)).map τ).toNatTrans.app
      ((twoYonedaSplit_owner_slice_lift_up U).obj (Over.mk (𝟙 U)))) =
      τ.toNatTrans.app (Over.mk (𝟙 U)) := by
  -- Again this is just the generic source-transport comparison, now specialized to `AsSmall S`.
  simpa using
    twoYonedaSplit_owner_slice_precompose_map_app
      (p := twoYonedaSplit_target_small p) U τ

/-- Helper for Remark 4.41.3: after transporting the target to `AsSmall S`, the lifted identity
evaluation still lies over the base object `U`. -/
private theorem twoYonedaSplit_owner_slice_precompose_target_small_eval_base
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (twoYonedaSplit_target_small p).obj
        (((show
            (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
                BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
              (BasedCategory.ofFunctor
                  (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
                BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) from
            precomposeBasedFunctor
              (X := BasedCategory.ofFunctor
                (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U))
              (Y := BasedCategory.ofFunctor (Over.forget U))
              (Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p))
              (twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U)).obj F).obj
          ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U)))) = U := by
  -- The specialized evaluation formula identifies the lifted identity value with the ordinary
  -- value `F(id_U)`, and that object already lies over `U`.
  calc
    (twoYonedaSplit_target_small p).obj
        (((show
            (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
                BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
              (BasedCategory.ofFunctor
                  (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
                BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) from
            precomposeBasedFunctor
              (X := BasedCategory.ofFunctor
                (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U))
              (Y := BasedCategory.ofFunctor (Over.forget U))
              (Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p))
              (twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U)).obj F).obj
          ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U)))) =
        (twoYonedaSplit_target_small p).obj (F.obj (Over.mk (𝟙 U))) := by
          rw [twoYonedaSplit_owner_slice_precompose_target_small_eval_obj p U F]
    _ = U := by
          change
            (twoYonedaSplit_target_small p).obj (F.obj (Over.mk (𝟙 U))) =
              (Over.forget U).obj (Over.mk (𝟙 U))
          exact F.w_obj (Over.mk (𝟙 U))

/-- Helper for Remark 4.41.3: after transporting the target to `AsSmall S`, the component of a
precomposed lifted-slice natural transformation at the lifted identity object is still a lift over
`𝟙 U`. -/
private theorem twoYonedaSplit_owner_slice_precompose_target_small_eval_isHomLift
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (τ : F ⟶ G) :
    (twoYonedaSplit_target_small p).IsHomLift (𝟙 U)
      (((show
          (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
              BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
            (BasedCategory.ofFunctor
                (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
              BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) from
          precomposeBasedFunctor
            (X := BasedCategory.ofFunctor
              (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U))
            (Y := BasedCategory.ofFunctor (Over.forget U))
            (Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p))
            (twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U)).map τ).toNatTrans.app
        ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U)))) := by
  -- The specialized lifted-source transport preserves the same base arrow `𝟙 U`.
  simpa using
    twoYonedaSplit_owner_slice_precompose_eval_isHomLift
      (p := twoYonedaSplit_target_small p) U τ

/-- Helper for Remark 4.41.3: the lifted tautological object of `AsSmall (C/U)` still lies over
the base object `U`. -/
private theorem twoYonedaSplit_owner_slice_lift_identity_base
    (U : C) :
    (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U).obj
        ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))) = U := by
  -- Forgetting the lifted identity object simply returns the ordinary object `id_U : U/U`.
  rfl

/-- Helper for Remark 4.41.3: inserting the ordinary slice into the lifted slice induces an
equivalence on each fiber over an object of `C`. -/
private theorem twoYonedaSplit_owner_slice_lift_up_fiberFunctor_isEquivalence
    (U V : C) :
    ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).fiberFunctor V).IsEquivalence := by
  -- Fiberwise equivalence follows from the already-packaged equivalence-over-base data for
  -- `twoYonedaSplit_owner_slice_lift_up U : C/U ⥤ᵇ AsSmall (C/U)`.
  exact
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U)
      (twoYonedaSplit_owner_slice_lift_up_isEquivalenceOverBase.{v₁, v₂, u} U)
      V

/-- Helper for Remark 4.41.3: on the shrunken target, raw evaluation still reads off the value of
a based functor at the tautological slice object `id_U : U/U`. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).obj F =
      ⟨F.obj (Over.mk (𝟙 U)), by
          change (twoYonedaSplit_target_small p).obj (F.obj (Over.mk (𝟙 U))) =
            (Over.forget U).obj (Over.mk (𝟙 U))
          exact F.w_obj (Over.mk (𝟙 U))⟩ := by
  -- Raw evaluation is definitionally the tautological value together with its base equality.
  rfl

/-- Helper for Remark 4.41.3: on the shrunken target, the map part of raw evaluation is still the
component at `id_U : U/U`. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (τ : F ⟶ G) :
    Fiber.fiberInclusion.map
      ((twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).map τ) =
        τ.app (Over.mk (𝟙 U)) := by
  -- This is the generic raw-evaluation component formula, specialized to the shrunken target.
  simpa using
    twoYonedaSplit_rawEvaluationFunctor_map_hom
      (p := twoYonedaSplit_target_small p) U τ

/-- Helper for Remark 4.41.3: precompose an ordinary slice functor
`C/U ⥤ AsSmall S` along the lifted-slice forgetful functor `AsSmall (C/U) ⥤ C/U`. -/
private abbrev twoYonedaSplit_owner_slice_precompose_target_small
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
      (BasedCategory.ofFunctor
          (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :=
  precomposeBasedFunctor
    (X := BasedCategory.ofFunctor
      (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U))
    (Y := BasedCategory.ofFunctor (Over.forget U))
    (Z := BasedCategory.ofFunctor (twoYonedaSplit_target_small p))
    (twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U)

/-- Helper for Remark 4.41.3: after precomposing with the lifted-slice equivalence on the source,
raw evaluation on `AsSmall S` is the same fiber object as evaluation at the lifted identity
object of `AsSmall (C/U)`. -/
private theorem twoYonedaSplit_owner_slice_precompose_target_small_eval_fiber_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).obj F =
      ⟨((twoYonedaSplit_owner_slice_precompose_target_small p U).obj F).obj
          ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))),
        by
          exact twoYonedaSplit_owner_slice_precompose_target_small_eval_base p U F⟩ := by
  -- The previously computed comparison identifies the underlying evaluated object on the nose.
  apply Subtype.ext
  change
    ((twoYonedaSplit_owner_slice_precompose_target_small p U).obj F).obj
        ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))) =
      F.obj (Over.mk (𝟙 U))
  simpa [twoYonedaSplit_owner_slice_precompose_target_small] using
    twoYonedaSplit_owner_slice_precompose_target_small_eval_obj.{v₁, v₂, u, v₂} p U F

/-- Helper for Remark 4.41.3: the lifted identity object of `AsSmall (C/U)` still maps to `U`. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_obj_base
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (twoYonedaSplit_target_small p).obj
        (F.obj ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U)))) =
      U := by
  -- The based-functor compatibility already computes the base of the lifted identity value.
  let a := (twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))
  change (BasedCategory.ofFunctor (twoYonedaSplit_target_small p)).p.obj (F.obj a) = U
  have h := F.w_obj a
  -- The lifted identity object forgets back to the base object `U`.
  exact h.trans (twoYonedaSplit_owner_slice_lift_identity_base.{v₁, v₂, u} U)

/-- Helper for Remark 4.41.3: the component of a lifted-slice based natural transformation at
the lifted identity object is a morphism over `𝟙 U`. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_map_isHomLift
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (τ : F ⟶ G) :
    (twoYonedaSplit_target_small p).IsHomLift (𝟙 U)
      (τ.toNatTrans.app
        ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U)))) := by
  -- The natural transformation is vertical at every source object, and the lifted identity object
  -- lies over `U`.
  simpa using
    τ.isHomLift' ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U)))

/-- Helper for Remark 4.41.3: on the shrunken target, evaluation at the lifted identity object of
`AsSmall (C/U)` defines a fiber-valued functor on lifted-slice based functors. -/
private noncomputable def twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
      (twoYonedaSplit_target_small p).Fiber U where
  obj F :=
    ⟨F.obj ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))),
      twoYonedaSplit_target_small_liftedIdentityEvaluation_obj_base p U F⟩
  map {F G} τ :=
    let _ :=
      twoYonedaSplit_target_small_liftedIdentityEvaluation_map_isHomLift
        (p := p) (U := U) τ
    Functor.Fiber.homMk (twoYonedaSplit_target_small p) U
      (τ.toNatTrans.app
        ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))))
  map_id := by
    intro F
    -- Evaluation at the lifted identity object turns the identity transformation into the
    -- identity morphism in the fiber over `U`.
    apply Functor.Fiber.hom_ext
    rfl
  map_comp := by
    intro F G H τ σ
    -- Composition is still computed componentwise at the lifted identity object.
    apply Functor.Fiber.hom_ext
    rfl

/-- Helper for Remark 4.41.3: on the shrunken target, the map part of lifted-identity evaluation
is the component of the based natural transformation at the lifted identity object. -/
@[simp] private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (τ : F ⟶ G) :
    Fiber.fiberInclusion.map
      ((twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).map τ) =
        τ.toNatTrans.app
          ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))) := by
  -- The lifted-identity evaluation functor was defined by taking this component in the fiber.
  rfl

/-- Helper for Remark 4.41.3: forgetting an equality morphism in a fiber recovers the
corresponding equality morphism on the underlying ambient objects. -/
private theorem twoYonedaSplit_fiber_eqToHom_map
    {T : Type uY} [Category.{vY} T] {q : T ⥤ C} {U : C}
    {P Q : q.Fiber U} (h : P = Q) :
    Functor.Fiber.fiberInclusion.map (eqToHom h) = eqToHom (congrArg Subtype.val h) := by
  -- Equality morphisms in the fiber are defined by the same underlying morphisms in the total
  -- category.
  cases h
  rfl

/-- Helper for Remark 4.41.3: the shrunken target still carries a fibered structure, so it can be
packaged as an owner object of fibred categories. -/
private noncomputable instance twoYonedaSplit_target_small_instIsFibered
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (twoYonedaSplit_target_small p).IsFibered :=
  twoYonedaSplit_target_small_isFibered p

/-- Helper for Remark 4.41.3: after transporting the source to the lifted slice, evaluation at
the lifted identity object agrees objectwise with raw evaluation at `id_U : U/U` on the shrunken
target. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    ((twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
        twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).obj F) =
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).obj F := by
  -- The lifted identity object in `AsSmall (C/U)` evaluates to the same fiber object as `id_U`
  -- after forgetting the `ULiftHom` wrapper along `lift_down`.
  symm
  exact twoYonedaSplit_owner_slice_precompose_target_small_eval_fiber_obj p U F

/-- Helper for Remark 4.41.3: the underlying object equality in the previous comparison is the
explicit evaluation equality on total-space objects. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_obj_val
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    congrArg Subtype.val
        (twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_obj p U F) =
      twoYonedaSplit_owner_slice_precompose_target_small_eval_obj p U F := by
  -- Both equalities come from the same computation of the evaluated underlying object.
  rfl

/-- Helper for Remark 4.41.3: after transporting the source to the lifted slice, the map part of
lifted-identity evaluation is still the component at `id_U : U/U` on the shrunken target. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (τ : F ⟶ G) :
    Fiber.fiberInclusion.map
      ((twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
          twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).map τ) =
        τ.toNatTrans.app (Over.mk (𝟙 U)) := by
  -- The lifted evaluation functor reads the component at the lifted identity object, and the
  -- precomposition comparison identifies that lifted component with the original component at
  -- `id_U`.
  simpa [Functor.comp_map] using
    (twoYonedaSplit_target_small_liftedIdentityEvaluation_map_hom
      (p := p) (U := U)
      (τ := (twoYonedaSplit_owner_slice_precompose_target_small p U).map τ))

/-- Helper for Remark 4.41.3: after precomposing ordinary-slice functors with `lift_down`, the
underlying map of lifted-identity evaluation is still the original component at `id_U : U/U`. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_underlying_map
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G) :
    Fiber.fiberInclusion.map
      ((twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
          twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).map η) =
        η.app (Over.mk (𝟙 U)) := by
  -- This is exactly the previously established lifted-identity comparison on maps.
  exact
    twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_map_hom
      (p := p) (U := U) (τ := η)

/-- Helper for Remark 4.41.3: the ordinary slice `C/U` packaged as a fibred category owner with
its source universes pinned explicitly. -/
private abbrev twoYonedaSplit_source_owner (U : C) :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor.{u, v₁, v₁, max u v₁} (Over.forget U)


/-- Helper for Remark 4.41.3: the shrunken target `AsSmall S` packaged as a fibred category owner
with its target universes pinned explicitly. -/
private abbrev twoYonedaSplit_target_small_owner
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor.{u, v₁, max (max u v₁) v₂, max (max u v₁) v₂}
    (twoYonedaSplit_target_small p)

/-- Helper for Remark 4.41.3: forgetting the pinned ordinary-slice owner recovers the usual slice
based category over `C`. -/
private theorem twoYonedaSplit_source_owner_toBasedCategory
    (U : C) :
    FibredCategoryOver.toBasedCategory (twoYonedaSplit_source_owner U) =
      BasedCategory.ofFunctor (Over.forget U) :=
  rfl

/-- Helper for Remark 4.41.3: forgetting the pinned shrunken target owner recovers the expected
based category over `C`. -/
private theorem twoYonedaSplit_target_small_owner_toBasedCategory
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredCategoryOver.toBasedCategory (twoYonedaSplit_target_small_owner p) =
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p) :=
  rfl


/-- Helper for Remark 4.41.3: the owner packaging of the ordinary slice really projects by the
usual slice forgetful functor `C/U ⥤ C`. -/
private theorem twoYonedaSplit_source_owner_projection
    (U : C) :
    (twoYonedaSplit_source_owner U).p = Over.forget U := by
  rfl

/-- Helper for Remark 4.41.3: the imported owner `2`-Yoneda lemma already gives an equivalence
for evaluation on the ordinary slice owner `C/U` in the small ambient. -/
private theorem twoYonedaSplit_source_owner_yonedaEvaluation_isEquivalence
    (U : C) :
    ((twoYonedaSplit_source_owner U).yonedaEvaluationFunctor U).IsEquivalence := by
  -- This is exactly the small-ambient owner theorem imported from Lemma 4.41.2.
  exact
    FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence
      (X := twoYonedaSplit_source_owner U) U

/-- Helper for Remark 4.41.3: the owner packaging of the shrunken target really projects by the
expected functor `AsSmall S ⥤ C`. -/
private theorem twoYonedaSplit_target_small_owner_projection
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (twoYonedaSplit_target_small_owner p).p = twoYonedaSplit_target_small p := by
  rfl

/-- Helper for Remark 4.41.3: after precomposing from the ordinary slice to the lifted slice,
lifted-identity evaluation agrees with raw evaluation on `AsSmall S`. -/
private noncomputable def twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_comparison
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
        twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U ≅
      twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U :=
  -- Package the already established objectwise and morphismwise comparison into a natural
  -- isomorphism of evaluation functors.
  NatIso.ofComponents
    (fun F ↦
      eqToIso (twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_obj p U F))
    (by
      intro F G η
      -- After the object comparisons are reduced to reflexive equalities, both map formulas are
      -- the same component at `id_U : U/U`.
      cases twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_obj p U F
      cases twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_obj p U G
      apply Functor.Fiber.hom_ext
      simp only [comp_obj, Functor.comp_map, eqToIso.hom, map_comp,
        twoYonedaSplit_target_small_liftedIdentityEvaluation_map_hom,
        twoYonedaSplit_rawEvaluationFunctor_map_hom]
      rw [twoYonedaSplit_owner_slice_precompose_target_small_map_app]
      have hnat :=
        (η.naturality
          (eqToHom (twoYonedaSplit_owner_slice_lift_identity_obj.{v₁, u, v₂} U))).symm
      simpa only [eqToHom_map, twoYonedaSplit_owner_slice_precompose_target_small_eval_obj,
        Category.assoc] using hnat)

/-- Helper for Remark 4.41.3: lifted-identity evaluation on `AsSmall S` packages the obvious
value of a lifted-slice based functor at the lifted identity object. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).obj F =
      ⟨F.obj ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))),
        twoYonedaSplit_target_small_liftedIdentityEvaluation_obj_base p U F⟩ := by
  -- The lifted-identity evaluation functor was defined by exactly this fiber object.
  rfl

/-- Helper for Remark 4.41.3: once lifted-identity evaluation on `AsSmall (C/U)` is known to be
be an equivalence, composing with the source-side lift equivalence already gives an equivalence on
the precomposed lifted-identity evaluation functor. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hlifted :
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence) :
    (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
        twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence := by
  have hpre :
      (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence :=
    twoYonedaSplit_owner_slice_precompose_target_small_isEquivalence p U
  letI : (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence := hpre
  letI :
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence :=
    hlifted
  -- Compose the source-side lift equivalence with lifted-identity evaluation on `AsSmall S`.
  let Epre := (twoYonedaSplit_owner_slice_precompose_target_small p U).asEquivalence
  let Elifted := (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).asEquivalence
  exact (Epre.trans Elifted).isEquivalence_functor

/-- Helper for Remark 4.41.3: once lifted-identity evaluation on `AsSmall (C/U)` is known to be
an equivalence, the already-proved source precomposition comparison transports that equivalence to
raw evaluation on the shrunken target `AsSmall S`. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_isEquivalence_of_liftedIdentity
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hlifted :
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence) :
    (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence := by
  have hcomp :
      (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
          twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence :=
    twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_isEquivalence p U hlifted
  -- Then rewrite the composite back to raw evaluation using the established natural isomorphism.
  exact
    (Functor.isEquivalence_iff_of_iso
      (twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_comparison p U)).1
      hcomp

/-- Helper for Remark 4.41.3: forgetting the lifted identity object along `lift_down` recovers
the ordinary identity object `id_U : U/U`. -/
private theorem twoYonedaSplit_owner_slice_lift_down_lifted_identity
    (U : C) :
    (twoYonedaSplit_owner_slice_lift_down.{v₁, u, v₂} U).obj
        ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))) =
      Over.mk (𝟙 U) := by
  rfl

/-- Helper for Remark 4.41.3: on the shrunken target, the source-side lift equivalence and the
comparison from lifted-identity evaluation back to raw evaluation are both already established. -/
private theorem twoYonedaSplit_target_small_liftedIdentity_frontier
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence ∧
      Nonempty
        (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
            twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U ≅
          twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U) := by
  constructor
  · -- The lifted-slice source is already equivalent to the ordinary slice by precomposition with
    -- `lift_down`.
    exact twoYonedaSplit_owner_slice_precompose_target_small_isEquivalence p U
  · -- The comparison with raw evaluation was already packaged as a natural isomorphism.
    exact ⟨twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_comparison p U⟩

/-- Helper for Remark 4.41.3: on the shrunken target, lifted-identity evaluation is an
equivalence exactly when raw evaluation is. This packages the already-proved source transport and
comparison isomorphism into a single reusable frontier statement. -/
private theorem twoYonedaSplit_target_small_liftedIdentity_isEquivalence_iff_rawEvaluation
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence ↔
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence := by
  constructor
  · -- This is the previously established transport from lifted-identity evaluation to raw
    -- evaluation on `AsSmall S`.
    exact twoYonedaSplit_target_small_rawEvaluation_isEquivalence_of_liftedIdentity p U
  · intro hraw
    have hpre :
        (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence :=
      twoYonedaSplit_owner_slice_precompose_target_small_isEquivalence p U
    have hcomp :
        (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
            twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence := by
      -- First rewrite raw evaluation back to the composite with lifted-identity evaluation.
      exact
        (Functor.isEquivalence_iff_of_iso
          (twoYonedaSplit_target_small_liftedIdentityEvaluation_precompose_comparison p U)).2
          hraw
    letI :
        (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence :=
      hpre
    letI :
        (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
            twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence :=
      hcomp
    -- Then cancel the source-side lift equivalence on the left.
    simpa using
      Functor.isEquivalence_of_comp_left
        (twoYonedaSplit_owner_slice_precompose_target_small p U)
        (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U)

/-- Helper for Remark 4.41.3: on the shrunken target, any equivalence proof for raw evaluation
can already be transported back to the lifted-identity evaluation functor on
`AsSmall (C/U) ⥤ᵇ AsSmall S`. -/
private theorem twoYonedaSplit_target_small_liftedIdentity_isEquivalence_of_rawEvaluation
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence →
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence := by
  intro hraw
  -- This is the reverse implication of the already-stabilized frontier equivalence.
  exact
    (twoYonedaSplit_target_small_liftedIdentity_isEquivalence_iff_rawEvaluation p U).2
      hraw

/-- Helper for Remark 4.41.3: if the source-side precomposition composite with lifted-identity
evaluation on `AsSmall S` is an equivalence, then lifted-identity evaluation itself is already an
equivalence. -/
private theorem twoYonedaSplit_target_small_liftedIdentity_isEquivalence_of_precompose
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hcomp :
      (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
          twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence) :
    (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence := by
  have hpre :
      (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence :=
    twoYonedaSplit_owner_slice_precompose_target_small_isEquivalence p U
  letI :
      (twoYonedaSplit_owner_slice_precompose_target_small p U).IsEquivalence :=
    hpre
  letI :
      (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
          twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence :=
    hcomp
  -- Cancel the source-side lift equivalence on the left to recover lifted-identity evaluation.
  simpa using
    Functor.isEquivalence_of_comp_left
      (twoYonedaSplit_owner_slice_precompose_target_small p U)
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U)

/-- Helper for Remark 4.41.3: once the universe-compatible owner transport yields an equivalence
for the lifted-source composite on `AsSmall S`, the main raw-evaluation equivalence follows by the
already-established lifted-identity frontier. -/
private theorem twoYonedaSplit_rawEvaluation_isEquivalence_of_precompose_liftedIdentity
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hcomp :
      (twoYonedaSplit_owner_slice_precompose_target_small p U ⋙
          twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence) :
    (twoYonedaSplit_rawEvaluationFunctor p U).IsEquivalence := by
  have hlifted :
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence :=
    twoYonedaSplit_target_small_liftedIdentity_isEquivalence_of_precompose p U hcomp
  have hsmall :
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence :=
    twoYonedaSplit_target_small_rawEvaluation_isEquivalence_of_liftedIdentity p U hlifted
  -- The remainder is exactly the previously stabilized target-side transport out of `AsSmall S`.
  exact twoYonedaSplit_rawEvaluation_isEquivalence_of_target_small p U hsmall

/-- Helper for Remark 4.41.3: once lifted-identity evaluation is an equivalence on the shrunken
target `AsSmall S`, the rest of the remark already follows by the established source-side and
target-side transports. -/
private theorem twoYonedaSplit_rawEvaluation_isEquivalence_of_liftedIdentity
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (hlifted :
      (twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).IsEquivalence) :
    (twoYonedaSplit_rawEvaluationFunctor p U).IsEquivalence := by
  -- First transport lifted-identity evaluation to raw evaluation on the shrunken target.
  have hsmall :
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence :=
    twoYonedaSplit_target_small_rawEvaluation_isEquivalence_of_liftedIdentity p U hlifted
  -- Then remove the target-side `AsSmall` wrapper using the previously proved comparison.
  exact twoYonedaSplit_rawEvaluation_isEquivalence_of_target_small p U hsmall

/-- Helper for Remark 4.41.3: once raw evaluation is known to be an equivalence on the shrunken
target `AsSmall S`, the main raw-evaluation theorem for `S` follows immediately. -/
private theorem twoYonedaSplit_rawEvaluation_reduce_to_target_small
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence →
      (twoYonedaSplit_rawEvaluationFunctor p U).IsEquivalence := by
  -- This is exactly the previously established target-side transport out of `AsSmall S`.
  intro hsmall
  exact twoYonedaSplit_rawEvaluation_isEquivalence_of_target_small p U hsmall

/-- Helper for Remark 4.41.3: an ordinary slice-based functor into the shrunken target can be
viewed without change as a based functor between the owner-packaged source and target. -/
private theorem twoYonedaSplit_target_small_owner_basedFunctor_cast
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_small_owner p).toBasedCategory from F) =
      F := by
  -- Both owner-packaged based categories are definitionally the ordinary slice and shrunken
  -- target based categories.
  rfl

/-- Helper for Remark 4.41.3: after reinterpreting an ordinary slice-based functor as a functor
between the owner-packaged based categories, it still preserves strongly cartesian morphisms. -/
private theorem twoYonedaSplit_target_small_owner_basedFunctor_preserves_strongly_cartesian
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_small_owner p).toBasedCategory from F).PreservesStronglyCartesian := by
  -- This is exactly the previously established fibred-in-groupoids preservation statement, after
  -- rewriting the owner-packaged based categories back to their ordinary definitions.
  simpa using
    (twoYonedaSplit_any_preserves_strongly_cartesian
      (p := twoYonedaSplit_target_small p) F)

/-- Helper for Remark 4.41.3: the same reinterpretation of ordinary raw-domain objects in the
owner-packaged source and target categories leaves based natural transformations unchanged. -/
private theorem twoYonedaSplit_target_small_owner_basedFunctor_map_cast
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G) :
    (show
        (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from F) ⟶
          (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from G) from η) =
      η := by
  rfl


/-- Helper for Remark 4.41.3: the canonical source owner used by the imported `2`-Yoneda
evaluation theorem still forgets to the ordinary slice-based functor category. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_cast
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_small_owner p).toBasedCategory from F) =
      F := by
  rfl

/-- Helper for Remark 4.41.3: viewed in the exact source owner expected by the imported
`2`-Yoneda theorem, an ordinary slice-based functor still preserves strongly cartesian morphisms.
-/
private theorem twoYonedaSplit_target_small_owner_rawDomain_preserves_strongly_cartesian
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_small_owner p).toBasedCategory from F).PreservesStronglyCartesian := by
  simpa using
    (twoYonedaSplit_any_preserves_strongly_cartesian
      (p := twoYonedaSplit_target_small p) F)

/-- Helper for Remark 4.41.3: the same reinterpretation of ordinary raw-domain objects in the
exact owner-based categories leaves based natural transformations unchanged. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_map_cast
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G) :
    (show
        (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from F) ⟶
          (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from G) from η) =
      η := by
  rfl

/-- Helper for Remark 4.41.3: after packaging the exact owner source and target based categories,
the remaining obstruction is only the ambient owner hom-universe, not the objectwise or mapwise
evaluation formulas. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_frontier
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (∀ F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p),
        (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from F) = F) ∧
      (∀ {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
          BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G),
        (show
            (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
                (twoYonedaSplit_target_small_owner p).toBasedCategory from F) ⟶
              (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
                (twoYonedaSplit_target_small_owner p).toBasedCategory from G) from η) =
          η) := by
  constructor
  · intro F
    exact twoYonedaSplit_target_small_owner_rawDomain_cast p U F
  · intro F G η
    exact twoYonedaSplit_target_small_owner_rawDomain_map_cast p U η

/-- Helper for Remark 4.41.3: lifted-identity evaluation on the shrunken target remembers the
same underlying total object as evaluating the lifted-slice based functor at the lifted identity
object. -/
private theorem twoYonedaSplit_target_small_liftedIdentityEvaluation_obj_val
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor
        (twoYonedaSplit_owner_slice_lift_forget.{v₁, u, v₂} U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    Functor.Fiber.fiberInclusion.obj
      ((twoYonedaSplit_target_small_liftedIdentityEvaluationFunctor p U).obj F) =
        F.obj ((twoYonedaSplit_owner_slice_lift_up.{v₁, u, v₂} U).obj (Over.mk (𝟙 U))) := by
  -- Unfold the lifted-identity evaluation functor: its object is definitionally the evaluation
  -- of `F` at the lifted tautological slice object.
  rfl

/-- Helper for Remark 4.41.3: raw evaluation on the shrunken target remembers the same
underlying total object as evaluating the ordinary slice-based functor at `id_U : U/U`. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_obj_val
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    Functor.Fiber.fiberInclusion.obj
      ((twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).obj F) =
        F.obj (Over.mk (𝟙 U)) := by
  -- Unfold the raw evaluation functor: its object is definitionally the value of `F` at the
  -- tautological slice object `id_U : U/U`.
  rfl

/-- Helper for Remark 4.41.3: the exact ambient-owner raw-domain packaging data are now stable:
the ordinary slice-based functor is unchanged after casting to the owner-packaged based
categories, it preserves strongly cartesian morphisms there, and the same strict cast behavior
holds on based natural transformations. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_packaging_frontier
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (∀ F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p),
        ((show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from F) = F) ∧
          (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
              (twoYonedaSplit_target_small_owner p).toBasedCategory from F).PreservesStronglyCartesian) ∧
      (∀ {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
          BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G),
        (show
            (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
                (twoYonedaSplit_target_small_owner p).toBasedCategory from F) ⟶
              (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
                (twoYonedaSplit_target_small_owner p).toBasedCategory from G) from η) =
          η) := by
  constructor
  · intro F
    -- Objectwise the owner packaging is strict, and preservation of strongly cartesian morphisms
    -- is already available on the packaged based functor.
    exact
      ⟨twoYonedaSplit_target_small_owner_rawDomain_cast p U F,
        twoYonedaSplit_target_small_owner_rawDomain_preserves_strongly_cartesian p U F⟩
  · intro F G η
    -- On `2`-morphisms the same owner packaging remains strict.
    exact twoYonedaSplit_target_small_owner_rawDomain_map_cast p U η

/-- Helper for Remark 4.41.3: for a fixed raw-domain object, the direct owner-side packaging data
are already complete at the based-functor level. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_packaged_object
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    ((show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_small_owner p).toBasedCategory from F) = F) ∧
      (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_small_owner p).toBasedCategory from F).PreservesStronglyCartesian := by
  -- This is the objectwise half of the stabilized frontier, extracted for direct reuse at the
  -- eventual source-side bridge.
  exact
    ⟨twoYonedaSplit_target_small_owner_rawDomain_cast p U F,
      twoYonedaSplit_target_small_owner_rawDomain_preserves_strongly_cartesian p U F⟩

/-- Helper for Remark 4.41.3: the strict cast identifying the owner-packaged raw-domain object
with the original based functor is natural in raw-domain morphisms. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_cast_naturality
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G) :
    eqToHom (twoYonedaSplit_target_small_owner_rawDomain_cast p U F) ≫ η =
      (show
          (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
              (twoYonedaSplit_target_small_owner p).toBasedCategory from F) ⟶
            (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
              (twoYonedaSplit_target_small_owner p).toBasedCategory from G) from η) ≫
        eqToHom (twoYonedaSplit_target_small_owner_rawDomain_cast p U G) := by
  -- Both sides are the same strict cast of the underlying based natural transformation.
  cases twoYonedaSplit_target_small_owner_rawDomain_cast p U F
  cases twoYonedaSplit_target_small_owner_rawDomain_cast p U G
  ext a
  simp

/-- Helper for Remark 4.41.3: on the shrunken target, the raw evaluation functor is already
strictly understood on both objects and morphisms before any owner-level packaging. -/
private theorem twoYonedaSplit_target_small_rawEvaluation_frontier
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (∀ F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p),
        Functor.Fiber.fiberInclusion.obj
          ((twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).obj F) =
            F.obj (Over.mk (𝟙 U))) ∧
      (∀ {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
          BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G),
        Functor.Fiber.fiberInclusion.map
          ((twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).map η) =
            η.app (Over.mk (𝟙 U))) := by
  constructor
  · intro F
    -- Objectwise raw evaluation is definitionally evaluation at `id_U : U/U`.
    exact twoYonedaSplit_target_small_rawEvaluation_obj_val p U F
  · intro F G η
    -- On maps raw evaluation is the component at `id_U : U/U`.
    exact twoYonedaSplit_target_small_rawEvaluation_map_hom p U η

/-- Helper for Remark 4.41.3: every ordinary raw-domain object already lies in the full
subcategory of based functors preserving strongly cartesian morphisms for the exact owner source
and target used by the imported `2`-Yoneda theorem. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_objectProperty_mem
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    FibredCategoryMor.objectProperty
        (twoYonedaSplit_source_owner U)
        (twoYonedaSplit_target_small_owner p)
        (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from F) := by
  -- This is exactly the already-established preservation statement in the owner-based coordinates.
  simpa [FibredCategoryMor.objectProperty] using
    twoYonedaSplit_target_small_owner_rawDomain_preserves_strongly_cartesian p U F

/-- Helper for Remark 4.41.3: the ordinary raw-domain category factors through the full
subcategory of owner-admissible based functors by remembering the already-proved strongly
cartesian preservation property. -/
private noncomputable abbrev twoYonedaSplit_target_small_owner_rawDomain_objectProperty
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) ⥤
      (FibredCategoryMor.objectProperty
          (twoYonedaSplit_source_owner U)
          (twoYonedaSplit_target_small_owner p)).FullSubcategory :=
  let P :
      ObjectProperty
        ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_small_owner p).toBasedCategory) :=
    FibredCategoryMor.objectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_small_owner p)
  P.lift (𝟭 _) (twoYonedaSplit_target_small_owner_rawDomain_objectProperty_mem p U)

/-- Helper for Remark 4.41.3: passing from the ordinary raw domain to the full subcategory of
owner-admissible based functors is only bookkeeping, so this lift is an equivalence. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_objectProperty_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).IsEquivalence := by
  let P :
      ObjectProperty
        ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_small_owner p).toBasedCategory) :=
    FibredCategoryMor.objectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_small_owner p)
  let F :
      ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_small_owner p).toBasedCategory) ⥤
        P.FullSubcategory :=
    twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U
  let G : P.FullSubcategory ⥤
      ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_small_owner p).toBasedCategory) :=
    P.ι
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- Forgetting the remembered object-property proof recovers the original raw-domain functor.
    simpa [F, G] using
      (P.liftCompιIso
        (F := 𝟭 _)
        (twoYonedaSplit_target_small_owner_rawDomain_objectProperty_mem p U)).symm
  · -- Reattaching the remembered property changes only proof fields, so the counit is the
    -- identity on the underlying based functors.
    refine NatIso.ofComponents
      (fun A ↦
        ObjectProperty.isoMk
          (P := P)
          (X := (G ⋙ F).obj A)
          (Y := A)
          (Iso.refl A.obj)) ?_
    intro A B f
    ext x
    simpa [G]

/-- Helper for Remark 4.41.3: forgetting an owner morphism to its underlying based functor and
repackaging it with the same preservation proof leaves the owner morphism unchanged. -/
private theorem twoYonedaSplit_ofBasedFunctor_toBasedFunctor
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    FibredCategoryMor.ofBasedFunctor (FibredCategoryMor.toBasedFunctor F) F.obj.property = F := by
  -- This is definitional: an owner morphism is already a based functor together with exactly this
  -- preservation proof.
  rfl

/-- Helper for Remark 4.41.3: forgetting the owner wrapper on a based functor packaged by
`ofBasedFunctor` recovers the original based functor strictly. -/
private theorem twoYonedaSplit_toBasedFunctor_ofBasedFunctor
    {X Y : FibredCategoryOver C}
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hF : F.PreservesStronglyCartesian) :
    FibredCategoryMor.toBasedFunctor (FibredCategoryMor.ofBasedFunctor F hF) = F := by
  -- The underlying based functor of `ofBasedFunctor F hF` is definitionally `F`.
  rfl

/-- Helper for Remark 4.41.3: the raw-domain lift to the admissible full subcategory remembers
exactly the original based functor together with the already-proved strongly-cartesian
preservation property. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_objectProperty_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).obj F =
      ⟨show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_small_owner p).toBasedCategory from F,
        twoYonedaSplit_target_small_owner_rawDomain_objectProperty_mem p U F⟩ := by
  -- The full-subcategory lift was defined by packaging `F` with this exact proof.
  rfl

/-- Helper for Remark 4.41.3: on morphisms, the raw-domain lift to the admissible full
subcategory leaves the underlying based natural transformation unchanged. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_objectProperty_map
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G) :
    (((twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).map η).hom) = η := by
  -- The lift uses `P.lift (𝟭 _)`, so morphisms are remembered strictly.
  rfl

/-- Helper for Remark 4.41.3: forgetting the remembered strongly-cartesian preservation proof from
the raw-domain object-property lift is strictly the identity on the ordinary raw-domain category.
-/
private noncomputable def twoYonedaSplit_target_small_owner_rawDomain_objectProperty_forgetIso
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U ⋙
        (FibredCategoryMor.objectProperty
          (twoYonedaSplit_source_owner U)
          (twoYonedaSplit_target_small_owner p)).ι ≅
      𝟭 (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) := by
  let P :
      ObjectProperty
        ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_small_owner p).toBasedCategory) :=
    FibredCategoryMor.objectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_small_owner p)
  -- The lift `P.lift (𝟭 _)` was defined precisely so that forgetting the remembered property is
  -- the identity on the ordinary raw-domain functor category.
  simpa [P, twoYonedaSplit_target_small_owner_rawDomain_objectProperty] using
    (P.liftCompιIso
      (F := 𝟭 (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor (twoYonedaSplit_target_small p)))
      (twoYonedaSplit_target_small_owner_rawDomain_objectProperty_mem p U)).symm

/-- Helper for Remark 4.41.3: the stabilized raw-domain bookkeeping layer already consists of an
equivalence into the admissible object-property full subcategory together with the strict
comparison that forgetting that bookkeeping is the identity on the ordinary raw domain. -/
private theorem twoYonedaSplit_target_small_owner_rawDomain_bookkeeping_frontier
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).IsEquivalence ∧
      Nonempty
        (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U ⋙
            (FibredCategoryMor.objectProperty
              (twoYonedaSplit_source_owner U)
              (twoYonedaSplit_target_small_owner p)).ι ≅
          𝟭 (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
            BasedCategory.ofFunctor (twoYonedaSplit_target_small p))) := by
  constructor
  · -- The bookkeeping lift itself is already an equivalence.
    exact twoYonedaSplit_target_small_owner_rawDomain_objectProperty_isEquivalence p U
  · -- Forgetting the remembered strongly-cartesian proof is strictly the identity.
    exact ⟨twoYonedaSplit_target_small_owner_rawDomain_objectProperty_forgetIso p U⟩

/-- Helper for Remark 4.41.3: packaging an admissible based functor as an owner morphism is an
equivalence, because the owner hom-category only adds the trivial wide-subcategory wrapper on
`2`-morphisms. -/
private theorem twoYonedaSplit_target_small_owner_ofObjectProperty_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (FibredCategoryMor.ofObjectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_small_owner p)).IsEquivalence := by
  let X := twoYonedaSplit_source_owner U
  let Y := twoYonedaSplit_target_small_owner p
  let F :
      (FibredCategoryMor.objectProperty X Y).FullSubcategory ⥤
        (X ⟶ Y) :=
    FibredCategoryMor.ofObjectProperty X Y
  let G :
      (X ⟶ Y) ⥤
        (FibredCategoryMor.objectProperty X Y).FullSubcategory :=
    wideSubcategoryInclusion ((fibredCategoryOverSubTwoCategory C).hom₂ X Y)
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · -- On admissible based functors, packaging as an owner morphism and then forgetting the
    -- trivial wide-subcategory proof changes nothing.
    apply eqToIso
    refine CategoryTheory.Functor.ext (fun A ↦ ?_) (fun A B η ↦ ?_)
    · cases A
      rfl
    · cases η
      rfl
  · -- On owner morphisms, forgetting to the admissible based functor and repackaging is
    -- definitionally the identity.
    apply eqToIso
    refine CategoryTheory.Functor.ext (fun A ↦ ?_) (fun A B η ↦ ?_)
    · exact twoYonedaSplit_ofBasedFunctor_toBasedFunctor A
    · cases A
      cases B
      cases η
      rfl

/-- Helper for Remark 4.41.3: after lifting an ordinary raw-domain object to the admissible full
subcategory and then packaging it as an owner morphism, owner evaluation at `id_U : U/U` has the
same underlying fiber object as raw evaluation on the shrunken target. -/
private theorem twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)) :
    ((twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U ⋙
          FibredCategoryMor.ofObjectProperty
            (twoYonedaSplit_source_owner U)
            (twoYonedaSplit_target_small_owner p) ⋙
          (twoYonedaSplit_target_small_owner p).yonedaEvaluationFunctor U).obj F) =
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).obj F := by
  -- Both functors evaluate the same underlying based functor at the tautological slice object
  -- `id_U : U/U`; only proof fields differ, and those are irrelevant in the fiber.
  apply Subtype.ext
  rfl

/-- Helper for Remark 4.41.3: after the same owner-side packaging, the underlying map of
evaluation is still the component at `id_U : U/U`. -/
private theorem twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (twoYonedaSplit_target_small p)} (η : F ⟶ G) :
    Functor.Fiber.fiberInclusion.map
      ((twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U ⋙
            FibredCategoryMor.ofObjectProperty
              (twoYonedaSplit_source_owner U)
              (twoYonedaSplit_target_small_owner p) ⋙
            (twoYonedaSplit_target_small_owner p).yonedaEvaluationFunctor U).map η) =
      η.app (Over.mk (𝟙 U)) := by
  -- The owner evaluation functor forgets to the same based natural transformation and reads off
  -- its component at `id_U : U/U`.
  rfl

/-- Helper for Remark 4.41.3: after transporting the ordinary raw domain through the admissible
object-property layer and the generic owner bridge, owner evaluation agrees with raw evaluation on
the shrunken target `AsSmall S`. -/
private noncomputable def
    twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_comparison
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U ⋙
        FibredCategoryMor.ofObjectProperty
          (twoYonedaSplit_source_owner U)
          (twoYonedaSplit_target_small_owner p) ⋙
        (twoYonedaSplit_target_small_owner p).yonedaEvaluationFunctor U ≅
      twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U :=
  NatIso.ofComponents
    (fun F ↦
      eqToIso
        (twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_obj p U F))
    (by
      intro F G η
      -- After the object comparisons are reduced to reflexive equalities, both map formulas are
      -- the same component at `id_U : U/U`.
      cases twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_obj p U F
      cases twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_obj p U G
      apply Functor.Fiber.hom_ext
      rw [twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_map_hom]
      exact twoYonedaSplit_target_small_rawEvaluation_map_hom p U η)

private theorem twoYonedaSplit_rawEvaluation_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_rawEvaluationFunctor p U).IsEquivalence := by
  let X := twoYonedaSplit_source_owner U
  let Y := twoYonedaSplit_target_small_owner p
  have hrawDomain :
      (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).IsEquivalence :=
    twoYonedaSplit_target_small_owner_rawDomain_objectProperty_isEquivalence p U
  have hofObjectProperty :
      (FibredCategoryMor.ofObjectProperty X Y).IsEquivalence :=
    twoYonedaSplit_target_small_owner_ofObjectProperty_isEquivalence p U
  have hyoneda :
      (Y.yonedaEvaluationFunctor U).IsEquivalence := by
    -- This is the imported owner `2`-Yoneda equivalence specialized to the shrunken target.
    exact FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence (X := Y) U
  have hsmallComposite :
      (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U ⋙
          FibredCategoryMor.ofObjectProperty X Y ⋙
          Y.yonedaEvaluationFunctor U).IsEquivalence := by
    -- Compose the raw-domain bookkeeping equivalence, the generic owner bridge, and the imported
    -- owner `2`-Yoneda equivalence.
    letI :
        (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).IsEquivalence :=
      hrawDomain
    letI : (FibredCategoryMor.ofObjectProperty X Y).IsEquivalence := hofObjectProperty
    letI : (Y.yonedaEvaluationFunctor U).IsEquivalence := hyoneda
    let Eraw := (twoYonedaSplit_target_small_owner_rawDomain_objectProperty p U).asEquivalence
    let Eowner := (FibredCategoryMor.ofObjectProperty X Y).asEquivalence
    let Eyoneda := (Y.yonedaEvaluationFunctor U).asEquivalence
    exact ((Eraw.trans Eowner).trans Eyoneda).isEquivalence_functor
  have hsmall :
      (twoYonedaSplit_rawEvaluationFunctor (twoYonedaSplit_target_small p) U).IsEquivalence := by
    -- Rewrite the owner-side evaluation composite back to the already-understood raw evaluation
    -- on `AsSmall S`.
    exact
      (Functor.isEquivalence_iff_of_iso
        (twoYonedaSplit_target_small_owner_rawEvaluation_ofObjectProperty_comparison p U)).1
        hsmallComposite
  -- Finally remove the target-side `AsSmall` wrapper using the earlier transport theorem.
  exact twoYonedaSplit_rawEvaluation_isEquivalence_of_target_small p U hsmall


-/

/-- Helper for Remark 4.41.3: the ordinary slice `C/U`, bundled as a fibred category over `C`. -/
private abbrev twoYonedaSplit_source_owner (U : C) :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor (Over.forget U)

/-- Helper for Remark 4.41.3: the original fibred-in-groupoids target bundled as a fibred category
over `C`. -/
private abbrev twoYonedaSplit_target_owner
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor p


/-- Helper for Remark 4.41.3: evaluation of a raw split-model object at `id_U : U/U` gives the
fiber object appearing in the comparison functor `G_U`. -/
private noncomputable def twoYonedaSplit_rawEvaluationFunctor
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    twoYonedaGroupoidPresheafValue p U ⥤ p.Fiber U where
  obj F :=
    ⟨F.obj (Over.mk (𝟙 U)), by
      let h :
          p.obj (F.obj (Over.mk (𝟙 U))) =
            (Over.forget U).obj (Over.mk (𝟙 U)) :=
        F.w_obj (Over.mk (𝟙 U))
      simpa using h⟩
  map {F G} τ :=
    let _ : p.IsHomLift (𝟙 U) (τ.toNatTrans.app (Over.mk (𝟙 U))) :=
      τ.isHomLift' (Over.mk (𝟙 U))
    Functor.Fiber.homMk p U (τ.toNatTrans.app (Over.mk (𝟙 U)))
  map_id := by
    intro F
    apply Functor.Fiber.hom_ext
    rfl
  map_comp := by
    intro F G H τ σ
    apply Functor.Fiber.hom_ext
    rfl

/-- Helper for Remark 4.41.3: the underlying morphism of raw evaluation on a based natural
transformation is its component at the tautological slice object `id_U : U/U`. -/
@[simp] private theorem twoYonedaSplit_rawEvaluationFunctor_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : twoYonedaGroupoidPresheafValue p U} (τ : F ⟶ G) :
    Functor.Fiber.fiberInclusion.map ((twoYonedaSplit_rawEvaluationFunctor p U).map τ) =
      τ.toNatTrans.app (Over.mk (𝟙 U)) :=
  rfl

/-- Helper for Remark 4.41.3: every raw based functor into the fibred-in-groupoids target is
admissible as a morphism of fibred categories. -/
private theorem twoYonedaSplit_target_owner_rawDomain_objectProperty_mem
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    FibredCategoryMor.objectProperty
        (twoYonedaSplit_source_owner U)
        (twoYonedaSplit_target_owner p)
        (show (twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
            (twoYonedaSplit_target_owner p).toBasedCategory from F) := by
  simpa [FibredCategoryMor.objectProperty, twoYonedaSplit_source_owner,
    twoYonedaSplit_target_owner] using
      twoYonedaSplit_preserves_strongly_cartesian (p := p) (U := U) F

/-- Helper for Remark 4.41.3: lift the raw based-functor category into the owner admissible
full subcategory by remembering the preservation proof. -/
private noncomputable abbrev twoYonedaSplit_target_owner_rawDomain_objectProperty
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
        BasedCategory.ofFunctor p) ⥤
      (FibredCategoryMor.objectProperty
          (twoYonedaSplit_source_owner U)
          (twoYonedaSplit_target_owner p)).FullSubcategory :=
  let P :
      ObjectProperty
        ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_owner p).toBasedCategory) :=
    FibredCategoryMor.objectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_owner p)
  P.lift (𝟭 _) (twoYonedaSplit_target_owner_rawDomain_objectProperty_mem p U)

/-- Helper for Remark 4.41.3: the raw-domain lift into the admissible full subcategory is only
bookkeeping, hence an equivalence. -/
private theorem twoYonedaSplit_target_owner_rawDomain_objectProperty_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_target_owner_rawDomain_objectProperty p U).IsEquivalence := by
  let P :
      ObjectProperty
        ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_owner p).toBasedCategory) :=
    FibredCategoryMor.objectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_owner p)
  let F :
      ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
          (twoYonedaSplit_target_owner p).toBasedCategory) ⥤
        P.FullSubcategory :=
    twoYonedaSplit_target_owner_rawDomain_objectProperty p U
  let G : P.FullSubcategory ⥤
      ((twoYonedaSplit_source_owner U).toBasedCategory ⥤ᵇ
        (twoYonedaSplit_target_owner p).toBasedCategory) :=
    P.ι
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · simpa [F, G] using
      (P.liftCompιIso
        (F := 𝟭 _)
        (twoYonedaSplit_target_owner_rawDomain_objectProperty_mem p U)).symm
  · refine NatIso.ofComponents
      (fun A ↦
        ObjectProperty.isoMk
          (P := P)
          (X := (G ⋙ F).obj A)
          (Y := A)
          (Iso.refl A.obj)) ?_
    intro A B f
    ext x
    simpa [G]

/-- Helper for Remark 4.41.3: forgetting an owner morphism to its underlying based functor and
repackaging it with the same preservation proof leaves the owner morphism unchanged. -/
private theorem twoYonedaSplit_ofBasedFunctor_toBasedFunctor
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    FibredCategoryMor.ofBasedFunctor (FibredCategoryMor.toBasedFunctor F) F.obj.property = F := by
  rfl

/-- Helper for Remark 4.41.3: packaging an admissible based functor as an owner morphism is an
equivalence. -/
private theorem twoYonedaSplit_target_owner_ofObjectProperty_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (FibredCategoryMor.ofObjectProperty
      (twoYonedaSplit_source_owner U)
      (twoYonedaSplit_target_owner p)).IsEquivalence := by
  let X := twoYonedaSplit_source_owner U
  let Y := twoYonedaSplit_target_owner p
  let P : ObjectProperty (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :=
    FibredCategoryMor.objectProperty X Y
  let F : P.FullSubcategory ⥤ (X ⟶ Y) :=
    FibredCategoryMor.ofObjectProperty X Y
  let G : (X ⟶ Y) ⥤ P.FullSubcategory :=
    wideSubcategoryInclusion ((fibredCategoryOverSubTwoCategory C).hom₂ X Y)
  refine Functor.IsEquivalence.mk' G ?_ ?_
  · refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact ObjectProperty.isoMk (P := P) (X := A) (Y := (F ⋙ G).obj A) (Iso.refl A.obj)
    · intro A B η
      apply ObjectProperty.hom_ext
      apply BasedNatTrans.ext
      ext a
      change η.hom.app a ≫ 𝟙 _ = 𝟙 _ ≫ η.hom.app a
      rw [Category.comp_id, Category.id_comp]
  · refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact
        twoYonedaSplit_fibredCategoryMorIsoOfBasedFunctorIso
          (F := (G ⋙ F).obj A) (G := A)
          (Iso.refl (FibredCategoryMor.toBasedFunctor A))
    · intro A B η
      apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      apply BasedNatTrans.ext
      ext a
      change η.hom.hom.app a ≫ 𝟙 _ = 𝟙 _ ≫ η.hom.hom.app a
      rw [Category.comp_id, Category.id_comp]

/-- Helper for Remark 4.41.3: equality morphisms in a fiber forget to the corresponding equality
morphisms in the total category. -/
private theorem twoYonedaSplit_fiber_eqToHom_map
    {T : Type v₁} [Category.{v₁} T] {q : T ⥤ C} {U : C}
    {P Q : q.Fiber U} (h : P = Q) :
    Functor.Fiber.fiberInclusion.map (eqToHom h) = eqToHom (congrArg Subtype.val h) := by
  cases h
  rfl

/-- Helper for Remark 4.41.3: after packaging a raw based functor as an owner morphism, owner
evaluation at `id_U : U/U` gives the same fiber object as raw evaluation. -/
private theorem twoYonedaSplit_target_owner_rawEvaluation_ofObjectProperty_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor p) :
    ((twoYonedaSplit_target_owner_rawDomain_objectProperty p U ⋙
          FibredCategoryMor.ofObjectProperty
            (twoYonedaSplit_source_owner U)
            (twoYonedaSplit_target_owner p) ⋙
          (twoYonedaSplit_target_owner p).yonedaEvaluationFunctor U).obj F) =
      (twoYonedaSplit_rawEvaluationFunctor p U).obj F := by
  apply Subtype.ext
  rfl

/-- Helper for Remark 4.41.3: after the same owner-side packaging, the underlying map of owner
evaluation is the raw component at `id_U : U/U`. -/
private theorem twoYonedaSplit_target_owner_rawEvaluation_ofObjectProperty_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor p} (η : F ⟶ G) :
    Functor.Fiber.fiberInclusion.map
      ((twoYonedaSplit_target_owner_rawDomain_objectProperty p U ⋙
            FibredCategoryMor.ofObjectProperty
              (twoYonedaSplit_source_owner U)
              (twoYonedaSplit_target_owner p) ⋙
            (twoYonedaSplit_target_owner p).yonedaEvaluationFunctor U).map η) =
      η.toNatTrans.app (Over.mk (𝟙 U)) := by
  rfl



/-- Helper for Remark 4.41.3: the identity of `F(id_U)` is a lift of `𝟙 U`, after using the
based-functor compatibility of `F`. -/
private theorem twoYonedaSplit_rawEvaluation_id_isHomLift
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    p.IsHomLift (𝟙 U) (𝟙 (F.obj (Over.mk (𝟙 U)))) := by
  let x := F.obj (Over.mk (𝟙 U))
  have hx : p.obj x = U := by
    change p.obj (F.obj (Over.mk (𝟙 U))) = (Over.forget U).obj (Over.mk (𝟙 U))
    exact F.w_obj (Over.mk (𝟙 U))
  change p.IsHomLift (𝟙 U) (𝟙 x)
  refine IsHomLift.of_fac p (𝟙 U) (𝟙 x) hx hx ?_
  change 𝟙 U = eqToHom hx.symm ≫ p.map (𝟙 x) ≫ eqToHom hx
  calc
    𝟙 U = eqToHom hx.symm ≫ 𝟙 (p.obj x) ≫ eqToHom hx := by
      simpa only [Category.id_comp, Category.comp_id] using (eqToHom_trans hx.symm hx).symm
    _ = eqToHom hx.symm ≫ p.map (𝟙 x) ≫ eqToHom hx := by
      exact congrArg (fun f ↦ eqToHom hx.symm ≫ f ≫ eqToHom hx) (p.map_id x).symm

/-- Helper for Remark 4.41.3: the comparison component between owner evaluation and raw evaluation
is the identity morphism on the common underlying object, viewed in the fiber over `U`. -/
private noncomputable def twoYonedaSplit_target_owner_rawEvaluation_ofObjectProperty_iso
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor p) :
    ((twoYonedaSplit_target_owner_rawDomain_objectProperty p U ⋙
          FibredCategoryMor.ofObjectProperty
            (twoYonedaSplit_source_owner U)
            (twoYonedaSplit_target_owner p) ⋙
          (twoYonedaSplit_target_owner p).yonedaEvaluationFunctor U).obj F) ≅
      (twoYonedaSplit_rawEvaluationFunctor p U).obj F where
  hom := by
    letI : p.IsHomLift (𝟙 U) (𝟙 (F.obj (Over.mk (𝟙 U)))) :=
      twoYonedaSplit_rawEvaluation_id_isHomLift p U F
    exact Functor.Fiber.homMk p U (𝟙 (F.obj (Over.mk (𝟙 U))))
  inv := by
    letI : p.IsHomLift (𝟙 U) (𝟙 (F.obj (Over.mk (𝟙 U)))) :=
      twoYonedaSplit_rawEvaluation_id_isHomLift p U F
    exact Functor.Fiber.homMk p U (𝟙 (F.obj (Over.mk (𝟙 U))))
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    change (𝟙 (F.obj (Over.mk (𝟙 U)))) ≫ 𝟙 (F.obj (Over.mk (𝟙 U))) =
      𝟙 (F.obj (Over.mk (𝟙 U)))
    simp
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    change (𝟙 (F.obj (Over.mk (𝟙 U)))) ≫ 𝟙 (F.obj (Over.mk (𝟙 U))) =
      𝟙 (F.obj (Over.mk (𝟙 U)))
    simp

/-- Helper for Remark 4.41.3: owner evaluation, after the raw-domain bookkeeping and owner
packaging layers, is naturally isomorphic to explicit raw evaluation. -/
private noncomputable def
    twoYonedaSplit_target_owner_rawEvaluation_ofObjectProperty_comparison
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    twoYonedaSplit_target_owner_rawDomain_objectProperty p U ⋙
        FibredCategoryMor.ofObjectProperty
          (twoYonedaSplit_source_owner U)
          (twoYonedaSplit_target_owner p) ⋙
        (twoYonedaSplit_target_owner p).yonedaEvaluationFunctor U ≅
      twoYonedaSplit_rawEvaluationFunctor p U :=
  NatIso.ofComponents
    (fun F ↦ twoYonedaSplit_target_owner_rawEvaluation_ofObjectProperty_iso p U F)
    (by
      intro F G η
      apply Functor.Fiber.hom_ext
      change η.toNatTrans.app (Over.mk (𝟙 U)) ≫ 𝟙 (G.obj (Over.mk (𝟙 U))) =
        𝟙 (F.obj (Over.mk (𝟙 U))) ≫ η.toNatTrans.app (Over.mk (𝟙 U))
      simp)

private theorem twoYonedaSplit_rawEvaluation_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (twoYonedaSplit_rawEvaluationFunctor p U).IsEquivalence := by
  let X := twoYonedaSplit_source_owner U
  let Y := twoYonedaSplit_target_owner p
  have hrawDomain :
      (twoYonedaSplit_target_owner_rawDomain_objectProperty p U).IsEquivalence :=
    twoYonedaSplit_target_owner_rawDomain_objectProperty_isEquivalence p U
  have hofObjectProperty :
      (FibredCategoryMor.ofObjectProperty X Y).IsEquivalence :=
    twoYonedaSplit_target_owner_ofObjectProperty_isEquivalence p U
  have hyoneda :
      (Y.yonedaEvaluationFunctor U).IsEquivalence := by
    exact FibredCategoryOver.yonedaEvaluationFunctor_isEquivalence (X := Y) U
  have hownerComposite :
      (twoYonedaSplit_target_owner_rawDomain_objectProperty p U ⋙
          FibredCategoryMor.ofObjectProperty X Y ⋙
          Y.yonedaEvaluationFunctor U).IsEquivalence := by
    letI :
        (twoYonedaSplit_target_owner_rawDomain_objectProperty p U).IsEquivalence :=
      hrawDomain
    letI : (FibredCategoryMor.ofObjectProperty X Y).IsEquivalence := hofObjectProperty
    letI : (Y.yonedaEvaluationFunctor U).IsEquivalence := hyoneda
    let Eraw := (twoYonedaSplit_target_owner_rawDomain_objectProperty p U).asEquivalence
    let Eowner := (FibredCategoryMor.ofObjectProperty X Y).asEquivalence
    let Eyoneda := (Y.yonedaEvaluationFunctor U).asEquivalence
    exact ((Eraw.trans Eowner).trans Eyoneda).isEquivalence_functor
  exact
    (Functor.isEquivalence_iff_of_iso
      (twoYonedaSplit_target_owner_rawEvaluation_ofObjectProperty_comparison p U)).1
      hownerComposite

/-- Helper for Remark 4.41.3: the chosen inclusion of the raw presheaf value into the split model
over `U` is the explicit split-model object with base `U` and fiber `G`. -/
private theorem twoYonedaSplit_owner_inclusion_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (G : HasFibers.Fib (twoYonedaSplitProjection p) U) :
    (HasFibers.ι (p := twoYonedaSplitProjection p) U).obj G = { base := U, fiber := G } := by
  rfl

/-- Helper for Remark 4.41.3: the chosen inclusion map on a morphism in the raw presheaf fiber is
the same morphism followed by the `mapId.inv` tail from the co-Grothendieck construction. -/
private theorem twoYonedaSplit_owner_inclusion_map_fiber
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : HasFibers.Fib (twoYonedaSplitProjection p) U} (τ : F ⟶ G) :
    ((HasFibers.ι (p := twoYonedaSplitProjection p) U).map τ).fiber =
      τ ≫ (((twoYonedaCatPresheaf p).toPseudofunctor'.mapId { as := op U }).inv.toNatTrans.app G) := by
  rfl

/-- Helper for Remark 4.41.3: on the included split-model object `{ base := U, fiber := G }`,
the identity map of the comparison functor is already the identity morphism in the fiber over
`U`. -/
private theorem twoYonedaSplit_owner_inclusion_identity_map
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (G : HasFibers.Fib (twoYonedaSplitProjection p) U) :
    twoYonedaSplitToOriginalMap p
        (𝟙 ({ base := U, fiber := G } : twoYonedaSplitCategory p)) =
      𝟙 (twoYonedaSplitToOriginalObj p { base := U, fiber := G }) := by
  -- This is the identity case of `twoYonedaSplitToOriginalMap`, specialized to the included raw
  -- split-fiber object.
  simpa using
    twoYonedaSplitToOriginalUnderlying_map_id (p := p) { base := U, fiber := G }

/-- Helper for Remark 4.41.3: the `mapId.inv` tail on an included split-model object cancels with
the tautological slice map after evaluation at `id_U : U/U`. -/
private theorem twoYonedaSplit_owner_inclusion_identity_tail
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (G : HasFibers.Fib (twoYonedaSplitProjection p) U) :
      ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId { as := op U }).inv.toNatTrans.app G).app
        (Over.mk (𝟙 U))) ≫
      G.map (twoYonedaTautologicalSliceHom (𝟙 U)) =
    𝟙 (twoYonedaSplitToOriginalObj p { base := U, fiber := G }) := by
  -- This is exactly the identity comparison formula specialized to the included object
  -- `{ base := U, fiber := G }`.
  simpa [twoYonedaSplitToOriginalMap] using
    twoYonedaSplit_owner_inclusion_identity_map p U G

/-- Helper for Remark 4.41.3: evaluating the composite of the raw fiber morphism with the
`mapId.inv` tail at `id_U : U/U` splits as the component of `τ` followed by the evaluated tail. -/
private theorem twoYonedaSplit_inclusion_component_app
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : HasFibers.Fib (twoYonedaSplitProjection p) U} (τ : F ⟶ G) :
    (τ ≫ (((twoYonedaCatPresheaf p).toPseudofunctor'.mapId { as := op U }).inv.toNatTrans.app
        G)).app (Over.mk (𝟙 U)) =
      τ.app (Over.mk (𝟙 U)) ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId { as := op U }).inv.toNatTrans.app G).app
          (Over.mk (𝟙 U))) := by
  -- This is the objectwise formula for composition of natural transformations.
  rfl

/-- Helper for Remark 4.41.3: applying the comparison functor to an included fiber morphism
simply evaluates that morphism at the tautological slice object `id_U : U/U`. -/
private theorem twoYonedaSplit_inclusion_map_evaluates_to_raw_component
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : HasFibers.Fib (twoYonedaSplitProjection p) U} (τ : F ⟶ G) :
    twoYonedaSplitToOriginalMap p
        ((HasFibers.ι (p := twoYonedaSplitProjection p) U).map τ) =
      τ.app (Over.mk (𝟙 U)) := by
  -- Expand the included map at `id_U`, then use the identity comparison on the included codomain
  -- object to cancel the residual `mapId.inv` tail.
  rw [twoYonedaSplitToOriginalMap, twoYonedaSplit_owner_inclusion_map_fiber]
  change
    (τ ≫ (((twoYonedaCatPresheaf p).toPseudofunctor'.mapId { as := op U }).inv.toNatTrans.app
        G)).app (Over.mk (𝟙 U)) ≫
      G.map (twoYonedaTautologicalSliceHom (𝟙 U)) =
        τ.app (Over.mk (𝟙 U))
  rw [twoYonedaSplit_inclusion_component_app]
  calc
    (τ.app (Over.mk (𝟙 U)) ≫
        ((((twoYonedaCatPresheaf p).toPseudofunctor'.mapId { as := op U }).inv.toNatTrans.app G).app
          (Over.mk (𝟙 U)))) ≫
        G.map (twoYonedaTautologicalSliceHom (𝟙 U)) =
      τ.app (Over.mk (𝟙 U)) ≫ 𝟙 (twoYonedaSplitToOriginalObj p { base := U, fiber := G }) := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ τ.app (Over.mk (𝟙 U)) ≫ k)
            (twoYonedaSplit_owner_inclusion_identity_tail p U G)
    _ = τ.app (Over.mk (𝟙 U)) := by
          exact Category.comp_id (τ.app (Over.mk (𝟙 U)))

/-- Helper for Remark 4.41.3: after forgetting from the fiber over `U`, the map of
`HasFibers.inducedFunctor ⋙ FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U`
is exactly the raw evaluation component at `id_U : U/U`. -/
private theorem twoYonedaSplit_induced_comp_obj_eq_rawEvaluation_obj
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    (F : HasFibers.Fib (twoYonedaSplitProjection p) U) :
    (HasFibers.inducedFunctor (twoYonedaSplitProjection p) U ⋙
        FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U).obj F =
      (twoYonedaSplit_rawEvaluationFunctor p U).obj F := by
  -- On objects, both functors evaluate the same split-model fiber object at `id_U : U/U`.
  rfl

/-- Helper for Remark 4.41.3: after forgetting from the fiber over `U`, the map of
`HasFibers.inducedFunctor ⋙ FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U`
is the comparison morphism `twoYonedaSplitToOriginalMap` applied to the included split-model
morphism. -/
@[simp] private theorem twoYonedaSplit_induced_comp_map_hom
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C)
    {F G : HasFibers.Fib (twoYonedaSplitProjection p) U} (τ : F ⟶ G) :
    Functor.Fiber.fiberInclusion.map
      ((HasFibers.inducedFunctor (twoYonedaSplitProjection p) U ⋙
          FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U).map τ) =
        twoYonedaSplitToOriginalMap p
          ((HasFibers.ι (p := twoYonedaSplitProjection p) U).map τ) := by
  -- Both sides are definitionally the underlying total-space map obtained by applying
  -- `twoYonedaSplitToOriginal` to the included morphism in the split model.
  rfl

private noncomputable def twoYonedaSplit_induced_comp_fiberFunctor_eq_rawEvaluation
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    HasFibers.inducedFunctor (twoYonedaSplitProjection p) U ⋙
        FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U ≅
      twoYonedaSplit_rawEvaluationFunctor p U := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · -- On objects, both functors are literally evaluation at `id_U : U/U`.
    exact eqToIso (twoYonedaSplit_induced_comp_obj_eq_rawEvaluation_obj p U F)
  · intro F G τ
    -- After forgetting from the fiber, both morphisms are the same component `τ.app (id_U)`.
    apply Functor.Fiber.hom_ext
    change
      twoYonedaSplitToOriginalMap p ((HasFibers.ι (p := twoYonedaSplitProjection p) U).map τ) ≫
        eqToHom rfl =
      eqToHom rfl ≫ τ.toNatTrans.app (Over.mk (𝟙 U))
    simp [twoYonedaSplit_inclusion_map_evaluates_to_raw_component]

/-- Helper for Remark 4.41.3: the owner Yoneda evaluation theorem transported along the canonical
split-fiber identifications proves that the fiber functor of `twoYonedaSplitToOriginal` is an
equivalence on every fiber. -/
private theorem twoYonedaFiberEvaluation_isEquivalence
    (p : S ⥤ C) [IsFibredInGroupoids p] (U : C) :
    (FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U).IsEquivalence := by
  -- Route correction: cancel the already-known equivalence
  -- `HasFibers.inducedFunctor (twoYonedaSplitProjection p) U`, transport the remaining composite
  -- to raw evaluation, and then apply the ordinary-slice `2`-Yoneda equivalence.
  let F := HasFibers.inducedFunctor (twoYonedaSplitProjection p) U
  let G := FibredInGroupoidsMor.fiberFunctor (twoYonedaSplitToOriginal p) U
  have hComp : (F ⋙ G).IsEquivalence := by
    exact
      (Functor.isEquivalence_iff_of_iso
        (twoYonedaSplit_induced_comp_fiberFunctor_eq_rawEvaluation p U)).2
        (twoYonedaSplit_rawEvaluation_isEquivalence p U)
  letI : F.IsEquivalence := twoYonedaSplit_inducedFunctor_isEquivalence p U
  letI : (F ⋙ G).IsEquivalence := hComp
  simpa [F, G] using Functor.isEquivalence_of_comp_left F G

-- Proof sketch: apply Example 4.37.1 to `twoYonedaGroupoidPresheaf p` to obtain a split fibred
-- category over `C`. For each `U`, Lemma 4.41.2 identifies the fiber of this split model with
-- `p.Fiber U`, and Lemma 4.35.9 upgrades these fiberwise equivalences to an equivalence over `C`.
/-- Remark 4.41.3: the `2`-Yoneda construction
`U ↦ Mor_{Cat/C}(C/U, S)`, formalized as `twoYonedaGroupoidPresheaf p`, gives an alternative
split model for a category fibred in groupoids `p : S ⥤ C`. The canonical comparison functor
`twoYonedaSplitToOriginal p : twoYonedaSplitModel p ⟶ FibredInGroupoidsOver.ofFunctor p`,
sending `(U, x)` to `x(𝟙 U)`, is an equivalence over `C`. -/
theorem twoYoneda_groupoidPresheaf_split_model_over_base
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    (twoYonedaSplitToOriginal p).IsEquivalenceOverBase := by
  -- The imported owner criterion upgrades the fiberwise equivalences to an equivalence over the
  -- base.
  exact
    FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence (F := twoYonedaSplitToOriginal p)
      ((FibredInGroupoidsMor.isEquivalence_iff_fiberwise (F := twoYonedaSplitToOriginal p)).2
        (fun U ↦ twoYonedaFiberEvaluation_isEquivalence p U))

end CategoryTheory
