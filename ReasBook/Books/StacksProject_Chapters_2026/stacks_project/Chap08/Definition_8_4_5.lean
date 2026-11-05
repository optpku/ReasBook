module

public import Mathlib
public import stacks_project.Chap04.Definition_4_33_9
public import stacks_project.Chap08.Definition_8_4_1


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v vDesc

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 8.4.5:
- primary domain: stacks over a site, viewed as fibred categories over a fixed base together with
  the stack condition.
- inspected owner-level declarations:
  `IsStackOnSite`,
  `FibredCategoryOver`,
  `FibredCategoryMor`,
  `SubTwoCategory`.
- best owner abstraction: the full sub-`2`-category of `FibredCategoryOver C` cut out by the
  source-facing predicate `IsStackOnSite J X.p`; morphisms and `2`-morphisms should reuse the
  ambient `FibredCategoryMor` and bicategory structure rather than duplicate their API.
- primitive data: a fibred category over `C` and a proof of `IsStackOnSite` for its projection.
- derived API: coercions to `FibredCategoryOver C`, inherited instances, and the inherited
  bicategory of stacks together with the bridge from ambient homs `X ⟶ Y` to
  `FibredCategoryMor X.toFibredCategoryOver Y.toFibredCategoryOver`.

Source/core/bridge triage:
- `source-facing`: `StackOver J`.
- `core/canonical`: `IsStackOnSite`, `FibredCategoryOver`, `FibredCategoryMor`, and
  `SubTwoCategory`.
- `bridge/view`: the coercion to `FibredCategoryOver C` and the ambient hom `X ⟶ Y`. -/

/-- Definition 8.4.5 at the owner level: stacks over `(C, J)` form the full sub-`2`-category of
`FibredCategoryOver C` cut out by the stack-on-site predicate on the projection functor. -/
abbrev stackOverSubTwoCategory (J : GrothendieckTopology C) :
    SubTwoCategory (FibredCategoryOver C) where
  obj := fun X ↦ IsStackOnSite J X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

/-- Definition 8.4.5: a stack over the site `(C, J)` is an object of the owner sub-`2`-category
`stackOverSubTwoCategory J`, equivalently a fibred category over `C` together with a proof that
its projection functor is a stack over `(C, J)` in the canonical sense of Definition `8.4.1`. -/
abbrev StackOver (J : GrothendieckTopology C) :=
  (stackOverSubTwoCategory J).Obj

namespace StackOver

variable {J : GrothendieckTopology C}
variable {D : Type vDesc} [Category.{vDesc} D]

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : StackOver J) : FibredCategoryOver C :=
  X.obj

/-- The projection functor of a stack over `(C, J)`. -/
abbrev p (X : StackOver J) :=
  X.toFibredCategoryOver.p

/-- The underlying based category over `C` of a stack over `(C, J)`. -/
abbrev toBasedCategory (X : StackOver J) : BasedCategory C :=
  X.toFibredCategoryOver.toBasedCategory

/-- Bundle a projection `p : D ⥤ C` that is already known to be a stack over `(C, J)`. -/
abbrev ofProjection (J : GrothendieckTopology C) (p : D ⥤ C) [IsStackOnSite J p] :
    StackOver J :=
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [FibredCategoryOver.p, FibredCategoryOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

/-- A stack over `(C, J)` is canonically viewed as its underlying fibred category over `C`. -/
instance : CoeOut (StackOver J) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- The projection functor of a stack over `(C, J)` is fibred. -/
instance (X : StackOver J) : X.p.IsFibered :=
  X.property.toIsFibered

/-- The projection functor of a stack over `(C, J)` is a stack over the site in the canonical
sense of Definition `8.4.1`. -/
instance (X : StackOver J) : IsStackOnSite J X.p :=
  X.property

/-- A stack over `(C, J)` satisfies the stack condition for its projection functor. -/
-- Proof sketch: this is exactly the defining property carried by an object of the full
-- sub-`2`-category `stackOverSubTwoCategory J`.
theorem isStackOnSite_p (X : StackOver J) : IsStackOnSite J X.p := by
  -- Expose the stack condition stored in the bundled object `X`.
  exact X.property

/-- The projection functor of a stack over `(C, J)` carries the canonical choice of fiber
categories. -/
instance (X : StackOver J) : HasFibers X.p :=
  HasFibers.canonical X.p

end StackOver

namespace ObjectProperty.FullSubcategory

/-- The total category of an object in a full subcategory of `FibredCategoryOver C`. This gives
the canonical `X.S` field-notation surface for bundled stacks and related chapter owners. -/
abbrev S {P : ObjectProperty (FibredCategoryOver C)} (X : P.FullSubcategory) :=
  X.obj.S

end ObjectProperty.FullSubcategory

/-- Stacks over `(C, J)` form a strict `2`-category via the induced bicategory structure on their
underlying fibred categories over `C`. -/
instance (J : GrothendieckTopology C) : Bicategory (StackOver J) :=
  SubTwoCategory.bicategoryObj (stackOverSubTwoCategory J)

/-- The induced `2`-category of stacks over `(C, J)` is strict. -/
instance (J : GrothendieckTopology C) : Bicategory.Strict (StackOver J) :=
  SubTwoCategory.strictObj (stackOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Category (StackOver J) :=
  StrictBicategory.category (StackOver J)

variable {J : GrothendieckTopology C}
variable {X Y : StackOver J}

abbrev ambientMor (F : X ⟶ Y) :
    X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver :=
  (SubTwoCategory.inclusion (stackOverSubTwoCategory J)).map F

/-- A morphism of stacks over `(C, J)` is canonically viewed as the corresponding ambient
`1`-morphism of fibred categories over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) where
  coe F := ambientMor F

namespace InducedCategory.Hom

/-- The ambient `1`-morphism of fibred categories over `C` underlying a morphism of stacks over
`(C, J)`. -/
abbrev toFibredCategoryMor (F : X ⟶ Y) :
    X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver :=
  ambientMor F

/-- Build a morphism of stacks over `(C, J)` from the corresponding ambient morphism of fibred
categories over `C`. Since `StackOver J` is a full sub-`2`-category on objects, no extra
structure is needed on the hom. -/
abbrev ofFibredCategoryMor
    (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) :
    X ⟶ Y :=
  ⟨⟨F, trivial⟩⟩

/-- Build a `2`-morphism of stack morphisms from the corresponding ambient `2`-morphism of
fibred-category morphisms. -/
abbrev homMk {F G : X ⟶ Y}
    (η : toFibredCategoryMor F ⟶ toFibredCategoryMor G) :
    F ⟶ G :=
  ⟨ObjectProperty.homMk η, trivial⟩

abbrev ambientInverse :
    (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) ⥤ (X ⟶ Y) :=
  { obj := ofFibredCategoryMor
    map := fun η ↦ homMk η }

noncomputable def ambientUnitIso :
    𝟭 (X ⟶ Y) ≅ ((stackOverSubTwoCategory J).hom X Y).inclusion ⋙ ambientInverse := by
  refine NatIso.ofComponents (fun F ↦ Iso.refl F) ?_
  intro F G η
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  rw [WideSubcategory.comp_def, ObjectProperty.FullSubcategory.comp_hom]
  simp only [Functor.comp_map, Iso.refl_hom, ObjectProperty.ι_map]
  change η.hom.hom ≫ 𝟙 G.obj.obj = 𝟙 F.obj.obj ≫ η.hom.hom
  rw [Category.comp_id, Category.id_comp]

noncomputable def ambientCounitIso :
    ambientInverse ⋙ ((stackOverSubTwoCategory J).hom X Y).inclusion ≅
      𝟭 (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) := by
  refine NatIso.ofComponents (fun F ↦ Iso.refl F) ?_
  intro F G η
  change (ambientInverse ⋙ ((stackOverSubTwoCategory J).hom X Y).inclusion).map η ≫ 𝟙 G =
      𝟙 F ≫ η
  simp [ambientInverse, homMk]

/-- The owner hom-category of stacks over `(C, J)` is canonically equivalent to the ambient
hom-category of fibred-category morphisms between the underlying fibred categories. -/
noncomputable def ambientEquivalence :
    CategoryTheory.Equivalence
      (X ⟶ Y)
      (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) :=
  Equivalence.mk
    (((stackOverSubTwoCategory J).hom X Y).inclusion)
    ambientInverse
    ambientUnitIso
    ambientCounitIso

/-- The underlying based functor of a morphism of stacks over `(C, J)`. -/
abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toFibredCategoryOver.toBasedCategory ⥤ᵇ Y.toFibredCategoryOver.toBasedCategory :=
  (toFibredCategoryMor F).toHom

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

/-- The underlying functor between the total categories. -/
abbrev G (F : X ⟶ Y) :
    X.toFibredCategoryOver.S ⥤ Y.toFibredCategoryOver.S :=
  (toBasedFunctor F).toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : G F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

instance : CoeOut (X ⟶ Y)
    (X.toFibredCategoryOver.toBasedCategory ⥤ᵇ Y.toFibredCategoryOver.toBasedCategory) where
  coe F := toBasedFunctor F

/-- A morphism of stacks over `(C, J)` is an equivalence over the base if its underlying based
functor is. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  (toBasedFunctor F).IsEquivalenceOverBase

/-- Every object of every target fiber is locally in the essential image of a morphism of stacks
over `(C, J)`. This is the stack-morphism owner surface for the corresponding ambient
fibred-category predicate. -/
abbrev LocallyEssentiallySurjectiveOnObjects
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J (toFibredCategoryMor F)

end InducedCategory.Hom

end CategoryTheory
