module

public import stacks_project.Chap04.Definition_4_33_9
public import stacks_project.Chap04.Definition_4_35_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v vS u w

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open BasedCategory
open scoped Bicategory

/-
Domain-style sampling for Definition 4.35.6:
- primary domain: categories fibred in groupoids over a fixed base and their morphisms over that
  base.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `FibredCategoryOver`,
  `FibredCategoryMor`,
  `SubTwoCategory`.
- best owner abstraction: the object owner is the full sub-`2`-category of
  `FibredCategoryOver C` cut out by `IsFibredInGroupoids X.p`.
- primitive data: a fibred category over `C` together with the proof that its projection is
  fibred in groupoids.
- derived API: the forgetful views to `FibredCategoryOver C`, `CategoryOver C`, and
  `BasedCategory C`, together with the source-facing morphism type of based functors over `C`;
  the ambient `FibredCategoryMor` is recovered canonically because strong-cartesian preservation
  is automatic in the fibred-in-groupoids case.

Source/core/bridge triage:
- `source-facing`: `FibredInGroupoidsOver C` and its owner homs `X ⟶ Y`;
- `core/canonical`: `fibredInGroupoidsOverSubTwoCategory C`, `FibredCategoryOver`,
  the ambient owner homs in `FibredCategoryOver C`, and `IsFibredInGroupoids`;
- `bridge/view`: the forgetful coercions to `FibredCategoryOver C`, `CategoryOver C`,
  `BasedCategory C`, the stable chapter alias `FibredInGroupoidsMor X Y`, and the coercion to
  the ambient `FibredCategoryMor`.

Primitive-vs-derived split:
- primitive data: the ambient fibred-category object together with the groupoid condition on its
  projection;
- derived API: the short object projections, the source-facing morphism view by based functors,
  and the ambient fibred-category-morphism coercion. -/

/-- Definition 4.35.6 (1): at the owner level, categories fibred in groupoids over `C` form the full
sub-`2`-category of `FibredCategoryOver C` cut out by the fibred-in-groupoids condition. -/
abbrev fibredInGroupoidsOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (FibredCategoryOver C) where
  obj := fun X ↦ IsFibredInGroupoids X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

variable {C : Type u} [Category.{v} C]

/-- The identity functor of `C` is strongly cartesian over `C`. -/
private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    subst_hom_lift (𝟭 C) (g ≫ f) φ
    refine ⟨g, ?_, ?_⟩
    · constructor
      · simpa using
          (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map g) g from inferInstance)
      · rfl
    · intro π hπ
      let _ := hπ.1
      subst_hom_lift (𝟭 C) g π
      rfl

instance : IsFibredInGroupoids (𝟭 C) where
  toIsFibered := by
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro a R f
    exact ⟨R, f, idFunctor_isStronglyCartesian f⟩
  isStronglyCartesian_map φ := idFunctor_isStronglyCartesian φ

/-- Definition 4.35.6 (2): the objects of the `2`-category of categories fibred in groupoids over `C`
are the objects of the canonical owner sub-`2`-category
`fibredInGroupoidsOverSubTwoCategory C`. -/
abbrev FibredInGroupoidsOver (C : Type u) [Category.{v} C] :=
  (fibredInGroupoidsOverSubTwoCategory C).Obj

namespace FibredInGroupoidsOver

/-- Helper for Definition 4.35.6: a slice morphism built with `Over.homMk` is a hom-lift for the
projection `Over.forget X`. -/
private theorem over_homMk_isHomLift {X : C} {a c : Over X}
    (g : c.left ⟶ a.left) (w : g ≫ a.hom = c.hom) :
    (Over.forget X).IsHomLift g (Over.homMk g w) := by
  -- The forgetful functor remembers exactly the underlying arrow in `C`.
  refine IsHomLift.of_fac' (Over.forget X) g (Over.homMk g w) rfl rfl ?_
  simp

/-- Helper for Definition 4.35.6: every morphism in `Over X` is strongly cartesian for the slice
projection `Over.forget X`. -/
private theorem over_hom_isStronglyCartesian {X : C} {a b : Over X} (φ : a ⟶ b) :
    (Over.forget X).IsStronglyCartesian φ.left φ where
  toIsHomLift := by
    -- A slice morphism lies over its underlying arrow by definition.
    refine IsHomLift.of_fac' (Over.forget X) φ.left φ rfl rfl ?_
    simp
  universal_property' := by
    intro c g φ' hφ'
    -- The competing lift is determined by its underlying arrow in `C`.
    have hbase : g ≫ φ.left = φ'.left := by
      exact
        @IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget X) _ _ (g ≫ φ.left) φ' hφ'
    have hw : g ≫ a.hom = c.hom := by
      -- Route correction: reduce the slice commutativity constraint to underlying arrows.
      have hga : g ≫ a.hom = (g ≫ φ.left) ≫ b.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ g ≫ t) (Over.w φ).symm
      have hbase_comp : (g ≫ φ.left) ≫ b.hom = φ'.left ≫ b.hom := by
        simpa [Category.assoc] using congrArg (fun t ↦ t ≫ b.hom) hbase
      have hφ'comm : φ'.left ≫ b.hom = c.hom := by
        simpa using Over.w φ'
      exact hga.trans (hbase_comp.trans hφ'comm)
    let χ : c ⟶ a := Over.homMk g hw
    have hχfac : χ ≫ φ = φ' := by
      -- Equality of slice morphisms is equality of their underlying arrows.
      apply Over.OverMorphism.ext
      simpa [χ] using hbase
    refine ⟨χ, ⟨over_homMk_isHomLift g hw, hχfac⟩, ?_⟩
    intro π hπ
    -- Any other candidate must have the same underlying arrow, hence is the same slice morphism.
    apply Over.OverMorphism.ext
    have hπleft : π.left = g := by
      simpa using
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget X) _ _ g π hπ.1).symm
    simpa [χ] using hπleft

/-- Helper for Definition 4.35.6: the slice projection `Over.forget X` is fibered. -/
private theorem over_forget_isFibered (X : C) : (Over.forget X).IsFibered := by
  -- Choose the textbook pullback object `f ≫ a.hom : R ⟶ X` and its tautological map to `a`.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro a R f
  let c : Over X := Over.mk (f ≫ a.hom)
  let φ : c ⟶ a := Over.homMk f (show f ≫ a.hom = c.hom by rfl)
  refine ⟨c, φ, ?_⟩
  simpa [c, φ] using over_hom_isStronglyCartesian (X := X) φ

/-- The slice projection `Over.forget X : Over X ⥤ C` is fibred in groupoids. -/
instance (X : C) : IsFibredInGroupoids (Over.forget X) := by
  -- The slice projection is fibered by explicit pullbacks, and every slice arrow is strongly
  -- cartesian because its universal property is controlled by the underlying arrow in `C`.
  refine
    { toIsFibered := over_forget_isFibered X
      isStronglyCartesian_map := fun φ ↦ ?_ }
  simpa using over_hom_isStronglyCartesian (X := X) φ

/-- Build a bundled category fibred in groupoids over `C` from a functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsFibredInGroupoids p] :
    FibredInGroupoidsOver C :=
  ⟨FibredCategoryOver.ofFunctor p, by
    simpa [fibredInGroupoidsOverSubTwoCategory, FibredCategoryOver.p, FibredCategoryOver.ofFunctor]
      using (inferInstance : IsFibredInGroupoids p)⟩

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : FibredInGroupoidsOver C) : FibredCategoryOver C :=
  X.obj

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredInGroupoidsOver C) : CategoryOver C :=
  X.toFibredCategoryOver.toCategoryOver

/-- The total category of a bundled category fibred in groupoids over `C`. -/
abbrev S (X : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver.S

/-- The projection functor of a bundled category fibred in groupoids over `C`. -/
abbrev p (X : FibredInGroupoidsOver C) :=
  X.toFibredCategoryOver.p

/-- The projection of a bundled category fibred in groupoids is fibred in groupoids. -/
-- Proof sketch: this is exactly the property field of an object of the owner full
-- sub-`2`-category after unfolding the projection abbreviation.
theorem p_isFibredInGroupoids (X : FibredInGroupoidsOver C) :
    IsFibredInGroupoids X.p :=
  X.property

/-- Forget a bundled category fibred in groupoids over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredInGroupoidsOver C) : BasedCategory C :=
  X.toFibredCategoryOver.toBasedCategory

/-- Compatibility coercion to fibred categories over `C`. -/
instance : CoeOut (FibredInGroupoidsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Compatibility coercion to the ambient category `Cat/C`. -/
instance : CoeOut (FibredInGroupoidsOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

/-- Compatibility coercion to the ambient based-category API. -/
instance : CoeOut (FibredInGroupoidsOver C) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in groupoids over `C` is fibred in
groupoids. -/
instance (X : FibredInGroupoidsOver C) : IsFibredInGroupoids X.p :=
  p_isFibredInGroupoids X

/-- The projection functor of a bundled category fibred in groupoids over `C` is fibred. -/
instance (X : FibredInGroupoidsOver C) : X.p.IsFibered :=
  X.property.toIsFibered

end FibredInGroupoidsOver

instance : Bicategory (FibredInGroupoidsOver C) :=
  SubTwoCategory.bicategoryObj (fibredInGroupoidsOverSubTwoCategory C)

instance : Bicategory.Strict (FibredInGroupoidsOver C) :=
  SubTwoCategory.strictObj (fibredInGroupoidsOverSubTwoCategory C)

instance fibredInGroupoidsOverCategory : Category (FibredInGroupoidsOver C) :=
  StrictBicategory.category (FibredInGroupoidsOver C)

instance fibredInGroupoidsOverHom₂IsMultiplicative
    (X Y : FibredInGroupoidsOver C) :
    ((fibredInGroupoidsOverSubTwoCategory C).hom₂ X Y).IsMultiplicative :=
  ((fibredInGroupoidsOverSubTwoCategory C).hom X Y).hom_isMultiplicative

instance fibredInGroupoidsOverHomInclusionFull
    (X Y : FibredInGroupoidsOver C) :
    (((fibredInGroupoidsOverSubTwoCategory C).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

instance fibredInGroupoidsOverHomWideInclusionFull
    (X Y : FibredInGroupoidsOver C) :
    (wideSubcategoryInclusion ((fibredInGroupoidsOverSubTwoCategory C).hom₂ X Y)).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨η, trivial⟩, rfl⟩

/-- Definition 4.35.6 (3): `FibredInGroupoidsMor X Y` is the stable chapter vocabulary for the owner
hom `X ⟶ Y` in the full sub-`2`-category of fibred categories over `C` cut out by the
fibred-in-groupoids condition. Since this sub-`2`-category is full on `1`-morphisms, the ambient
canonical `FibredCategoryMor` API is recovered by thin coercion and bridge declarations; the
public theorem surface below uses the owner notation `X ⟶ Y` directly. -/
abbrev FibredInGroupoidsMor (X Y : FibredInGroupoidsOver C) :=
  X ⟶ Y

namespace FibredInGroupoidsMor

variable {X Y : FibredInGroupoidsOver C}

/-- Regard an ambient morphism of the underlying fibred categories over `C` as the corresponding
owner hom in `FibredInGroupoidsOver C`. -/
abbrev ofAmbientHom
    (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) :
    X ⟶ Y :=
  { obj := { obj := F, property := trivial } }

/-- In a category fibred in groupoids every based functor over `C` preserves strongly cartesian
morphisms, so it canonically defines an ambient morphism of fibred categories. -/
theorem preservesStronglyCartesian
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    G.PreservesStronglyCartesian := by
  intro a b φ _
  exact (inferInstance : IsFibredInGroupoids Y.p).isStronglyCartesian_map (G.map φ)

/-- The ambient fibred-category morphism underlying an owner hom in
`FibredInGroupoidsOver C`. -/
abbrev toFibredCategoryMor (F : X ⟶ Y) :
    X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver :=
  F.toHom

/-- A morphism of categories fibred in groupoids over `C` is canonically viewed as the
corresponding ambient `1`-morphism of fibred categories over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) where
  coe F := FibredInGroupoidsMor.toFibredCategoryMor F

/-- The underlying based functor of a morphism of categories fibred in groupoids over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredCategoryMor.toBasedFunctor (FibredInGroupoidsMor.toFibredCategoryMor F)

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  FibredInGroupoidsMor.toBasedFunctor F |>.fiberFunctor U

/-- The underlying functor between the total categories. -/
abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  FibredInGroupoidsMor.toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : FibredInGroupoidsMor.G F ⋙ Y.p = X.p :=
  FibredInGroupoidsMor.toBasedFunctor F |>.w

/-- Compatibility coercion from owner homs to based functors over `C`. -/
instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := FibredInGroupoidsMor.toBasedFunctor F

/-- Build a morphism of categories fibred in groupoids over `C` from a based functor over `C`.
This is the thin bridge from the owner-selected homs to the ambient `BasedFunctor` API. -/
abbrev ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  ⟨FibredCategoryMor.ofBasedFunctor G (preservesStronglyCartesian G), trivial⟩

/-- A morphism of categories fibred in groupoids over `C` is an equivalence over the base if its
underlying based functor is. -/
abbrev IsEquivalenceOverBase (F : FibredInGroupoidsMor X Y) : Prop :=
  FibredCategoryMor.IsEquivalenceOverBase (FibredInGroupoidsMor.toFibredCategoryMor F)

noncomputable def fibredCategoryMorIsoOfBasedFunctorIso
    {F G : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver}
    (e : FibredCategoryMor.toBasedFunctor F ≅ FibredCategoryMor.toBasedFunctor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Convert an isomorphism between the ambient fibred-category morphisms underlying `F` and `G`
into an isomorphism of morphisms of categories fibred in groupoids. -/
noncomputable def ofFibredCategoryMorIso
    {F G : X ⟶ Y}
    (e : FibredInGroupoidsMor.toFibredCategoryMor F ≅
      FibredInGroupoidsMor.toFibredCategoryMor G) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

noncomputable def ownerIsoOfBasedFunctorIso
    {F G : X ⟶ Y}
    (e : FibredInGroupoidsMor.toBasedFunctor F ≅ FibredInGroupoidsMor.toBasedFunctor G) :
    F ≅ G :=
  ofFibredCategoryMorIso (fibredCategoryMorIsoOfBasedFunctorIso e)

noncomputable def basedFunctorIsoOfOwnerIso
    {F G : X ⟶ Y} (e : F ≅ G) :
    FibredInGroupoidsMor.toBasedFunctor F ≅ FibredInGroupoidsMor.toBasedFunctor G :=
  Functor.mapIso
    (((fibredCategoryOverSubTwoCategory C).hom X.toFibredCategoryOver Y.toFibredCategoryOver).inclusion)
    (Functor.mapIso (((fibredInGroupoidsOverSubTwoCategory C).hom X Y).inclusion) e)

/-- Explicit equivalence-over-base data on the underlying based functor of `F` induce a
bicategorical equivalence with forward morphism `F`. -/
noncomputable def ofEquivalenceOverBase
    (F : X ⟶ Y)
    (e : BasedFunctor.EquivalenceOverBase (FibredInGroupoidsMor.toBasedFunctor F)) :
    Bicategory.Equivalence X Y :=
  let e : BasedFunctor.EquivalenceOverBase (FibredInGroupoidsMor.toBasedFunctor F) :=
    e
  let G : Y ⟶ X := ofBasedFunctor e.inverse
  let eta : (𝟙 X : X ⟶ X) ≅ F ≫ G :=
    by
      simpa [G] using ownerIsoOfBasedFunctorIso e.unitIso
  let eps : G ≫ F ≅ (𝟙 Y : Y ⟶ Y) :=
    by
      simpa [G] using ownerIsoOfBasedFunctorIso e.counitIso
  Bicategory.Equivalence.mkOfAdjointifyCounit eta eps

/-- A morphism of categories fibred in groupoids over `C` that is an equivalence over the base
admits a bicategorical equivalence with forward morphism `F`. -/
theorem exists_equivalence
    (F : X ⟶ Y) (hF : FibredInGroupoidsMor.IsEquivalenceOverBase F) :
    ∃ e : Bicategory.Equivalence X Y, e.hom = F := by
  rcases hF.nonempty with ⟨e⟩
  exact ⟨ofEquivalenceOverBase F e, rfl⟩

/-- A morphism of categories fibred in groupoids over `C` that is an equivalence over the base
admits an explicit inverse morphism together with unit and counit isomorphisms. -/
theorem exists_inverse
    (F : X ⟶ Y) (hF : FibredInGroupoidsMor.IsEquivalenceOverBase F) :
    ∃ G : Y ⟶ X,
      Nonempty ((𝟙 X : X ⟶ X) ≅ F ≫ G) ∧
        Nonempty (G ≫ F ≅ (𝟙 Y : Y ⟶ Y)) := by
  rcases hF.nonempty with ⟨e⟩
  refine ⟨ofBasedFunctor e.inverse, ?_, ?_⟩
  · refine ⟨?_⟩
    change (𝟙 X : X ⟶ X) ≅ F ≫ (ofBasedFunctor e.inverse : Y ⟶ X)
    exact ownerIsoOfBasedFunctorIso e.unitIso
  · refine ⟨?_⟩
    change ((ofBasedFunctor e.inverse : Y ⟶ X) ≫ F) ≅ (𝟙 Y : Y ⟶ Y)
    exact ownerIsoOfBasedFunctorIso e.counitIso

end FibredInGroupoidsMor

namespace FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}

/-- The canonical morphism from a category fibred in groupoids over `C` to the base identity
functor. -/
abbrev baseProjection (X : FibredInGroupoidsOver C) :
    X ⟶ ofFunctor (𝟭 C) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := X.p
      w := Functor.comp_id X.p }

/- The `1`-morphism underlying a bicategorical equivalence of categories fibred in groupoids over
`C` is an equivalence over the base. -/
theorem hom_isEquivalenceOverBase
    (e : Bicategory.Equivalence X Y) :
    FibredInGroupoidsMor.IsEquivalenceOverBase e.hom := by
  let hHom : X ⟶ Y := e.hom
  let hInv : Y ⟶ X := e.inv
  change BasedFunctor.IsEquivalenceOverBase (FibredInGroupoidsMor.toBasedFunctor hHom)
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      (FibredInGroupoidsMor.toBasedFunctor hInv)
      (by
        change (𝟙 X.toBasedCategory) ≅
            (FibredInGroupoidsMor.toBasedFunctor hHom ⋙
              FibredInGroupoidsMor.toBasedFunctor hInv)
        simpa [hHom, hInv] using FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.unit)
      (by
        change
          (FibredInGroupoidsMor.toBasedFunctor hInv ⋙
              FibredInGroupoidsMor.toBasedFunctor hHom) ≅
            𝟙 Y.toBasedCategory
        simpa [hHom, hInv] using FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.counit)

end FibredInGroupoidsOver

variable {X Y : FibredInGroupoidsOver C}
variable (F G : X ⟶ Y)

/- Definition 4.35.6 (4): a `2`-morphism between `1`-morphisms of categories fibred in groupoids
over `C` is the inherited morphism in the ambient hom-category of fibred categories over `C`. -/
#check (F ⟶ G)

end CategoryTheory
