module

public import stacks_project.Chap04.Definition_4_29_2
public import stacks_project.Chap04.Definition_4_3_3
public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_38_3
public import stacks_project.Chap04.Example_4_38_5
public import stacks_project.Chap04.Lemma_4_33_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS vS

namespace CategoryTheory

open Bicategory Opposite Functor ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FibredInSetsOver

variable {X Y : FibredInSetsOver C}

/-- Compatibility helper for Lemma 4.38.6: a based functor between bundled categories fibred in
sets defines the inherited owner morphism through the ambient fibred-in-groupoids owner. -/
abbrev ofBasedFunctor (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) : X ⟶ Y :=
  FibredInSetsOver.ofAmbientHom (X := X) (Y := Y)
    (FibredInGroupoidsMor.ofBasedFunctor
      (X := X.toFibredInGroupoidsOver) (Y := Y.toFibredInGroupoidsOver) F)

end FibredInSetsOver

open FibredInSetsOver

/-- Helper for Lemma 4.38.6: based functors over a fixed base are equal once their underlying
ordinary functors are equal. -/
private theorem based_functor_ext
    {X Y : BasedCategory C} {F G : X ⥤ᵇ Y} (h : F.toFunctor = G.toFunctor) :
    F = G := by
  cases F
  cases G
  cases h
  rfl

/- Domain-style sampling for Lemma 4.38.6:
- primary domain: categories fibred in sets over a fixed base and their comparison with
  `Type`-valued presheaves via the category-of-elements construction.
- inspected owner-level declarations:
  `Presheaf`,
  `FibredInSetsOver.ofFunctor`,
  `canonicalPullbackChoice`,
  `FibredInGroupoidsMor.fiberFunctor`.
- best owner abstraction: the source-facing equivalence is between the bundled owner
  `FibredInSetsOver C` and the chapter owner `Presheaf C`; the pullback action on fibers should be
  derived from the chapter owner `canonicalPullbackChoice`, and morphisms over the base should be
  read through the inherited ambient hom API rather than by re-packaging subcategory data.
- primitive data: the bundled fibred-in-sets object `X : FibredInSetsOver C` and its projection
  `X.p`.
- derived API: the functor `presheafToFibredInSetsOver`, the inverse object-presheaf
  `Functor.fiberObjectPresheaf`, and the equivalence statement.

Source/core/bridge triage:
- `source-facing`: `presheafToFibredInSetsOver`,
  `Functor.fiberObjectPresheaf`,
  `presheafToFibredInSetsOver_isEquivalence`;
- `core/canonical`: `FibredInSetsOver`, `Functor.Fiber`, `PullbackChoice.pullbackFunctor`,
  `FibredInGroupoidsMor.fiberFunctor`;
- `bridge/view`: the presheaf of fiber objects attached to a bundled fibred-in-sets object, with
  pullback action read through the owner bridge `canonicalPullbackChoice`. -/

/-- The textbook construction `F ↦ 𝒮_F` defines a functor from presheaves of sets on `C` to
categories fibred in sets over `C`. -/
def presheafToFibredInSetsOver :
    Presheaf.{max u v} C ⥤ FibredInSetsOver C where
  obj F := ofFunctor ((CategoryOfElements.π F).leftOp)
  map {X} {Y} α := by
    let G :
        BasedCategory.ofFunctor ((CategoryOfElements.π X).leftOp) ⥤ᵇ
          BasedCategory.ofFunctor ((CategoryOfElements.π Y).leftOp) :=
      { toFunctor := (CategoryOfElements.map α).op
        w := rfl }
    exact
      show ofFunctor ((CategoryOfElements.π X).leftOp) ⟶
          ofFunctor ((CategoryOfElements.π Y).leftOp) from
        ofBasedFunctor G
  map_id := by
    intro F
    rfl
  map_comp := by
    intro F G H α β
    rfl

namespace Functor

variable {S : Type uS} [Category.{vS} S]

-- Proof sketch: this is the object function of the canonical pullback functor attached to
-- `canonicalPullbackChoice p`; discreteness of the fibers makes the resulting presheaf choice
-- invariant.
/-- Pullback along an identity morphism acts trivially on the fiber-object presheaf. -/
noncomputable def fiberObjectPresheafMap
    (p : S ⥤ C) [IsFibredInSets p] {U V : Cᵒᵖ} (f : U ⟶ V) :
    p.Fiber (unop U) → p.Fiber (unop V) :=
  ((canonicalPullbackChoice p).pullbackFunctor f.unop).obj

theorem fiberObjectPresheafMap_id
    (p : S ⥤ C) [IsFibredInSets p] (U : Cᵒᵖ) :
    fiberObjectPresheafMap p (𝟙 U) = id := by
  -- In a discrete fiber, the canonical identity-pullback isomorphism rigidifies to equality.
  funext x
  simpa [fiberObjectPresheafMap] using
    (obj_ext_of_isDiscrete (((canonicalPullbackChoice p).pullbackIdIso (unop U)).inv.app x))

-- Proof sketch: apply the composition comparison `mapComp` of the owner pseudofunctor and use
-- discreteness of the target fiber to identify the comparison isomorphism with equality on
-- underlying objects.
/-- Pullback of fiber objects is contravariantly functorial in the base morphism. -/
theorem fiberObjectPresheafMap_comp
    (p : S ⥤ C) [IsFibredInSets p] {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    fiberObjectPresheafMap p (f ≫ g) =
      fiberObjectPresheafMap p g ∘ fiberObjectPresheafMap p f := by
  -- The comparison isomorphism for composite pullbacks becomes equality of objects in the
  -- discrete target fiber.
  funext x
  simpa [fiberObjectPresheafMap, Function.comp] using
    (obj_ext_of_isDiscrete
      (((canonicalPullbackChoice p).pullbackCompIso f.unop g.unop).hom.app x))

/-- The presheaf sending `U` to the set of objects of the fiber `p.Fiber U`, obtained from the
object functions of the owner pullback system `canonicalPullbackChoice p`; discreteness makes the
result independent of the choice of pullback system. -/
noncomputable def fiberObjectPresheaf
    (p : S ⥤ C) [IsFibredInSets p] : Presheaf.{uS} C where
  obj U := p.Fiber (unop U)
  map f := fiberObjectPresheafMap p f
  map_id := fiberObjectPresheafMap_id p
  map_comp := fiberObjectPresheafMap_comp p

end Functor

noncomputable def fibredInSetsOverToPresheafApp
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) (U : Cᵒᵖ) :
    (X.p.fiberObjectPresheaf).obj U →
      (Y.p.fiberObjectPresheaf).obj U :=
  (fiberFunctor F (unop U)).obj

-- Proof sketch: both composites are objects of the discrete fiber `Y_{U}` equipped with the same
-- vertical comparison morphism to the image of `x`, so they are equal.
private theorem fibredInSetsOverToPresheafApp_naturality
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) {U V : Cᵒᵖ} (f : U ⟶ V) :
    fibredInSetsOverToPresheafApp F V ∘
        (X.p.fiberObjectPresheaf).map f =
      (Y.p.fiberObjectPresheaf).map f ∘
        fibredInSetsOverToPresheafApp F U :=
  by
    funext x
    let hX := canonicalPullbackChoice X.p
    let hY := canonicalPullbackChoice Y.p
    have hf : f.unop = 𝟙 (unop V) ≫ f.unop := by
      simp
    -- The image of the chosen pullback map is still a lift over `f`, so the chosen pullback in
    -- `Y` produces a vertical comparison between the two candidate pullback objects.
    letI : X.p.IsHomLift f.unop (hX.map f.unop x) :=
      (hX.isStronglyCartesian f.unop x).toIsHomLift
    have hτ :
        Y.p.IsHomLift f.unop
          ((toBasedFunctor F).map (hX.map f.unop x)) := by
      simpa using
        (show Y.p.IsHomLift f.unop
          ((toBasedFunctor F).map (hX.map f.unop x)) from inferInstance)
    letI :
        Y.p.IsHomLift f.unop
          ((toBasedFunctor F).map (hX.map f.unop x)) :=
      hτ
    letI :
        Y.p.IsStronglyCartesian f.unop
          (hY.map f.unop (fibredInSetsOverToPresheafApp F U x)) :=
      hY.isStronglyCartesian f.unop (fibredInSetsOverToPresheafApp F U x)
    let τ' := (toBasedFunctor F).map (hX.map f.unop x)
    let ψ :=
      @IsStronglyCartesian.map _ _ _ _ Y.p
        (unop V)
        (unop U)
        (((hY.pullbackFunctor f.unop).obj (fibredInSetsOverToPresheafApp F U x)).1)
        ((fibredInSetsOverToPresheafApp F U x).1)
        f.unop
        (hY.map f.unop (fibredInSetsOverToPresheafApp F U x))
        (hY.isStronglyCartesian f.unop (fibredInSetsOverToPresheafApp F U x))
        (unop V)
        ((toBasedFunctor F).obj (((hX.pullbackFunctor f.unop).obj x).1))
        (𝟙 (unop V))
        f.unop
        hf
        τ'
        hτ
    have hψ : Y.p.IsHomLift (𝟙 (unop V)) ψ := by
      dsimp [ψ]
      infer_instance
    letI : Y.p.IsHomLift (𝟙 (unop V)) ψ := hψ
    -- Discreteness of the target fiber turns the vertical comparison into equality of objects.
    simpa [Functor.fiberObjectPresheaf, Functor.fiberObjectPresheafMap,
      fibredInSetsOverToPresheafApp] using
      (obj_ext_of_isDiscrete (Functor.Fiber.homMk Y.p (unop V) ψ))

/-- A morphism of categories fibred in sets over `C` induces a morphism between the presheaves of
objects in its fibers. -/
noncomputable def fibredInSetsOverToPresheafMap
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) :
    X.p.fiberObjectPresheaf ⟶ Y.p.fiberObjectPresheaf where
  app U := fibredInSetsOverToPresheafApp F U
  naturality := fun {_ _} f ↦ by
    ext x
    exact congrFun (fibredInSetsOverToPresheafApp_naturality F f) x

-- Proof sketch: the identity morphism of `X` induces the identity functor on each fiber, hence
-- also the identity natural transformation on the presheaf of fiber objects.
theorem fibredInSetsOverToPresheafMap_id
    (X : FibredInSetsOver C) :
    fibredInSetsOverToPresheafMap (𝟙 X) =
      𝟙 X.p.fiberObjectPresheaf := by
  -- The identity morphism induces the identity functor on every fiber.
  ext U x
  rfl

-- Proof sketch: the presheaf map attached to a composite is computed fiberwise from the composite
-- of the induced fiber functors, so functoriality reduces to functoriality of those fiberwise
-- maps on fiber objects.
theorem fibredInSetsOverToPresheafMap_comp
    {X Y Z : FibredInSetsOver C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    fibredInSetsOverToPresheafMap (F ≫ G) =
      fibredInSetsOverToPresheafMap F ≫ fibredInSetsOverToPresheafMap G := by
  -- Fiberwise, composition is computed by composition of the induced fiber functors.
  ext U x
  rfl

/-- The inverse functor in Lemma 4.38.6 sends a category fibred in sets over `C` to the presheaf
of objects in its fibers, obtained from the owner construction
`X.p.fiberObjectPresheaf`. -/
noncomputable def fibredInSetsOverToPresheaf :
    FibredInSetsOver C ⥤ Presheaf.{max u v} C where
  obj X := X.p.fiberObjectPresheaf
  map {_} {_} F := fibredInSetsOverToPresheafMap F
  map_id X := fibredInSetsOverToPresheafMap_id X
  map_comp F G := fibredInSetsOverToPresheafMap_comp F G

-- Proof sketch: for each object `a` of the source fibred category, both components of any two
-- vertical natural transformations `G ⟶ H` lie in the discrete fiber of `Y` over `X.1.p.obj a`.
-- Hence there is at most one possible component at `a`, and componentwise uniqueness gives
-- equality of the natural transformations.
/-- Any two `2`-morphisms between `1`-morphisms of categories fibred in sets over `C` are equal;
hence the ambient `2`-category is actually an ordinary category. -/
theorem fibredInSetsOverTwoHom_subsingleton
    {X Y : FibredInSetsOver C} (G H : X ⟶ Y) :
    Subsingleton (G ⟶ H) := by
  constructor
  intro τ σ
  -- The owner bicategory is built from successive full/wide subcategory wrappers, so extensional
  -- equality reduces to equality of the underlying `BasedNatTrans`.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  -- Each component is vertical over the identity, hence a morphism in the discrete fiber over
  -- `X.p.obj a`; there is therefore only one possible component.
  have hτlift :
      Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
        (τ.hom.hom.hom.hom.hom.hom.app a) := by
    exact τ.hom.hom.hom.hom.hom.hom.isHomLift (rfl : X.p.obj a = X.p.obj a)
  have hσlift :
      Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
        (σ.hom.hom.hom.hom.hom.hom.app a) := by
    exact σ.hom.hom.hom.hom.hom.hom.isHomLift (rfl : X.p.obj a = X.p.obj a)
  letI := hτlift
  letI := hσlift
  have hFiber :
      Functor.Fiber.homMk Y.p (X.p.obj a) (τ.hom.hom.hom.hom.hom.hom.app a) =
        Functor.Fiber.homMk Y.p (X.p.obj a) (σ.hom.hom.hom.hom.hom.hom.app a) :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hFiber

/-- Helper for Lemma 4.38.6: a section of a presheaf over `U` is the same thing as the
corresponding object of the fiber of the opposite category of elements over `unop U`. -/
private noncomputable def presheaf_category_of_elements_fiber_equiv
    (F : Presheaf.{max u v} C) (U : Cᵒᵖ) :
    F.obj U ≃ (((CategoryOfElements.π F).leftOp).Fiber (unop U)) where
  toFun a := Functor.Fiber.mk (a := op (F.elementsMk U a)) rfl
  invFun x := by
    -- Unpacking a fiber object over `unop U` recovers an element of `F.obj U`.
    let y := x.1.unop
    have hy : y.1 = U := by
      simpa [y, Functor.leftOp_obj, CategoryOfElements.π_obj] using x.2
    exact Eq.ndrec y.2 hy
  left_inv a := by
    -- Reading back the stored element from the canonical fiber object recovers the original
    -- section immediately.
    rfl
  right_inv x := by
    -- Every fiber object over `unop U` in the opposite category of elements is canonically of the
    -- form `op ⟨U, a⟩`; unpacking the sigma data makes the round trip definitional.
    cases x with
    | mk x hx =>
        have hx' : x.unop.1 = U := by
          simpa [Functor.leftOp_obj, CategoryOfElements.π_obj] using hx
        cases hx'
        rfl

/-- Helper for Lemma 4.38.6: the explicit element-arrow realizing pullback along `f` in the
opposite category of elements is strongly cartesian over `f.unop`. -/
private theorem presheaf_category_of_elements_pullback_hom_isStronglyCartesian
    (F : Presheaf.{max u v} C) {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) :
    Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop
      (Quiver.Hom.op <|
        CategoryOfElements.homMk
          (F.elementsMk U a)
          (F.elementsMk V (F.map f a))
          f
          rfl) := by
  -- This is the textbook pullback arrow `f^* a ⟶ a` viewed in `F.Elementsᵒᵖ`.
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · refine IsHomLift.of_fac' ((CategoryOfElements.π F).leftOp) f.unop _ rfl rfl ?_
    simp
  · intro a' g φ' hφ'
    let hgf : ((CategoryOfElements.π F).leftOp).obj a' ⟶ unop U := g ≫ f.unop
    have hComp :
        hgf = ((CategoryOfElements.π F).leftOp).map φ' := by
      exact
        @IsHomLift.eq_of_isHomLift _ _ _ _
          ((CategoryOfElements.π F).leftOp) _ _ hgf φ' hφ'
    have hVal : φ'.unop.val = f ≫ g.op := by
      simpa [hgf] using congrArg Quiver.Hom.op hComp.symm
    refine ⟨Quiver.Hom.op (CategoryOfElements.homMk _ _ g.op ?_), ⟨?_, ?_⟩, ?_⟩
    · simpa [FunctorToTypes.map_comp_apply, hVal] using φ'.unop.property
    · refine IsHomLift.of_fac' ((CategoryOfElements.π F).leftOp) g _ rfl rfl ?_
      simp
    · exact Quiver.Hom.unop_inj <| CategoryOfElements.ext F _ _ <| by
        simpa using hVal.symm
    · intro ψ hψ
      exact Quiver.Hom.unop_inj <| CategoryOfElements.ext F _ _ <| by
        have hBase : g = ((CategoryOfElements.π F).leftOp).map ψ := by
          exact
            @IsHomLift.eq_of_isHomLift _ _ _ _
              ((CategoryOfElements.π F).leftOp) _ _ g ψ hψ.1
        simpa using congrArg Quiver.Hom.op hBase.symm

/-- Helper for Lemma 4.38.6: restricting a section along `f : U ⟶ V` corresponds to the chosen
pullback of the associated category-of-elements fiber object along `f.unop`. -/
private theorem presheaf_category_of_elements_fiber_equiv_naturality
    (F : Presheaf.{max u v} C) {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) :
    presheaf_category_of_elements_fiber_equiv F V (F.map f a) =
      ((canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)).pullbackFunctor f.unop).obj
        (presheaf_category_of_elements_fiber_equiv F U a) := by
  let hc := canonicalPullbackChoice ((CategoryOfElements.π F).leftOp)
  let φexp :
      op (F.elementsMk V (F.map f a)) ⟶ op (F.elementsMk U a) :=
    Quiver.Hom.op <|
      CategoryOfElements.homMk
        (F.elementsMk U a)
        (F.elementsMk V (F.map f a))
        f
        rfl
  let φcan :
      ((hc.pullbackFunctor f.unop).obj (presheaf_category_of_elements_fiber_equiv F U a)).1 ⟶
        (presheaf_category_of_elements_fiber_equiv F U a).1 :=
    hc.map f.unop (presheaf_category_of_elements_fiber_equiv F U a)
  have hφexp :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φexp :=
    presheaf_category_of_elements_pullback_hom_isStronglyCartesian F f a
  letI :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φexp :=
    hφexp
  have hCartExp :
      Functor.IsCartesian ((CategoryOfElements.π F).leftOp) f.unop φexp :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := ((CategoryOfElements.π F).leftOp))
      (f := f.unop)
      (φ := φexp)
  have hStrongCan :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φcan :=
    hc.isStronglyCartesian f.unop (presheaf_category_of_elements_fiber_equiv F U a)
  letI :
      Functor.IsStronglyCartesian ((CategoryOfElements.π F).leftOp) f.unop φcan :=
    hStrongCan
  have hCartCan :
      Functor.IsCartesian ((CategoryOfElements.π F).leftOp) f.unop φcan :=
    Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      (p := ((CategoryOfElements.π F).leftOp))
      (f := f.unop)
      (φ := φcan)
  let e :=
    @Functor.IsCartesian.domainUniqueUpToIso _ _ _ _
      ((CategoryOfElements.π F).leftOp) _ _ _ _ f.unop φcan hCartCan _ φexp hCartExp
  have hHomLift :
      ((CategoryOfElements.π F).leftOp).IsHomLift (𝟙 (unop V)) e.hom := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _
        ((CategoryOfElements.π F).leftOp) _ _ _ _ f.unop φcan hCartCan _ φexp hCartExp)
  have hInvLift :
      ((CategoryOfElements.π F).leftOp).IsHomLift (𝟙 (unop V)) e.inv := by
    simpa [e] using
      (@Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift _ _ _ _
        ((CategoryOfElements.π F).leftOp) _ _ _ _ f.unop φcan hCartCan _ φexp hCartExp)
  let eFiber :
      presheaf_category_of_elements_fiber_equiv F V (F.map f a) ≅
        ((hc.pullbackFunctor f.unop).obj (presheaf_category_of_elements_fiber_equiv F U a)) :=
    { hom := ⟨e.hom, hHomLift⟩
      inv := ⟨e.inv, hInvLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }
  -- Comparing the two pullback arrows first turns the object-level statement into a discrete-fiber
  -- equality, which is the source-proof route.
  exact obj_ext_of_isDiscrete eFiber.hom

/-- Helper for Lemma 4.38.6: the presheaf-side round trip is naturally isomorphic to the
identity by the explicit fiber/category-of-elements identification on each object. -/
private noncomputable def presheafToFibredInSetsOver_unitIso :
    𝟭 (Presheaf.{max u v} C) ≅
      presheafToFibredInSetsOver ⋙ fibredInSetsOverToPresheaf := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · refine
        { hom := (presheaf_category_of_elements_fiber_equiv F U).toIso.hom
          inv := (presheaf_category_of_elements_fiber_equiv F U).toIso.inv
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      · ext a
        exact (presheaf_category_of_elements_fiber_equiv F U).left_inv a
      · ext x
        exact (presheaf_category_of_elements_fiber_equiv F U).right_inv x
    · intro U V f
      -- Both sides send `a` to the pullback object represented by `F.map f a`, so naturality is
      -- the explicit category-of-elements pullback object and the chosen pullback object are equal
      -- in the discrete fiber over `unop V`.
      ext a
      exact presheaf_category_of_elements_fiber_equiv_naturality F f a
  · intro F G α
    -- The comparison is objectwise `a ↦ op ⟨U, a⟩`, so compatibility with a presheaf map is
    -- again definitional.
    ext U a
    rfl

/-- Helper for Lemma 4.38.6: a morphism `phi : a ⟶ b` is the chosen pullback of `b` along its
base arrow when viewed inside the fiber-object presheaf. -/
private theorem fiber_object_presheaf_map_eq_of_hom
    {X : FibredInSetsOver C} {a b : X.S} (phi : a ⟶ b) :
    X.p.fiberObjectPresheaf.map (X.p.map phi).op (Functor.Fiber.mk rfl) = Functor.Fiber.mk rfl := by
  -- The chosen cartesian lift of `b` along `X.p.map phi` has a vertical comparison to `phi`, and
  -- discreteness of the source fiber rigidifies that comparison to equality of fiber objects.
  let hc := canonicalPullbackChoice X.p
  letI : X.p.IsStronglyCartesian (X.p.map phi) (hc.map (X.p.map phi) ⟨b, rfl⟩) :=
    hc.isStronglyCartesian (X.p.map phi) ⟨b, rfl⟩
  let e := Functor.IsCartesian.domainUniqueUpToIso X.p (X.p.map phi)
    (hc.map (X.p.map phi) ⟨b, rfl⟩) phi
  have hInvLift : X.p.IsHomLift (𝟙 (X.p.obj a)) e.inv := by
    change X.p.IsHomLift (𝟙 (X.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso X.p (X.p.map phi)
        (hc.map (X.p.map phi) ⟨b, rfl⟩) phi).inv)
    infer_instance
  have hHomLift : X.p.IsHomLift (𝟙 (X.p.obj a)) e.hom := by
    change X.p.IsHomLift (𝟙 (X.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso X.p (X.p.map phi)
        (hc.map (X.p.map phi) ⟨b, rfl⟩) phi).hom)
    infer_instance
  let eFiber :
      (((canonicalPullbackChoice X.p).pullbackFunctor (X.p.map phi)).obj ⟨b, rfl⟩) ≅
        ⟨a, rfl⟩ :=
    { hom := ⟨e.inv, hInvLift⟩
      inv := ⟨e.hom, hHomLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id }
  simpa [Functor.fiberObjectPresheaf, Functor.fiberObjectPresheafMap] using
    obj_ext_of_isDiscrete eFiber.hom

/-- Helper for Lemma 4.38.6: an element arrow in the fiber-object presheaf identifies its source
fiber object with the chosen pullback of its target fiber object. -/
private theorem fiber_object_element_source_eq
    (X : FibredInSetsOver C) {A B : (X.p.fiberObjectPresheaf).Elementsᵒᵖ}
    (k : A ⟶ B) :
    ((canonicalPullbackChoice X.p).pullbackFunctor (k.unop.1.unop)).obj B.unop.2 = A.unop.2 := by
  -- Unfold the category-of-elements condition into the chosen pullback action on fiber objects.
  rcases k.unop with ⟨g, hg⟩
  simpa [Functor.fiberObjectPresheaf, Functor.fiberObjectPresheafMap] using hg

/-- Helper for Lemma 4.38.6: the base morphism of an element arrow, rewritten into the actual
bases of the corresponding fiber objects. -/
private noncomputable abbrev fiber_object_element_base
    (X : FibredInSetsOver C) {A B : (X.p.fiberObjectPresheaf).Elementsᵒᵖ}
    (k : A ⟶ B) :
    X.p.obj A.unop.2.1 ⟶ X.p.obj B.unop.2.1 :=
  eqToHom A.unop.2.2 ≫ k.unop.1.unop ≫ eqToHom B.unop.2.2.symm

/-- Helper for Lemma 4.38.6: an element arrow of the fiber-object presheaf induces the ambient
morphism between the corresponding objects of `X` by transporting the chosen pullback map. -/
private noncomputable def fiber_object_element_hom
    (X : FibredInSetsOver C) {A B : (X.p.fiberObjectPresheaf).Elementsᵒᵖ}
    (k : A ⟶ B) :
    A.unop.2.1 ⟶ B.unop.2.1 :=
  eqToHom (congrArg Subtype.val (fiber_object_element_source_eq X k)).symm ≫
    (canonicalPullbackChoice X.p).map (k.unop.1.unop) B.unop.2

/-- Helper for Lemma 4.38.6: the category-of-elements arrow attached to a morphism of `X` is the
forward comparison morphism for the counit component. -/
private noncomputable def fiber_object_presheaf_element_hom
    (X : FibredInSetsOver C) {a b : X.S} (phi : a ⟶ b) :
    op ((X.p.fiberObjectPresheaf).elementsMk (op (X.p.obj a)) (Functor.Fiber.mk rfl)) ⟶
      op ((X.p.fiberObjectPresheaf).elementsMk (op (X.p.obj b)) (Functor.Fiber.mk rfl)) :=
  Quiver.Hom.op <|
    CategoryOfElements.homMk
      ((X.p.fiberObjectPresheaf).elementsMk (op (X.p.obj b)) (Functor.Fiber.mk rfl))
      ((X.p.fiberObjectPresheaf).elementsMk (op (X.p.obj a)) (Functor.Fiber.mk rfl))
      (X.p.map phi).op
      (by
        -- The defining property of the category-of-elements arrow is exactly the pullback
        -- identity already proved above.
        simpa using fiber_object_presheaf_map_eq_of_hom phi)

/-- Helper for Lemma 4.38.6: the transported pullback arrow associated to an element morphism is
itself a lift over the same base morphism. -/
private theorem fiber_object_element_hom_isHomLift
    (X : FibredInSetsOver C) {A B : (X.p.fiberObjectPresheaf).Elementsᵒᵖ}
    (k : A ⟶ B) :
    X.p.IsHomLift (fiber_object_element_base X k) (fiber_object_element_hom X k) := by
  -- The chosen pullback arrow is already a lift in the fiber coordinates, and transporting its
  -- source across the discrete-fiber equality keeps the same lifted base arrow.
  let hc := canonicalPullbackChoice X.p
  have hPullback :
      X.p.IsHomLift (k.unop.1.unop) (hc.map (k.unop.1.unop) B.unop.2) :=
    (hc.isStronglyCartesian (k.unop.1.unop) B.unop.2).toIsHomLift
  have hTransport :
      X.p.IsHomLift (k.unop.1.unop) (fiber_object_element_hom X k) := by
    -- Transporting the source object across the discrete-fiber equality does not change which
    -- base morphism the chosen pullback arrow lifts.
    simpa [fiber_object_element_hom] using
      (IsHomLift.comp_eqToHom_lift_iff X.p (k.unop.1.unop)
        (hc.map (k.unop.1.unop) B.unop.2)
        (congrArg Subtype.val (fiber_object_element_source_eq X k)).symm).2 hPullback
  -- The remaining source and target coordinate changes are exactly the `eqToHom` wrappers in
  -- `fiber_object_element_base X k`.
  exact
    (IsHomLift.lift_eqToHom_comp_iff X.p
      (k.unop.1.unop ≫ eqToHom B.unop.2.2.symm)
      (fiber_object_element_hom X k)
      A.unop.2.2).2 <|
      (IsHomLift.lift_comp_eqToHom_iff X.p
        (k.unop.1.unop)
        (fiber_object_element_hom X k)
        B.unop.2.2.symm).2 hTransport

/-- Helper for Lemma 4.38.6: in a category fibred in sets, a lift over a fixed base morphism with
fixed source and target is unique. -/
private theorem hom_lift_subsingleton
    (X : FibredInSetsOver C) {a b : X.S} (f : X.p.obj a ⟶ X.p.obj b) :
    Subsingleton { phi : a ⟶ b // X.p.IsHomLift f phi } := by
  let hc := canonicalPullbackChoice X.p
  letI : X.p.IsStronglyCartesian f (hc.map f ⟨b, rfl⟩) :=
    hc.isStronglyCartesian f ⟨b, rfl⟩
  constructor
  intro φ ψ
  letI : X.p.IsHomLift f φ.1 := φ.2
  letI : X.p.IsHomLift f ψ.1 := ψ.2
  have hf_id : f = 𝟙 (X.p.obj a) ≫ f := by
    simp
  let χφ :=
    IsStronglyCartesian.map X.p f (hc.map f ⟨b, rfl⟩)
      (g := 𝟙 (X.p.obj a)) hf_id φ.1
  let χψ :=
    IsStronglyCartesian.map X.p f (hc.map f ⟨b, rfl⟩)
      (g := 𝟙 (X.p.obj a)) hf_id ψ.1
  have hχφ : X.p.IsHomLift (𝟙 (X.p.obj a)) χφ := by
    dsimp [χφ]
    infer_instance
  have hχψ : X.p.IsHomLift (𝟙 (X.p.obj a)) χψ := by
    dsimp [χψ]
    infer_instance
  letI := hχφ
  letI := hχψ
  have hχ :
      Functor.Fiber.homMk X.p (X.p.obj a) χφ =
        Functor.Fiber.homMk X.p (X.p.obj a) χψ :=
    Subsingleton.elim _ _
  apply Subtype.ext
  -- After moving both lifts to the chosen pullback, discreteness of the fiber makes the
  -- comparison unique, and the strong-cartesian factorization identifies the original lifts.
  calc
    φ.1 = χφ ≫ hc.map f ⟨b, rfl⟩ := by
      symm
      exact IsStronglyCartesian.fac X.p f (hc.map f ⟨b, rfl⟩)
        (g := 𝟙 (X.p.obj a)) hf_id φ.1
    _ = χψ ≫ hc.map f ⟨b, rfl⟩ := by
      simpa using congrArg (fun ζ => ζ ≫ hc.map f ⟨b, rfl⟩) (congrArg Subtype.val hχ)
    _ = ψ.1 := by
      exact IsStronglyCartesian.fac X.p f (hc.map f ⟨b, rfl⟩)
        (g := 𝟙 (X.p.obj a)) hf_id ψ.1

/-- Helper for Lemma 4.38.6: the ambient morphism extracted from an element arrow lies over the
base arrow carried by that element arrow. -/
private theorem fiber_object_element_hom_base
    (X : FibredInSetsOver C) {A B : (X.p.fiberObjectPresheaf).Elementsᵒᵖ}
    (k : A ⟶ B) :
    X.p.map (fiber_object_element_hom X k) = fiber_object_element_base X k := by
  -- The previous helper packages the extracted morphism as a genuine lift, so its base map is
  -- the prescribed base morphism.
  letI : X.p.IsHomLift (fiber_object_element_base X k) (fiber_object_element_hom X k) :=
    fiber_object_element_hom_isHomLift X k
  exact (IsHomLift.eq_of_isHomLift X.p (fiber_object_element_base X k)
    (fiber_object_element_hom X k)).symm

/-- Helper for Lemma 4.38.6: extracting an ambient morphism from the forward image of a morphism
of `X` recovers the original morphism. -/
private theorem fiber_object_element_hom_of_hom
    (X : FibredInSetsOver C) {a b : X.S} (phi : a ⟶ b) :
    fiber_object_element_hom X (fiber_object_presheaf_element_hom X phi) = phi := by
  -- Both sides are lifts of the same base arrow with the same source and target, so uniqueness
  -- in a fibred-in-sets category forces equality.
  letI : Subsingleton { ψ : a ⟶ b // X.p.IsHomLift (X.p.map phi) ψ } :=
    hom_lift_subsingleton X (f := X.p.map phi)
  let lhs :
      { ψ : a ⟶ b // X.p.IsHomLift (X.p.map phi) ψ } :=
    ⟨fiber_object_element_hom X (fiber_object_presheaf_element_hom X phi), by
      simpa [fiber_object_element_base, fiber_object_presheaf_element_hom] using
        fiber_object_element_hom_isHomLift X (fiber_object_presheaf_element_hom X phi)⟩
  let rhs :
      { ψ : a ⟶ b // X.p.IsHomLift (X.p.map phi) ψ } :=
    ⟨phi, inferInstance⟩
  exact congrArg Subtype.val (Subsingleton.elim lhs rhs)

/-- Helper for Lemma 4.38.6: extracting an ambient morphism from the identity element arrow gives
the identity morphism. -/
private theorem fiber_object_element_hom_id
    (X : FibredInSetsOver C) (A : (X.p.fiberObjectPresheaf).Elementsᵒᵖ) :
    fiber_object_element_hom X (𝟙 A) = 𝟙 A.unop.2.1 := by
  -- This is the identity case of uniqueness of lifts over an identity morphism.
  letI : Subsingleton { ψ : A.unop.2.1 ⟶ A.unop.2.1 //
      X.p.IsHomLift (𝟙 (X.p.obj A.unop.2.1)) ψ } :=
    hom_lift_subsingleton X (f := 𝟙 (X.p.obj A.unop.2.1))
  let lhs :
      { ψ : A.unop.2.1 ⟶ A.unop.2.1 // X.p.IsHomLift (𝟙 (X.p.obj A.unop.2.1)) ψ } :=
    ⟨fiber_object_element_hom X (𝟙 A), by
      simpa [fiber_object_element_base] using fiber_object_element_hom_isHomLift X (𝟙 A)⟩
  let rhs :
      { ψ : A.unop.2.1 ⟶ A.unop.2.1 // X.p.IsHomLift (𝟙 (X.p.obj A.unop.2.1)) ψ } :=
    ⟨𝟙 A.unop.2.1, inferInstance⟩
  exact congrArg Subtype.val (Subsingleton.elim lhs rhs)

/-- Helper for Lemma 4.38.6: extracting ambient morphisms from a composite element arrow is
compatible with composition. -/
private theorem fiber_object_element_hom_comp
    (X : FibredInSetsOver C) {A B D : (X.p.fiberObjectPresheaf).Elementsᵒᵖ}
    (k : A ⟶ B) (l : B ⟶ D) :
    fiber_object_element_hom X (k ≫ l) =
      fiber_object_element_hom X k ≫ fiber_object_element_hom X l := by
  -- Both composites are lifts of the same composite base arrow between the same source and
  -- target, so uniqueness reduces functoriality to the fibred-in-sets lifting property.
  letI : Subsingleton { ψ : A.unop.2.1 ⟶ D.unop.2.1 //
      X.p.IsHomLift (fiber_object_element_base X (k ≫ l)) ψ } :=
    hom_lift_subsingleton X (f := fiber_object_element_base X (k ≫ l))
  let lhs :
      { ψ : A.unop.2.1 ⟶ D.unop.2.1 // X.p.IsHomLift (fiber_object_element_base X (k ≫ l)) ψ } :=
    ⟨fiber_object_element_hom X (k ≫ l),
      fiber_object_element_hom_isHomLift X (k ≫ l)⟩
  let rhs :
      { ψ : A.unop.2.1 ⟶ D.unop.2.1 // X.p.IsHomLift (fiber_object_element_base X (k ≫ l)) ψ } :=
    ⟨fiber_object_element_hom X k ≫ fiber_object_element_hom X l, by
      letI : X.p.IsHomLift (fiber_object_element_base X k) (fiber_object_element_hom X k) :=
        fiber_object_element_hom_isHomLift X k
      letI : X.p.IsHomLift (fiber_object_element_base X l) (fiber_object_element_hom X l) :=
        fiber_object_element_hom_isHomLift X l
      simpa [fiber_object_element_base, Category.assoc] using (inferInstance :
        X.p.IsHomLift (fiber_object_element_base X k ≫ fiber_object_element_base X l)
          (fiber_object_element_hom X k ≫ fiber_object_element_hom X l))⟩
  exact congrArg Subtype.val (Subsingleton.elim lhs rhs)

/-- Helper for Lemma 4.38.6: the total category of the fiber-object presheaf of `X`, viewed as a
based category over `C`. -/
private noncomputable abbrev fiber_object_presheaf_total (X : FibredInSetsOver C) :=
  BasedCategory.ofFunctor ((CategoryOfElements.π X.p.fiberObjectPresheaf).leftOp)

/-- Helper for Lemma 4.38.6: the category-of-elements arrow attached to an identity morphism of
`X` is the identity arrow in the opposite category of elements. -/
private theorem fiber_object_presheaf_element_hom_id
    (X : FibredInSetsOver C) (a : X.S) :
    fiber_object_presheaf_element_hom X (𝟙 a) = 𝟙 _ := by
  -- The category-of-elements arrow is determined by its base arrow, which is `X.p.map_id`.
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext (X.p.fiberObjectPresheaf) _ _
  simp [fiber_object_presheaf_element_hom] at *

/-- Helper for Lemma 4.38.6: the category-of-elements arrow attached to a composite in `X`
factors as the composite of the attached element arrows. -/
private theorem fiber_object_presheaf_element_hom_comp
    (X : FibredInSetsOver C) {a b c : X.S} (phi : a ⟶ b) (psi : b ⟶ c) :
    fiber_object_presheaf_element_hom X (phi ≫ psi) =
      fiber_object_presheaf_element_hom X phi ≫ fiber_object_presheaf_element_hom X psi := by
  -- The base morphism in the category of elements is the opposite of `X.p.map_comp`.
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext (X.p.fiberObjectPresheaf) _ _
  simp [fiber_object_presheaf_element_hom] at *

/-- Helper for Lemma 4.38.6: the forward comparison functor from `X` to the category of elements
of its fiber-object presheaf. -/
private noncomputable def fiber_object_presheaf_to_elements
    (X : FibredInSetsOver C) :
    X.toBasedCategory ⥤ᵇ fiber_object_presheaf_total X where
  toFunctor :=
    { obj := fun a ↦
        op ((X.p.fiberObjectPresheaf).elementsMk (op (X.p.obj a)) (Functor.Fiber.mk rfl))
      map := fun phi ↦ fiber_object_presheaf_element_hom X phi
      map_id := by
        intro a
        -- The forward comparison respects identities because its base-arrow description does.
        simpa using fiber_object_presheaf_element_hom_id X a
      map_comp := by
        intro a b c phi psi
        -- Composition is likewise determined by the base-arrow computation in the category of
        -- elements.
        simpa using fiber_object_presheaf_element_hom_comp X phi psi }
  w := rfl

/-- Helper for Lemma 4.38.6: the backward comparison functor from the category of elements of the
fiber-object presheaf of `X` back to `X`. -/
private noncomputable def fiber_object_presheaf_from_elements
    (X : FibredInSetsOver C) :
    fiber_object_presheaf_total X ⥤ᵇ X.toBasedCategory where
  toFunctor :=
    { obj := fun A ↦ A.unop.2.1
      map := fun k ↦ fiber_object_element_hom X k
      map_id := by
        intro A
        simpa using fiber_object_element_hom_id X A
      map_comp := by
        intro A B D k l
        simpa using fiber_object_element_hom_comp X k l }
  w := by
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro A
      simpa [fiber_object_presheaf_total] using A.unop.2.2
    · intro A B k
      simpa [fiber_object_presheaf_total] using fiber_object_element_hom_base X k

/-- Helper for Lemma 4.38.6: the forward comparison packaged as a morphism of categories fibred in
sets over `C`. -/
private noncomputable def fiber_object_presheaf_counit_inv
    (X : FibredInSetsOver C) :
    X ⟶ presheafToFibredInSetsOver.obj (fibredInSetsOverToPresheaf.obj X) := by
  -- This is the textbook map `a ↦ (p(a), a)` written as a based functor over `C`.
  exact
    show X ⟶ FibredInSetsOver.ofFunctor ((CategoryOfElements.π X.p.fiberObjectPresheaf).leftOp) from
      FibredInSetsOver.ofBasedFunctor (fiber_object_presheaf_to_elements X)

/-- Helper for Lemma 4.38.6: the backward comparison packaged as a morphism of categories fibred in
sets over `C`. -/
private noncomputable def fiber_object_presheaf_counit_hom
    (X : FibredInSetsOver C) :
    presheafToFibredInSetsOver.obj (fibredInSetsOverToPresheaf.obj X) ⟶ X := by
  -- This is the textbook forgetful map from the category of elements back to the original fibred
  -- category.
  exact
    show FibredInSetsOver.ofFunctor ((CategoryOfElements.π X.p.fiberObjectPresheaf).leftOp) ⟶ X from
      FibredInSetsOver.ofBasedFunctor (fiber_object_presheaf_from_elements X)

/-- Helper for Lemma 4.38.6: unpacking an opposite category-of-elements object and repacking it
from its fiber object gives the same object again. -/
private theorem fiber_object_presheaf_round_trip_obj
    (X : FibredInSetsOver C) (A : (X.p.fiberObjectPresheaf).Elementsᵒᵖ) :
    op ((X.p.fiberObjectPresheaf).elementsMk
      (op (X.p.obj A.unop.2.1)) (Functor.Fiber.mk rfl)) = A := by
  -- The opposite element already consists of exactly this base object together with this fiber
  -- object; unpacking first the opposite base object and then the fiber witness makes the round
  -- trip literal.
  cases A
  rename_i A
  cases A with
  | mk U x =>
      cases U
      rename_i U
      cases x with
      | mk a ha =>
          cases ha
          rfl

/-- Helper for Lemma 4.38.6: the `eqToHom` transport attached to the object round trip has the
expected base arrow in the opposite category of elements. -/
private theorem fiber_object_presheaf_round_trip_obj_eqToHom_val
    (X : FibredInSetsOver C) (A : (X.p.fiberObjectPresheaf).Elementsᵒᵖ) :
    ((eqToHom (fiber_object_presheaf_round_trip_obj X A)).unop).val =
      eqToHom (congrArg Opposite.op A.unop.2.2).symm := by
  -- The round-trip equality is literally obtained by unpacking the opposite element data, so the
  -- induced transport arrow on bases is definitionally the corresponding `eqToHom`.
  cases A
  rename_i A
  cases A with
  | mk U x =>
      cases U
      rename_i U
      cases x with
      | mk a ha =>
          cases ha
          rfl

/-- Helper for Lemma 4.38.6: moving from `X` to the category of elements of its fiber-object
presheaf and back is strictly the identity on the underlying based functor. -/
private theorem fiber_object_presheaf_hom_inv_id
    (X : FibredInSetsOver C) :
    (show X.toBasedCategory ⥤ᵇ X.toBasedCategory from
      BasedFunctor.comp (fiber_object_presheaf_to_elements X) (fiber_object_presheaf_from_elements X)) =
      𝟙 X.toBasedCategory := by
  -- The object part is definitional, and the morphism part is the already-established
  -- round-trip `phi ↦ (p(phi), phi) ↦ phi`.
  apply based_functor_ext
  -- Choosing the object equality to be definitional keeps the map comparison on the nose.
  refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
  intro a b phi
  change fiber_object_element_hom X (fiber_object_presheaf_element_hom X phi) =
    eqToHom rfl ≫ phi ≫ eqToHom rfl
  simpa using fiber_object_element_hom_of_hom X phi

/-- Helper for Lemma 4.38.6: moving from the category of elements of the fiber-object presheaf of
`X` back to `X` and forward again is strictly the identity on the underlying based functor. -/
private theorem fiber_object_presheaf_inv_hom_id
    (X : FibredInSetsOver C) :
    (show fiber_object_presheaf_total X ⥤ᵇ fiber_object_presheaf_total X from
      BasedFunctor.comp (fiber_object_presheaf_from_elements X) (fiber_object_presheaf_to_elements X)) =
      𝟙 fiber_object_presheaf_total X := by
  -- The objectwise round trip is obtained by unpacking the opposite element together with its
  -- fiber witness, and morphisms are then determined by their base arrows in the category of
  -- elements.
  -- Route correction: the missing work is the explicit `eqToHom` transport in the category of
  -- elements, not a new abstract comparison functor.
  apply based_functor_ext
  -- Using heterogeneous extensionality keeps the morphism comparison in the native object
  -- coordinates and avoids additional `eqToHom` transport bookkeeping.
  refine CategoryTheory.Functor.hext (fiber_object_presheaf_round_trip_obj X) ?_
  intro A B k
  -- Once the opposite elements are unpacked, the round trip on a morphism is exactly the base
  -- arrow already computed by `fiber_object_element_hom_base`.
  cases A
  rename_i A
  cases A with
  | mk U a =>
      cases U
      rename_i U
      cases a with
      | mk a ha =>
          cases ha
          cases B
          rename_i B
          cases B with
          | mk V b =>
              cases V
              rename_i V
              cases b with
              | mk b hb =>
                  cases hb
                  have hk :
                      (fiber_object_presheaf_to_elements X).map
                          ((fiber_object_presheaf_from_elements X).map k) = k := by
                    apply Quiver.Hom.unop_inj
                    apply CategoryOfElements.ext (X.p.fiberObjectPresheaf) _ _
                    simpa [fiber_object_presheaf_to_elements, fiber_object_presheaf_from_elements,
                      fiber_object_presheaf_element_hom] using
                      congrArg Quiver.Hom.op (fiber_object_element_hom_base X k)
                  exact heq_of_eq hk

/-- Helper for Lemma 4.38.6: morphisms of fibred-in-sets categories are determined by their
underlying based functors. -/
private theorem fibredInSetsOver_hom_eq_of_toBasedFunctor_eq
    {X Y : FibredInSetsOver C} {F G : X ⟶ Y}
    (h : FibredInSetsOver.toBasedFunctor F = FibredInSetsOver.toBasedFunctor G) :
    F = G := by
  -- The bundled homs are nested induced/wide-subcategory wrappers, so extensionality peels the
  -- wrappers until only the underlying based functor remains.
  rcases F with ⟨⟨F₁⟩⟩
  rcases G with ⟨⟨G₁⟩⟩
  rcases F₁ with ⟨⟨F₂⟩⟩
  rcases G₁ with ⟨⟨G₂⟩⟩
  rcases F₂ with ⟨⟨F₃⟩⟩
  rcases G₂ with ⟨⟨G₃⟩⟩
  congr

/-- Helper for Lemma 4.38.6: counit naturality is strict on underlying based functors. -/
private theorem fiber_object_presheaf_counit_naturality_based
    {X Y : FibredInSetsOver C} (F : X ⟶ Y) :
    FibredInSetsOver.toBasedFunctor
        (((fibredInSetsOverToPresheaf ⋙ presheafToFibredInSetsOver).map F) ≫
          fiber_object_presheaf_counit_hom Y) =
      FibredInSetsOver.toBasedFunctor (fiber_object_presheaf_counit_hom X ≫ F) := by
  -- The source and target objects agree definitionally, while on morphisms both composites are
  -- lifts over the same base arrow in `Y`, so uniqueness in the discrete fibers forces equality.
  apply based_functor_ext
  -- Heterogeneous extensionality lets us work directly with the explicit formulas for both
  -- composites on a fixed arrow of the category of elements.
  refine CategoryTheory.Functor.hext (fun A ↦ rfl) ?_
  intro A B k
  -- After unpacking the category-of-elements objects, both composites become ambient morphisms in
  -- `Y` between the same source and target objects.
  cases A
  rename_i A
  cases A with
  | mk U a =>
      cases U
      rename_i U
      cases a with
      | mk a ha =>
          cases ha
          cases B
          rename_i B
          cases B with
          | mk V b =>
              cases V
              rename_i V
              cases b with
              | mk b hb =>
                  cases hb
                  change fiber_object_element_hom Y
                      (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map k) ≍
                    (toBasedFunctor F).map (fiber_object_element_hom X k)
                  have hEq :
                      fiber_object_element_hom Y
                          (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map k) =
                        (toBasedFunctor F).map (fiber_object_element_hom X k) := by
                    have hbase :
                        Y.p.map ((toBasedFunctor F).map (fiber_object_element_hom X k)) =
                          fiber_object_element_base Y
                            (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map
                              k) := by
                      -- The mapped ambient morphism lies over exactly the base arrow obtained by
                      -- applying `CategoryOfElements.map` to `k`.
                      calc
                        Y.p.map ((toBasedFunctor F).map (fiber_object_element_hom X k)) =
                            eqToHom ((toBasedFunctor F).w_obj a) ≫
                              X.p.map (fiber_object_element_hom X k) ≫
                                eqToHom ((toBasedFunctor F).w_obj b).symm := by
                                  have hcongr :
                                      eqToHom ((toBasedFunctor F).w_obj a) ≫
                                          X.p.map (fiber_object_element_hom X k) ≫
                                            eqToHom ((toBasedFunctor F).w_obj b).symm =
                                        Y.p.map
                                          ((toBasedFunctor F).map (fiber_object_element_hom X k)) := by
                                    simpa [Category.assoc] using
                                      (Functor.congr_hom (toBasedFunctor F).w
                                        (fiber_object_element_hom X k)).symm
                                  exact hcongr.symm
                        _ = eqToHom ((toBasedFunctor F).w_obj a) ≫ fiber_object_element_base X k ≫
                            eqToHom ((toBasedFunctor F).w_obj b).symm := by
                              rw [fiber_object_element_hom_base X k]
                        _ = fiber_object_element_base Y
                            (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map
                              k) := by
                              rcases k.unop with ⟨g, hg⟩
                              simp [fiber_object_element_base, fibredInSetsOverToPresheafMap,
                                fibredInSetsOverToPresheafApp]
                              rfl
                    let g :=
                      fiber_object_element_base Y
                        (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map k)
                    letI :
                        Subsingleton { ψ : (toBasedFunctor F).obj a ⟶ (toBasedFunctor F).obj b //
                          Y.p.IsHomLift g ψ } :=
                      hom_lift_subsingleton Y (f := g)
                    let lhs :
                        { ψ : (toBasedFunctor F).obj a ⟶ (toBasedFunctor F).obj b //
                          Y.p.IsHomLift g ψ } := by
                      refine ⟨fiber_object_element_hom Y
                          (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map k),
                        ?_⟩
                      -- The extracted morphism from the mapped element arrow is, by construction,
                      -- a lift over its own base morphism.
                      simpa [g] using
                        fiber_object_element_hom_isHomLift Y
                          (((CategoryOfElements.map (fibredInSetsOverToPresheafMap F)).op).map k)
                    let rhs :
                        { ψ : (toBasedFunctor F).obj a ⟶ (toBasedFunctor F).obj b //
                          Y.p.IsHomLift g ψ } := by
                      refine ⟨(toBasedFunctor F).map (fiber_object_element_hom X k), ?_⟩
                      have hSelf :
                          Y.p.IsHomLift
                              (Y.p.map ((toBasedFunctor F).map (fiber_object_element_hom X k)))
                              ((toBasedFunctor F).map (fiber_object_element_hom X k)) := by
                        infer_instance
                      -- Replacing the base morphism by the explicit one computed above moves the
                      -- right-hand morphism into the same singleton of lifts as the left-hand one.
                      exact (show Y.p.IsHomLift g
                          ((toBasedFunctor F).map (fiber_object_element_hom X k)) from by
                        simpa [g] using hbase ▸ hSelf)
                    exact congrArg Subtype.val (Subsingleton.elim lhs rhs)
                  exact heq_of_eq hEq

/-- Helper for Lemma 4.38.6: the counit of the presheaf/fibred-in-sets equivalence is obtained
from the explicit forward and backward comparison functors on each object. -/
private noncomputable def presheafToFibredInSetsOver_counitIso :
    fibredInSetsOverToPresheaf ⋙ presheafToFibredInSetsOver ≅ 𝟭 (FibredInSetsOver C) := by
  -- The component maps are the explicit forward/backward comparison functors, and naturality is
  -- already strict on the underlying based functors.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine
      { hom := fiber_object_presheaf_counit_hom X
        inv := fiber_object_presheaf_counit_inv X
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply fibredInSetsOver_hom_eq_of_toBasedFunctor_eq
      simpa [FibredInSetsOver.toBasedFunctor, fiber_object_presheaf_counit_hom,
        fiber_object_presheaf_counit_inv] using fiber_object_presheaf_inv_hom_id X
    · apply fibredInSetsOver_hom_eq_of_toBasedFunctor_eq
      simpa [FibredInSetsOver.toBasedFunctor, fiber_object_presheaf_counit_hom,
        fiber_object_presheaf_counit_inv] using fiber_object_presheaf_hom_inv_id X
  · intro X Y F
    apply fibredInSetsOver_hom_eq_of_toBasedFunctor_eq
    simpa [FibredInSetsOver.toBasedFunctor] using fiber_object_presheaf_counit_naturality_based F

/-- Lemma 4.38.6: the category-of-elements construction from presheaves of sets on `C` to
categories fibred in sets over `C` is an equivalence, with inverse given by the presheaf of
objects in the fibers. -/
theorem presheafToFibredInSetsOver_isEquivalence :
    Functor.IsEquivalence
      (presheafToFibredInSetsOver :
        Presheaf.{max u v} C ⥤ FibredInSetsOver C) := by
  -- Route correction: the missing step is the explicit round-trip between sections, fiber
  -- objects, and category-of-elements objects, not another abstract pullback argument.
  refine Functor.IsEquivalence.mk' fibredInSetsOverToPresheaf ?_ ?_
  · -- The presheaf-side unit is exactly the objectwise identification between sections and
    -- objects in the corresponding fiber of the opposite category of elements.
    exact presheafToFibredInSetsOver_unitIso
  · -- The fibred-side counit is the strict comparison between `X` and the category of elements
    -- of the presheaf of objects in its fibers.
    exact presheafToFibredInSetsOver_counitIso

end CategoryTheory
