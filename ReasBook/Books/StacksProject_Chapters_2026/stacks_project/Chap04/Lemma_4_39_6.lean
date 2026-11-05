module

public import stacks_project.Chap04.Definition_4_39_3
public import stacks_project.Chap04.Lemma_4_35_9
public import stacks_project.Chap04.Lemma_4_39_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open scoped Bicategory

open Functor BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y Z : FibredInSetoidsOver C}

/- Domain-style sampling for Lemma 4.39.6:
- primary domain: categories fibred in setoids over a fixed base, their presheaves of fiberwise
  isomorphism classes, and the induced comparison with categories fibred in sets;
- inspected owner-level declarations:
  `Functor.fiberIsoClassPresheaf`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets`,
  `presheafToFibredInSetsOver`;
- best owner abstraction: the core/canonical owners are the presheaf
  `X.p.fiberIsoClassPresheaf` and the associated fibred-in-sets object
  `X.associatedFibredInSets`; the functorial constructions in this file should be thin bridge/view
  data built directly from those owners;
- primitive data: a bundled fibred-in-setoids object or morphism over `C`;
- derived API: the induced presheaf morphism on isomorphism classes, the induced fibred-in-sets
  morphism, and the quotient-level comparison on homs.

Source/core/bridge triage:
- `source-facing`: `fibredInSetoidsToPresheaf`, `fibredInSetoidsToFibredInSets`, and the final
  hom-level comparison;
- `core/canonical`: `Functor.fiberIsoClassPresheaf`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets`,
  `presheafToFibredInSetsOver`;
- `bridge/view`: the helper proofs relating morphisms in `FibredInSetoidsOver C` to morphisms of
  the associated presheaves and associated fibred-in-sets objects. -/

noncomputable def fiberIsoClassPresheafMapApp
    (F : X ⟶ Y) (U : Cᵒᵖ) :
    (X.p.fiberIsoClassPresheaf).obj U →
      (Y.p.fiberIsoClassPresheaf).obj U :=
  isomorphismClasses.map
    ((FibredInGroupoidsMor.fiberFunctor F (unop U)).toCatHom)

/-- Helper for Lemma 4.39.6: applying a morphism of fibred-in-setoids categories to a chosen
pullback object gives an object isomorphic to the chosen pullback of the image object in the
target fiber. -/
private theorem fiberIsoClassPullbackComparisonIso
    (F : X ⟶ Y) {U V : Cᵒᵖ} (f : U ⟶ V) (x : X.p.Fiber (unop U)) :
    Nonempty
      (((FibredInGroupoidsMor.fiberFunctor F.toHom (unop V)).obj
        (((canonicalPullbackChoice X.p).pullbackFunctor f.unop).obj x)) ≅
      ((canonicalPullbackChoice Y.p).pullbackFunctor f.unop).obj
        ((FibredInGroupoidsMor.fiberFunctor F.toHom (unop U)).obj x)) := by
  let hX := canonicalPullbackChoice X.p
  let hY := canonicalPullbackChoice Y.p
  let xPull := ((hX.pullbackFunctor f.unop).obj x)
  let yImg := (FibredInGroupoidsMor.fiberFunctor F.toHom (unop U)).obj x
  let yPull := ((hY.pullbackFunctor f.unop).obj yImg)
  have hf : f.unop = 𝟙 (unop V) ≫ f.unop := by
    simp
  -- The chosen pullback in `X` maps to a lift over `f`, so strong cartesianness in `Y`
  -- produces a vertical comparison to the chosen pullback of the image object.
  letI : X.p.IsHomLift f.unop (hX.map f.unop x) :=
    (hX.isStronglyCartesian f.unop x).toIsHomLift
  have hτ :
      Y.p.IsHomLift f.unop
        ((FibredInSetoidsOver.toBasedFunctor F).map (hX.map f.unop x)) := by
    simpa using
      (show Y.p.IsHomLift f.unop
        ((FibredInSetoidsOver.toBasedFunctor F).map (hX.map f.unop x)) from inferInstance)
  letI :
      Y.p.IsHomLift f.unop
        ((FibredInSetoidsOver.toBasedFunctor F).map (hX.map f.unop x)) :=
    hτ
  let τ' := (FibredInSetoidsOver.toBasedFunctor F).map (hX.map f.unop x)
  let ψ :=
    @IsStronglyCartesian.map _ _ _ _ Y.p
      (unop V)
      (unop U)
      yPull.1
      yImg.1
      f.unop
      (hY.map f.unop yImg)
      (hY.isStronglyCartesian f.unop yImg)
      (unop V)
      ((FibredInSetoidsOver.toBasedFunctor F).obj xPull.1)
      (𝟙 (unop V))
      f.unop
      hf
      τ'
      hτ
  have hψ : Y.p.IsHomLift (𝟙 (unop V)) ψ := by
    dsimp [ψ]
    infer_instance
  let m :
      ((FibredInGroupoidsMor.fiberFunctor F.toHom (unop V)).obj xPull) ⟶ yPull :=
    ⟨ψ, hψ⟩
  -- A vertical morphism in a setoid fiber is automatically an isomorphism there.
  exact ⟨asIso m⟩

-- Proof sketch: both composites apply the fiberwise map induced by `F` together with the canonical
-- pullback functors on `X` and `Y`; the commutation with the base projections gives a canonical
-- comparison in each target fiber, and setoidness makes that comparison unique on isomorphism
-- classes.
theorem fiberIsoClassPresheafMap_naturality
    (F : X ⟶ Y) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (X.p.fiberIsoClassPresheaf).map f ≫
        fiberIsoClassPresheafMapApp F V =
      fiberIsoClassPresheafMapApp F U ≫
        (Y.p.fiberIsoClassPresheaf).map f := by
  ext q
  refine Quotient.inductionOn q ?_
  intro x
  -- Both sides are quotient classes of the two pullback objects compared above.
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (unop V)))
      ((FibredInGroupoidsMor.fiberFunctor F (unop V)).obj
        (((canonicalPullbackChoice X.p).pullbackFunctor f.unop).obj x)) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (unop V)))
        (((canonicalPullbackChoice Y.p).pullbackFunctor f.unop).obj
          ((FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x))
  rw [Quotient.eq'']
  -- The comparison isomorphism in the target fiber identifies the two representatives.
  exact fiberIsoClassPullbackComparisonIso F f x

/-- A morphism of fibred categories over `C` induces a morphism between the presheaves of
isomorphism classes of objects in the fibers. -/
noncomputable def fibredInSetoidsToPresheafMap (F : X ⟶ Y) :
    X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf where
  app U := fiberIsoClassPresheafMapApp F U
  naturality := fun {_ _} f ↦ fiberIsoClassPresheafMap_naturality F f

-- Proof sketch: the identity morphism of `X` induces the identity map on each fiber, hence also
-- the identity natural transformation on the presheaf of isomorphism classes.
private theorem fibredInSetoidsToPresheafMap_id
    (X : FibredInSetoidsOver C) :
    fibredInSetoidsToPresheafMap (𝟙 X) =
      𝟙 X.p.fiberIsoClassPresheaf := by
  -- The identity morphism acts as the identity functor on every fiber.
  ext U q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

-- Proof sketch: the presheaf map attached to a composite is computed fiberwise from the composite
-- of the induced fiber functors, so functoriality reduces to functoriality of those fiberwise
-- maps on isomorphism classes.
private theorem fibredInSetoidsToPresheafMap_comp
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    fibredInSetoidsToPresheafMap (F ≫ G) =
      fibredInSetoidsToPresheafMap F ≫ fibredInSetoidsToPresheafMap G := by
  -- Fiberwise, the map on isomorphism classes is induced by the composite fiber functor.
  ext U q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The presheaf of isomorphism classes in the fibers defines a functor from categories fibred in
setoids over `C` to presheaves of sets on `C`. -/
noncomputable def fibredInSetoidsToPresheaf :
    FibredInSetoidsOver C ⥤ Presheaf.{max u₁ v₁} C where
  obj X := X.p.fiberIsoClassPresheaf
  map {X} {Y} F := fibredInSetoidsToPresheafMap F
  map_id X := by
    exact fibredInSetoidsToPresheafMap_id X
  map_comp F G := by
    exact fibredInSetoidsToPresheafMap_comp F G

/-- Helper for Lemma 4.39.6: the category-of-elements construction sends a presheaf of sets on
`C` to the corresponding category fibred in sets over `C`. This local bridge avoids importing the
full Lemma 4.38.6 file, whose current generated source is not import-stable in this workspace. -/
noncomputable def presheafToFibredInSetsOverLocal :
    Presheaf.{max u₁ v₁} C ⥤ FibredInSetsOver C where
  obj F := FibredInSetsOver.ofFunctor ((CategoryOfElements.π F).leftOp)
  map {X} {Y} α := by
    let G :
        BasedCategory.ofFunctor ((CategoryOfElements.π X).leftOp) ⥤ᵇ
          BasedCategory.ofFunctor ((CategoryOfElements.π Y).leftOp) :=
      { toFunctor := (CategoryOfElements.map α).op
        w := rfl }
    exact
      show FibredInSetsOver.ofFunctor ((CategoryOfElements.π X).leftOp) ⟶
          FibredInSetsOver.ofFunctor ((CategoryOfElements.π Y).leftOp) from
        FibredInSetsOver.ofAmbientHom (FibredInGroupoidsMor.ofBasedFunctor G)
  map_id := by
    intro F
    rfl
  map_comp := by
    intro F G H α β
    rfl

/-- Lemma 4.39.6 (1): taking isomorphism classes in each fiber and then applying the category of
 elements construction defines a functor from categories fibred in setoids over `C` to categories
 fibred in sets over `C`, reusing the source-facing replacement object
 `FibredInSetoidsOver.associatedFibredInSets` from Lemma 4.39.5. -/
-- TODO: define this functor by sending `X` to `X.associatedFibredInSets` and sending a morphism
-- `F` to the map induced on the category of elements by `fibredInSetoidsToPresheaf.map F`; the
-- current blocker is packaging the identity/composition laws without triggering elaboration
-- timeouts in the generated owner wrappers.
noncomputable def fibredInSetoidsToFibredInSets :
    FibredInSetoidsOver C ⥤ FibredInSetsOver C :=
  fibredInSetoidsToPresheaf ⋙ presheafToFibredInSetsOverLocal

/-- Helper for Lemma 4.39.6: equality of associated fibred-in-sets maps forces equality of the
fiberwise quotient classes attached to each source object. -/
private theorem quotient_eq_of_associated_map_eq
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    (h : fibredInSetoidsToFibredInSets.map F =
      fibredInSetoidsToFibredInSets.map G) (a : X.S) :
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
      ((FibredInGroupoidsMor.fiberFunctor F.toHom (X.p.obj a)).obj ⟨a, rfl⟩) =
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
      ((FibredInGroupoidsMor.fiberFunctor G.toHom (X.p.obj a)).obj ⟨a, rfl⟩) := by
  let x :=
    op ((X.p.fiberIsoClassPresheaf).elementsMk
      (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩))
  -- Evaluating the equal associated maps on the element-object of `a` identifies the two quotient
  -- classes represented by the images of `a`.
  have hObj :=
    congrArg (fun K ↦ (FibredInSetsOver.toBasedFunctor K).obj x) h
  change
    op ((Y.p.fiberIsoClassPresheaf).elementsMk (op (X.p.obj a))
      (@Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
        ((FibredInGroupoidsMor.fiberFunctor F.toHom (X.p.obj a)).obj ⟨a, rfl⟩))) =
    op ((Y.p.fiberIsoClassPresheaf).elementsMk (op (X.p.obj a))
      (@Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
        ((FibredInGroupoidsMor.fiberFunctor G.toHom (X.p.obj a)).obj ⟨a, rfl⟩))) at hObj
  rw [Opposite.op_inj_iff] at hObj
  have hPair := Sigma.mk.inj_iff.mp hObj
  simpa using hPair.2

/-- Helper for Lemma 4.39.6: equality after passage to associated fibred-in-sets objects produces
a chosen isomorphism between the images of a fixed source object in the target fiber. -/
private noncomputable def chosen_fiber_iso_of_associated_map_eq
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    (h : fibredInSetoidsToFibredInSets.map F =
      fibredInSetoidsToFibredInSets.map G)
    (a : X.S) :
    (FibredInGroupoidsMor.fiberFunctor F.toHom (X.p.obj a)).obj ⟨a, rfl⟩ ≅
      (FibredInGroupoidsMor.fiberFunctor G.toHom (X.p.obj a)).obj ⟨a, rfl⟩ := by
  -- The quotient equality is exactly the witness needed to choose a fiberwise isomorphism.
  exact Classical.choice
    (Quotient.exact (quotient_eq_of_associated_map_eq (X := X) (Y := Y) h a))

/-- Helper for Lemma 4.39.6: in a category fibred in setoids, a lift over a fixed base morphism
with fixed source and target is unique. -/
private theorem fibredInSetoids_hom_lift_subsingleton
    (Y : FibredInSetoidsOver C) {a b : Y.S} (f : Y.p.obj a ⟶ Y.p.obj b) :
    Subsingleton { phi : a ⟶ b // Y.p.IsHomLift f phi } := by
  let hc := canonicalPullbackChoice Y.p
  letI : Y.p.IsStronglyCartesian f (hc.map f ⟨b, rfl⟩) :=
    hc.isStronglyCartesian f ⟨b, rfl⟩
  constructor
  intro φ ψ
  letI : Y.p.IsHomLift f φ.1 := φ.2
  letI : Y.p.IsHomLift f ψ.1 := ψ.2
  have hf_id : f = 𝟙 (Y.p.obj a) ≫ f := by
    simp
  let χφ :=
    IsStronglyCartesian.map Y.p f (hc.map f ⟨b, rfl⟩)
      (g := 𝟙 (Y.p.obj a)) hf_id φ.1
  let χψ :=
    IsStronglyCartesian.map Y.p f (hc.map f ⟨b, rfl⟩)
      (g := 𝟙 (Y.p.obj a)) hf_id ψ.1
  have hχφ : Y.p.IsHomLift (𝟙 (Y.p.obj a)) χφ := by
    dsimp [χφ]
    infer_instance
  have hχψ : Y.p.IsHomLift (𝟙 (Y.p.obj a)) χψ := by
    dsimp [χψ]
    infer_instance
  letI := hχφ
  letI := hχψ
  have hχ :
      Functor.Fiber.homMk Y.p (Y.p.obj a) χφ =
        Functor.Fiber.homMk Y.p (Y.p.obj a) χψ :=
    Subsingleton.elim _ _
  apply Subtype.ext
  -- Move both lifts to the chosen pullback; thinness of the target fiber identifies them there.
  calc
    φ.1 = χφ ≫ hc.map f ⟨b, rfl⟩ := by
      symm
      exact IsStronglyCartesian.fac Y.p f (hc.map f ⟨b, rfl⟩)
        (g := 𝟙 (Y.p.obj a)) hf_id φ.1
    _ = χψ ≫ hc.map f ⟨b, rfl⟩ := by
      simpa using congrArg (fun ζ => ζ ≫ hc.map f ⟨b, rfl⟩) (congrArg Subtype.val hχ)
    _ = ψ.1 := by
      exact IsStronglyCartesian.fac Y.p f (hc.map f ⟨b, rfl⟩)
        (g := 𝟙 (Y.p.obj a)) hf_id ψ.1

/-- Helper for Lemma 4.39.6: equality of the induced presheaf maps gives pointwise isomorphisms
between the fiber images of each source object. -/
private noncomputable def chosen_fiber_iso_of_presheaf_map_eq
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    (h : fibredInSetoidsToPresheaf.map F =
      fibredInSetoidsToPresheaf.map G)
    (a : X.S) :
    (FibredInGroupoidsMor.fiberFunctor F.toHom (X.p.obj a)).obj ⟨a, rfl⟩ ≅
      (FibredInGroupoidsMor.fiberFunctor G.toHom (X.p.obj a)).obj ⟨a, rfl⟩ := by
  have hApp :=
    congrFun
      (congrArg (fun α => α.app (op (X.p.obj a))) h)
      (Quotient.mk'' ⟨a, rfl⟩)
  exact Classical.choice (Quotient.exact hApp)

-- Proof sketch: if two `1`-morphisms induce the same morphism after passing to isomorphism
-- classes, then for each source object their images in the target fiber are isomorphic. Because
-- the target is fibred in setoids, these fiberwise isomorphisms are unique and assemble into a
-- unique vertical natural isomorphism.
/-- If two `1`-morphisms become equal after applying
`fibredInSetoidsToFibredInSets`, then they are `2`-isomorphic. Uniqueness is supplied separately
by `fibredInSetoidsOverTwoIso_subsingleton`. -/
theorem fibredInSetoidsToFibredInSets_nonempty_iso_of_map_eq
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    (h : fibredInSetoidsToFibredInSets.map F =
      fibredInSetoidsToFibredInSets.map G) :
    Nonempty (F ≅ G) := by
  let F' := FibredInSetoidsOver.toBasedFunctor F
  let G' := FibredInSetoidsOver.toBasedFunctor G
  let componentIso :
      ∀ a : X.S, F'.obj a ≅ G'.obj a :=
    fun a ↦
      let e := chosen_fiber_iso_of_associated_map_eq (X := X) (Y := Y) (F := F) (G := G) h a
      show F'.obj a ≅ G'.obj a from
      { hom := e.hom.1
        inv := e.inv.1
        hom_inv_id := by
          exact congrArg Subtype.val e.hom_inv_id
        inv_hom_id := by
          exact congrArg Subtype.val e.inv_hom_id }
  have hComponentLift :
      ∀ a : X.S, Y.p.IsHomLift (𝟙 (X.p.obj a)) ((componentIso a).hom) := by
    intro a
    let e := chosen_fiber_iso_of_associated_map_eq (X := X) (Y := Y) (F := F) (G := G) h a
    change Y.p.IsHomLift (𝟙 (X.p.obj a)) e.hom.1
    exact e.hom.2
  let τNat : F'.toFunctor ≅ G'.toFunctor := by
    refine NatIso.ofComponents componentIso ?_
    intro a b φ
    let base :=
      Y.p.map (F'.map φ ≫ (componentIso b).hom)
    have hLeft :
        Y.p.IsHomLift base (F'.map φ ≫ (componentIso b).hom) := by
      exact inferInstance
    have hFBase :
        Y.p.map (F'.map φ) =
          eqToHom (BasedFunctor.w_obj F' a) ≫
            X.p.map φ ≫
              eqToHom (BasedFunctor.w_obj F' b).symm := by
      have hcongr :
          eqToHom (BasedFunctor.w_obj F' a) ≫
              X.p.map φ ≫
                eqToHom (BasedFunctor.w_obj F' b).symm =
            Y.p.map (F'.map φ) := by
        simpa [Category.assoc] using
          (Functor.congr_hom F'.w φ).symm
      exact hcongr.symm
    have hGBase :
        Y.p.map (G'.map φ) =
          eqToHom (BasedFunctor.w_obj G' a) ≫
            X.p.map φ ≫
              eqToHom (BasedFunctor.w_obj G' b).symm := by
      have hcongr :
          eqToHom (BasedFunctor.w_obj G' a) ≫
              X.p.map φ ≫
                eqToHom (BasedFunctor.w_obj G' b).symm =
            Y.p.map (G'.map φ) := by
        simpa [Category.assoc] using
          (Functor.congr_hom G'.w φ).symm
      exact hcongr.symm
    have hCompA :
        Y.p.map ((componentIso a).hom) =
          eqToHom (BasedFunctor.w_obj F' a) ≫
            𝟙 (X.p.obj a) ≫
              eqToHom (BasedFunctor.w_obj G' a).symm := by
      simpa using IsHomLift.fac' Y.p (𝟙 (X.p.obj a)) ((componentIso a).hom)
    have hCompB :
        Y.p.map ((componentIso b).hom) =
          eqToHom (BasedFunctor.w_obj F' b) ≫
            𝟙 (X.p.obj b) ≫
              eqToHom (BasedFunctor.w_obj G' b).symm := by
      simpa using IsHomLift.fac' Y.p (𝟙 (X.p.obj b)) ((componentIso b).hom)
    have hRightBase :
        Y.p.map ((componentIso a).hom ≫ G'.map φ) = base := by
      calc
        Y.p.map ((componentIso a).hom ≫ G'.map φ) =
            Y.p.map ((componentIso a).hom) ≫ Y.p.map (G'.map φ) := by
              simp
        _ =
            (eqToHom (BasedFunctor.w_obj F' a) ≫
                𝟙 (X.p.obj a) ≫
                  eqToHom (BasedFunctor.w_obj G' a).symm) ≫
              (eqToHom (BasedFunctor.w_obj G' a) ≫
                X.p.map φ ≫
                  eqToHom (BasedFunctor.w_obj G' b).symm) := by
              rw [hCompA, hGBase]
        _ =
            eqToHom (BasedFunctor.w_obj F' a) ≫
              X.p.map φ ≫
                eqToHom (BasedFunctor.w_obj G' b).symm := by
              simp
        _ =
            (eqToHom (BasedFunctor.w_obj F' a) ≫
                X.p.map φ ≫
                  eqToHom (BasedFunctor.w_obj F' b).symm) ≫
              (eqToHom (BasedFunctor.w_obj F' b) ≫
                𝟙 (X.p.obj b) ≫
                  eqToHom (BasedFunctor.w_obj G' b).symm) := by
              simp [Category.assoc]
        _ = Y.p.map (F'.map φ) ≫ Y.p.map ((componentIso b).hom) := by
              rw [hFBase, hCompB]
        _ = base := by
              simp [base]
    have hRight :
        Y.p.IsHomLift base ((componentIso a).hom ≫ G'.map φ) := by
      have hRightSelf :
          Y.p.IsHomLift
            (Y.p.map ((componentIso a).hom ≫ G'.map φ))
            ((componentIso a).hom ≫ G'.map φ) := by
        exact inferInstance
      simpa [base, hRightBase] using hRightSelf
    letI :
        Subsingleton { ψ : F'.obj a ⟶ G'.obj b // Y.p.IsHomLift base ψ } :=
      fibredInSetoids_hom_lift_subsingleton (Y := Y) (f := base)
    have hEq :
        (F'.map φ ≫ (componentIso b).hom) =
          ((componentIso a).hom ≫ G'.map φ) :=
      congrArg Subtype.val (Subsingleton.elim ⟨_, hLeft⟩ ⟨_, hRight⟩)
    simpa using hEq
  let τBased : F' ≅ G' :=
    BasedNatIso.mkNatIso τNat hComponentLift
  let τBasedAmbient :
      FibredInGroupoidsMor.toBasedFunctor F.toHom ≅
        FibredInGroupoidsMor.toBasedFunctor G.toHom := by
    simpa [F', G', FibredInSetoidsOver.toBasedFunctor] using τBased
  let τFibredCategory :
      FibredInGroupoidsMor.toFibredCategoryMor F.toHom ≅
        FibredInGroupoidsMor.toFibredCategoryMor G.toHom :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ τBasedAmbient) trivial trivial
  let τAmbient : F.toHom ≅ G.toHom :=
    CategoryTheory.isoMk
      (ObjectProperty.isoMk _ τFibredCategory)
      trivial
      trivial
  exact ⟨FibredInSetoidsOver.ofAmbientIso τAmbient⟩

-- Proof sketch: any `2`-morphism between `F` and `G` is vertical over the identity on each base
-- object by `fibredCategoryMor_hom_isHomLift_id`; since `Y` is fibred in setoids, each component
-- lies in a thin fiber and is therefore unique. Componentwise uniqueness then forces equality of
-- `2`-morphisms.
/-- Any two `2`-morphisms between `1`-morphisms of categories fibred in setoids over `C` are
equal. -/
theorem fibredInSetoidsOverTwoHom_subsingleton
    {X Y : FibredInSetoidsOver C} (F G : X ⟶ Y) :
    Subsingleton (F ⟶ G) := by
  constructor
  intro τ σ
  -- Equality in the owner hom-category reduces to equality of the underlying based natural
  -- transformations, so it suffices to compare components.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext a
  -- Each component is vertical over the identity, hence a morphism in the thin fiber of `Y`
  -- over `X.p.obj a`; thinness makes the component unique.
  have hτlift :
      Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
        (τ.hom.hom.hom.hom.hom.hom.app a) := by
    exact (τ.hom.hom.hom.hom.hom.hom).isHomLift rfl
  have hσlift :
      Functor.IsHomLift Y.p (𝟙 (X.p.obj a))
        (σ.hom.hom.hom.hom.hom.hom.app a) := by
    exact (σ.hom.hom.hom.hom.hom.hom).isHomLift rfl
  letI := hτlift
  letI := hσlift
  have hFiber :
      Functor.Fiber.homMk Y.p (X.p.obj a) (τ.hom.hom.hom.hom.hom.hom.app a) =
        Functor.Fiber.homMk Y.p (X.p.obj a) (σ.hom.hom.hom.hom.hom.hom.app a) :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hFiber

-- Proof sketch: a `2`-isomorphism is determined by its forward and inverse `2`-morphisms, and
-- those are already unique by `fibredInSetoidsOverTwoHom_subsingleton`.
/-- Any two `2`-isomorphisms between `1`-morphisms of categories fibred in setoids over `C` are
equal. -/
theorem fibredInSetoidsOverTwoIso_subsingleton
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y}
    : Subsingleton (F ≅ G) := by
  constructor
  intro τ σ
  -- An isomorphism is determined by its forward and inverse `2`-morphisms, and both hom-types
  -- are already subsingletons.
  cases τ
  cases σ
  congr
  · exact (fibredInSetoidsOverTwoHom_subsingleton F G).elim _ _
  · exact (fibredInSetoidsOverTwoHom_subsingleton G F).elim _ _

/-- Helper for Lemma 4.39.6: based functors over a fixed base are determined by their underlying
ordinary functors. -/
private theorem based_functor_ext
    {X Y : BasedCategory C} {F G : X ⥤ᵇ Y} (h : F.toFunctor = G.toFunctor) :
    F = G := by
  -- The extra based-functor structure is proof data, so equality of the ordinary functor part
  -- forces equality of the whole based functor.
  cases F
  cases G
  cases h
  rfl

/-- Helper for Lemma 4.39.6: morphisms of categories fibred in sets are determined by their
underlying based functors. -/
private theorem fibredInSetsOver_hom_eq_of_toBasedFunctor_eq
    {X Y : FibredInSetsOver C} {F G : X ⟶ Y}
    (h : FibredInSetsOver.toBasedFunctor F = FibredInSetsOver.toBasedFunctor G) :
    F = G := by
  -- The bundled homs are nested induced/wide-subcategory wrappers, so extensionality peels the
  -- wrappers until only the underlying based functor remains.
  rcases F with ⟨⟨F₁⟩⟩
  rcases G with ⟨⟨G₁⟩⟩
  congr
  rcases F₁ with ⟨⟨F₂⟩⟩
  rcases G₁ with ⟨⟨G₂⟩⟩
  congr
  rcases F₂ with ⟨⟨F₃⟩⟩
  rcases G₂ with ⟨⟨G₃⟩⟩
  congr

/-- Helper for Lemma 4.39.6: a section of a presheaf over `U` is the same thing as an object of
the fiber of the opposite category of elements over `unop U`. -/
private noncomputable def presheaf_category_of_elements_fiber_equiv
    (F : Presheaf.{max u₁ v₁} C) (U : Cᵒᵖ) :
    F.obj U ≃ (((CategoryOfElements.π F).leftOp).Fiber (unop U)) where
  toFun a := Functor.Fiber.mk (a := op (F.elementsMk U a)) rfl
  invFun x := by
    -- Unpacking a fiber object over `unop U` recovers the corresponding section of `F` over `U`.
    let y := x.1.unop
    have hy : y.1 = U := by
      simpa [y, Functor.leftOp_obj, CategoryOfElements.π_obj] using x.2
    exact Eq.ndrec y.2 hy
  left_inv a := by
    -- The canonical fiber object built from `a` reads back to `a` immediately.
    rfl
  right_inv x := by
    -- Every object over `unop U` in the opposite category of elements is canonically `op ⟨U, a⟩`.
    cases x with
    | mk x hx =>
        have hx' : x.unop.1 = U := by
          simpa [Functor.leftOp_obj, CategoryOfElements.π_obj] using hx
        cases hx'
        rfl

/-- Helper for Lemma 4.39.6: evaluate a morphism of local categories of elements on the
distinguished object attached to `x`. -/
private noncomputable def presheaf_map_preimage_app
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (U : Cᵒᵖ) :
    P.obj U → Q.obj U :=
  fun x ↦
    (presheaf_category_of_elements_fiber_equiv Q U).symm
      ⟨(FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x)), by
        -- The image object lies over the same base because `H` is a based functor over `C`.
        change (presheafToFibredInSetsOverLocal.obj Q).toBasedCategory.p.obj
            ((FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x))) =
          (presheafToFibredInSetsOverLocal.obj P).toBasedCategory.p.obj
            (op (P.elementsMk U x))
        exact BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H) (op (P.elementsMk U x))⟩

/-- Helper for Lemma 4.39.6: the image of a distinguished element object under a morphism of local
categories of elements is again a distinguished element object over the same base. -/
private theorem presheaf_map_preimage_exists
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    ∃ y : Q.obj U,
      (unop ((FibredInSetsOver.toBasedFunctor H).obj
        (op (P.elementsMk U x)))) = Q.elementsMk U y := by
  -- The local inverse-on-objects is obtained by reading the image object as a fiber object over
  -- `unop U` and transporting it back through the explicit fiber equivalence.
  refine ⟨presheaf_map_preimage_app H U x, ?_⟩
  let A : (((CategoryOfElements.π Q).leftOp).Fiber (unop U)) :=
    ⟨(FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x)), by
      -- This is the same base-preservation fact used in `presheaf_map_preimage_app`.
      change (presheafToFibredInSetsOverLocal.obj Q).toBasedCategory.p.obj
          ((FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x))) =
        (presheafToFibredInSetsOverLocal.obj P).toBasedCategory.p.obj
          (op (P.elementsMk U x))
      exact BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H) (op (P.elementsMk U x))⟩
  have hA :=
    congrArg Subtype.val
      ((presheaf_category_of_elements_fiber_equiv Q U).right_inv A).symm
  exact congrArg Opposite.unop hA

/-- Helper for Lemma 4.39.6: the image of a distinguished element object under a morphism of local
categories of elements is identified with the distinguished object attached to the extracted
element. -/
private theorem presheaf_map_preimage_spec
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (U : Cᵒᵖ) (x : P.obj U) :
    (unop ((FibredInSetsOver.toBasedFunctor H).obj
      (op (P.elementsMk U x)))) =
      Q.elementsMk U (presheaf_map_preimage_app H U x) :=
by
  -- This is the right-inverse formula for the explicit fiber equivalence used to define
  -- `presheaf_map_preimage_app`.
  let A : (((CategoryOfElements.π Q).leftOp).Fiber (unop U)) :=
    ⟨(FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x)), by
      change (presheafToFibredInSetsOverLocal.obj Q).toBasedCategory.p.obj
          ((FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x))) =
        (presheafToFibredInSetsOverLocal.obj P).toBasedCategory.p.obj
          (op (P.elementsMk U x))
      exact BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H) (op (P.elementsMk U x))⟩
  have hA :=
    congrArg Subtype.val
      ((presheaf_category_of_elements_fiber_equiv Q U).right_inv A).symm
  exact congrArg Opposite.unop hA

/-- Helper for Lemma 4.39.6: the distinguished-object round trip for the local inverse-on-homs is
strict on objects. -/
private theorem presheaf_map_preimage_round_trip_obj
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (A : P.Elementsᵒᵖ) :
    op (Q.elementsMk A.unop.1 (presheaf_map_preimage_app H A.unop.1 A.unop.2)) =
      (FibredInSetsOver.toBasedFunctor H).obj A := by
  -- The reconstructed element was defined precisely so that the image object of `A` is this
  -- distinguished element object.
  cases A
  rename_i A
  cases A with
  | mk U x =>
      exact congrArg Opposite.op (presheaf_map_preimage_spec H U x).symm

/-- Helper for Lemma 4.39.6: the round-trip object equality identifies the base object of the
image of an opposite element with the original base object. -/
private theorem presheaf_map_preimage_round_trip_obj_base
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (A : P.Elementsᵒᵖ) :
    A.unop.1 = (unop ((FibredInSetsOver.toBasedFunctor H).obj A)).1 := by
  -- Passing the round-trip object equality back to `Q.Elements` and projecting to the base
  -- coordinate records exactly which object of `Cᵒᵖ` underlies the image of `A`.
  simpa using
    congrArg (fun Z : Q.Elements => Z.1)
      (congrArg Opposite.unop (presheaf_map_preimage_round_trip_obj H A))

/-- Helper for Lemma 4.39.6: after transporting the endpoints of the image of a morphism in
`P.Elementsᵒᵖ` along the round-trip object equalities, its base arrow is the original base arrow. -/
private theorem presheaf_map_preimage_round_trip_base
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    {A B : P.Elementsᵒᵖ} (k : A ⟶ B) :
    k.unop.1 =
      eqToHom (presheaf_map_preimage_round_trip_obj_base H B) ≫
        ((FibredInSetsOver.toBasedFunctor H).map k).unop.1 ≫
          eqToHom (presheaf_map_preimage_round_trip_obj_base H A).symm := by
  cases A
  rename_i A
  cases A with
  | mk U x =>
      cases B
      rename_i B
      cases B with
      | mk V y =>
          -- The based-functor compatibility for `H` gives the transported base arrow identity in
          -- `C`; passing to opposites and cancelling the endpoint transports yields the desired
          -- equality in `Cᵒᵖ`.
          have hw := Functor.congr_hom (FibredInSetsOver.toBasedFunctor H).w k
          have hbase :
              eqToHom (presheaf_map_preimage_round_trip_obj_base H (Opposite.op ⟨V, y⟩)).symm ≫
                  k.unop.1 ≫
                    eqToHom (presheaf_map_preimage_round_trip_obj_base H (Opposite.op ⟨U, x⟩)) =
                ((FibredInSetsOver.toBasedFunctor H).map k).unop.1 := by
            simpa [eqToHom_op, presheaf_map_preimage_round_trip_obj_base] using
              congrArg Quiver.Hom.op hw.symm
          have hleft :
              k.unop.1 ≫
                  eqToHom (presheaf_map_preimage_round_trip_obj_base H (Opposite.op ⟨U, x⟩)) =
                eqToHom (presheaf_map_preimage_round_trip_obj_base H (Opposite.op ⟨V, y⟩)) ≫
                  ((FibredInSetsOver.toBasedFunctor H).map k).unop.1 := by
            exact (eqToHom_comp_iff _ _ _).mp hbase
          simpa [Category.assoc] using (comp_eqToHom_iff _ _ _).mp hleft

/-- Helper for Lemma 4.39.6: once a morphism in `Q.Elements` is transported to distinguished
endpoints, its defining property becomes the corresponding section equation. -/
private theorem categoryOfElements_hom_property_transport
    {Q : Presheaf.{max u₁ v₁} C} {U V : Cᵒᵖ} (f : U ⟶ V)
    {x : Q.obj U} {y : Q.obj V} {A B : Q.Elements} (g : A ⟶ B)
    (hA : A = Q.elementsMk U x) (hB : B = Q.elementsMk V y)
    (hbase : (eqToHom hA.symm ≫ g ≫ eqToHom hB).1 = f) :
    Q.map f x = y := by
  simpa [hbase] using (eqToHom hA.symm ≫ g ≫ eqToHom hB).property

/-- Helper for Lemma 4.39.6: the base arrow of an `eqToHom` in a category of elements becomes the
corresponding `eqToHom` on first coordinates after passing back to the base category. -/
private theorem categoryOfElements_eqToHom_base_unop
    {Q : Presheaf.{max u₁ v₁} C} {A B : Q.Elements} (h : A = B) :
    ((eqToHom h).1).unop =
      eqToHom (congrArg (fun z : Q.Elements => unop z.1) h).symm := by
  -- After reducing to reflexivity, both sides are the identity on the common base object.
  cases h
  rfl

/-- Helper for Lemma 4.39.6: consecutive transports along an equality and its inverse cancel in
the base category. -/
private theorem eqToHom_symm_comp_eqToHom
    {X Y : C} (h : X = Y) :
    eqToHom h.symm ≫ eqToHom h = 𝟙 Y := by
  -- After reducing to reflexivity, both transports are identities.
  cases h
  simp

/-- Helper for Lemma 4.39.6: cancel a transport pair on the left of a morphism in the base
category. -/
private theorem eqToHom_symm_comp_eqToHom_assoc
    {X Y Z : C} (h : X = Y) (f : Y ⟶ Z) :
    eqToHom h.symm ≫ (eqToHom h ≫ f) = f := by
  -- After reducing to reflexivity, the transport pair becomes identities.
  cases h
  simp

/-- Helper for Lemma 4.39.6: cancel a transport pair on the right of a morphism in the base
category. -/
private theorem comp_eqToHom_symm_assoc_eqToHom
    {X Y Z : C} (f : X ⟶ Y) (h : Z = Y) :
    (f ≫ eqToHom h.symm) ≫ eqToHom h = f := by
  -- After reducing to reflexivity, the transport pair becomes identities.
  cases h
  simp

/-- Helper for Lemma 4.39.6: the function obtained by evaluating a category-of-elements morphism
on distinguished objects is natural in the base object. -/
private theorem presheaf_map_preimage_naturality
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q) :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V),
      P.map f ≫ presheaf_map_preimage_app H V =
        presheaf_map_preimage_app H U ≫ Q.map f := by
  intro U V f
  funext x
  -- Apply `H` to the canonical element arrow encoding the restriction of `x` along `f`.
  let A :=
    unop ((FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk U x)))
  let B :=
    unop ((FibredInSetsOver.toBasedFunctor H).obj (op (P.elementsMk V (P.map f x))))
  let k :
      op (P.elementsMk V (P.map f x)) ⟶ op (P.elementsMk U x) :=
    Quiver.Hom.op <|
      CategoryOfElements.homMk
        (P.elementsMk U x)
        (P.elementsMk V (P.map f x))
        f
        rfl
  let hk : A ⟶ B := by
    simpa [A, B] using Quiver.Hom.unop ((FibredInSetsOver.toBasedFunctor H).map k)
  -- Rewriting the endpoints by the defining specification of `presheaf_map_preimage_app`
  -- turns the mapped arrow into an element-arrow in `Q`.
  have hA : A = Q.elementsMk U (presheaf_map_preimage_app H U x) := by
    simpa [A] using presheaf_map_preimage_spec H U x
  have hB : B = Q.elementsMk V (presheaf_map_preimage_app H V (P.map f x)) := by
    simpa [B] using presheaf_map_preimage_spec H V (P.map f x)
  have hp :
      (presheafToFibredInSetsOverLocal.obj P).toBasedCategory.p.map k = f.unop := by
    rfl
  have hq :
      (presheafToFibredInSetsOverLocal.obj Q).toBasedCategory.p.map
          ((FibredInSetsOver.toBasedFunctor H).map k) = hk.1.unop := by
    rfl
  have hw := Functor.congr_hom (FibredInSetsOver.toBasedFunctor H).w k
  have hkBase : (eqToHom hA.symm ≫ hk ≫ eqToHom hB).1 = f := by
    -- The base-arrow comparison comes from the defining equality `H ⋙ p = p` for a based
    -- functor, after rewriting the image endpoints by the distinguished-object specifications.
    apply Quiver.Hom.unop_inj
    dsimp [A, B] at hA hB ⊢
    subst A
    subst B
    rw [← hq]
    have hw' :
        (presheafToFibredInSetsOverLocal.obj Q).toBasedCategory.p.map
            ((FibredInSetsOver.toBasedFunctor H).map k) =
          eqToHom
              (BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H)
                (op (P.elementsMk V (P.map f x)))) ≫
            f.unop ≫
              eqToHom
                (BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H)
                  (op (P.elementsMk U x))).symm := by
      simpa [hp] using hw
    rw [hw']
    -- The remaining transport is the endpoint bookkeeping hidden in the opposite category of
    -- elements.
    have hA_base :
        ((eqToHom hA.symm).1).unop =
          eqToHom
            (BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H)
              (op (P.elementsMk U x))) := by
      -- The source endpoint rewrite uses the same object equality encoded by `H.w_obj`.
      simpa using
        (categoryOfElements_eqToHom_base_unop (Q := Q) hA.symm)
    have hB_base :
        ((eqToHom hB).1).unop =
          eqToHom
            (BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H)
              (op (P.elementsMk V (P.map f x)))).symm := by
      -- The target endpoint rewrite is the inverse transport on the corresponding base object.
      simpa using
        (categoryOfElements_eqToHom_base_unop (Q := Q) hB)
    let eU :=
      BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H) (op (P.elementsMk U x))
    let eV :=
      BasedFunctor.w_obj (FibredInSetsOver.toBasedFunctor H) (op (P.elementsMk V (P.map f x)))
    -- Once the endpoint transports are rewritten in the base category, they cancel pairwise.
    rw [hB_base, hA_base]
    have hleft :
        eqToHom eV.symm ≫ (eqToHom eV ≫ f.unop ≫ eqToHom eU.symm) =
          f.unop ≫ eqToHom eU.symm := by
      -- Cancel the left transport pair coming from the target endpoint.
      change eqToHom eV.symm ≫ (eqToHom eV ≫ (f.unop ≫ eqToHom eU.symm)) =
        f.unop ≫ eqToHom eU.symm
      exact eqToHom_symm_comp_eqToHom_assoc eV (f.unop ≫ eqToHom eU.symm)
    have hright :
        (f.unop ≫ eqToHom eU.symm) ≫ eqToHom eU = f.unop := by
      -- Cancel the right transport pair coming from the source endpoint.
      exact comp_eqToHom_symm_assoc_eqToHom (f := f.unop) eU
    exact (congrArg (fun k => k ≫ eqToHom eU) hleft).trans hright
  -- The transported image arrow is exactly the distinguished element arrow over `f`.
  exact (categoryOfElements_hom_property_transport f hk hA hB hkBase).symm

/-- Helper for Lemma 4.39.6: the local inverse-on-homs extracted from distinguished element
objects. -/
private noncomputable def presheaf_map_preimage
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q) :
    P ⟶ Q where
  app := presheaf_map_preimage_app H
  naturality := fun {_ _} f ↦ presheaf_map_preimage_naturality H f

/-- Helper for Lemma 4.39.6: reconstructing the presheaf map from `H` preserves the underlying
base arrow of a morphism in the opposite category of elements. -/
private theorem presheaf_map_preimage_reconstructed_base
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    {A B : P.Elementsᵒᵖ} (k : A ⟶ B) :
    (((FibredInSetsOver.toBasedFunctor
        (presheafToFibredInSetsOverLocal.map (presheaf_map_preimage H))).map k).unop).1 =
      (k.unop).1 := by
  -- Unfolding the local category-of-elements functor shows that it acts by the opposite of the
  -- reconstructed presheaf map, so the underlying base arrow is unchanged.
  simp [presheafToFibredInSetsOverLocal, presheaf_map_preimage]

/-- Helper for Lemma 4.39.6: the transport on a round-trip object equality has the expected base
arrow in `Q.Elements`. -/
private theorem presheaf_map_preimage_round_trip_eqToHom_base
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (A : P.Elementsᵒᵖ) :
    ((eqToHom (presheaf_map_preimage_round_trip_obj H A)).unop).1 =
      eqToHom (presheaf_map_preimage_round_trip_obj_base H A).symm := by
  -- Passing to `Q.Elements` and then to the base category turns the opposite transport into the
  -- corresponding `eqToHom` on first coordinates.
  apply Quiver.Hom.unop_inj
  simpa [presheaf_map_preimage_round_trip_obj_base, eqToHom_unop] using
    (categoryOfElements_eqToHom_base_unop (Q := Q)
      (congrArg Opposite.unop (presheaf_map_preimage_round_trip_obj H A).symm))

/-- Helper for Lemma 4.39.6: the inverse round-trip transport has the corresponding inverse base
arrow in `Q.Elements`. -/
private theorem presheaf_map_preimage_round_trip_eqToHom_base_symm
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    (A : P.Elementsᵒᵖ) :
    ((eqToHom (presheaf_map_preimage_round_trip_obj H A).symm).unop).1 =
      eqToHom (presheaf_map_preimage_round_trip_obj_base H A) := by
  -- This is the same transport computation with the object equality reversed.
  apply Quiver.Hom.unop_inj
  simpa [presheaf_map_preimage_round_trip_obj_base, eqToHom_unop] using
    (categoryOfElements_eqToHom_base_unop (Q := Q)
      (congrArg Opposite.unop (presheaf_map_preimage_round_trip_obj H A)))

/-- Helper for Lemma 4.39.6: after transporting the source and target of the round-trip local
category-of-elements map, its action on a morphism is literally the original morphism. -/
private theorem presheaf_map_preimage_round_trip_hom
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q)
    {A B : P.Elementsᵒᵖ} (k : A ⟶ B) :
    (FibredInSetsOver.toBasedFunctor
      (presheafToFibredInSetsOverLocal.map (presheaf_map_preimage H))).map k =
      eqToHom (presheaf_map_preimage_round_trip_obj H A) ≫
        (FibredInSetsOver.toBasedFunctor H).map k ≫
          eqToHom (presheaf_map_preimage_round_trip_obj H B).symm := by
  -- Route correction: after moving to `Q.Elements`, the only data left is the base arrow.
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext Q _ _
  -- The reconstructed map has the same base arrow as `k`, while the transported original map has
  -- the same base arrow by the explicit round-trip transport lemma.
  calc
    (((FibredInSetsOver.toBasedFunctor
          (presheafToFibredInSetsOverLocal.map (presheaf_map_preimage H))).map k).unop).1 =
        (k.unop).1 := by
          exact presheaf_map_preimage_reconstructed_base H k
    _ =
        eqToHom (presheaf_map_preimage_round_trip_obj_base H B) ≫
          ((FibredInSetsOver.toBasedFunctor H).map k).unop.1 ≫
            eqToHom (presheaf_map_preimage_round_trip_obj_base H A).symm := by
          exact presheaf_map_preimage_round_trip_base H k
    _ =
        ((eqToHom (presheaf_map_preimage_round_trip_obj H A) ≫
              (FibredInSetsOver.toBasedFunctor H).map k ≫
                eqToHom (presheaf_map_preimage_round_trip_obj H B).symm).unop).1 := by
          -- The endpoint transports appearing after `unop` are exactly the explicit base
          -- transports already identified above.
          rw [show
              ((eqToHom (presheaf_map_preimage_round_trip_obj H A) ≫
                    (FibredInSetsOver.toBasedFunctor H).map k ≫
                      eqToHom (presheaf_map_preimage_round_trip_obj H B).symm).unop).1 =
                ((eqToHom (presheaf_map_preimage_round_trip_obj H B).symm).unop).1 ≫
                  ((FibredInSetsOver.toBasedFunctor H).map k).unop.1 ≫
                    ((eqToHom (presheaf_map_preimage_round_trip_obj H A)).unop).1 by
              simp [Category.assoc]]
          rw [presheaf_map_preimage_round_trip_eqToHom_base_symm,
            presheaf_map_preimage_round_trip_eqToHom_base]

/-- Helper for Lemma 4.39.6: reconstructing a presheaf map from a morphism of local categories of
elements and then applying the local category-of-elements functor returns the original morphism. -/
private theorem presheaf_map_preimage_of_elements_hom
    {P Q : Presheaf.{max u₁ v₁} C}
    (H : presheafToFibredInSetsOverLocal.obj P ⟶
      presheafToFibredInSetsOverLocal.obj Q) :
    presheafToFibredInSetsOverLocal.map (presheaf_map_preimage H) = H := by
  -- Route correction: the remaining issue is not constructing the inverse-on-homs but
  -- strictifying the round-trip object equalities through the `eqToHom` terms in the opposite
  -- category of elements so that `Functor.hext` closes on the nose.
  apply fibredInSetsOver_hom_eq_of_toBasedFunctor_eq
  apply based_functor_ext
  -- The object round trip is already strict, so only the transported morphism clause remains.
  refine Functor.hext (presheaf_map_preimage_round_trip_obj H) ?_
  intro A B k
  exact
    (conj_eqToHom_iff_heq _ _
      (presheaf_map_preimage_round_trip_obj H A)
      (presheaf_map_preimage_round_trip_obj H B)).1
      (presheaf_map_preimage_round_trip_hom H k)
/-- Helper for Lemma 4.39.6: the local category-of-elements functor should be bijective on homs.
The intended proof is the local 4.38.6 counit construction for categories of elements, but that
comparison API is not yet available in this file. -/
private theorem presheafToFibredInSetsOverLocal_hom_bijective
    (P Q : Presheaf.{max u₁ v₁} C) :
    Function.Bijective (fun α : P ⟶ Q ↦ presheafToFibredInSetsOverLocal.map α) := by
  constructor
  · intro α β hαβ
    -- Equality on the fibred-in-sets side can be tested on distinguished element objects.
    ext U x
    have hObj :=
      congrArg
        (fun K : presheafToFibredInSetsOverLocal.obj P ⟶
            presheafToFibredInSetsOverLocal.obj Q ↦
          (FibredInSetsOver.toBasedFunctor K).obj (op (P.elementsMk U x)))
        hαβ
    change op (Q.elementsMk U (α.app U x)) = op (Q.elementsMk U (β.app U x)) at hObj
    rw [Opposite.op_inj_iff] at hObj
    have hPair := Sigma.mk.inj_iff.mp hObj
    simpa using hPair.2
  · intro H
    -- The preimage is obtained by reading `H` on distinguished element objects, and the local
    -- counit theorem identifies the resulting category-of-elements morphism with `H`.
    exact ⟨presheaf_map_preimage H, presheaf_map_preimage_of_elements_hom H⟩

/-- Helper for Lemma 4.39.6: in the source presheaf of fiberwise isomorphism classes, restricting
the class of `b` along a morphism `φ : a ⟶ b` recovers the class of `a`. -/
private theorem fiber_iso_class_map_eq
    (X : FibredInSetoidsOver C) {a b : X.S} (φ : a ⟶ b) :
    (X.p.fiberIsoClassPresheaf).map (X.p.map φ).op (Quotient.mk'' ⟨b, rfl⟩) =
      Quotient.mk'' ⟨a, rfl⟩ := by
  let hc := canonicalPullbackChoice X.p
  -- The canonical pullback of `b` along `φ` and the actual source object `a` represent the same
  -- fiberwise class because cartesian uniqueness supplies an isomorphism between them.
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber (X.p.obj a)))
        (((canonicalPullbackChoice X.p).pullbackFunctor (X.p.map φ)).obj ⟨b, rfl⟩) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber (X.p.obj a))) ⟨a, rfl⟩
  letI : X.p.IsStronglyCartesian (X.p.map φ) (hc.map (X.p.map φ) ⟨b, rfl⟩) :=
    hc.isStronglyCartesian (X.p.map φ) ⟨b, rfl⟩
  let e := Functor.IsCartesian.domainUniqueUpToIso X.p (X.p.map φ)
    (hc.map (X.p.map φ) ⟨b, rfl⟩) φ
  have hInvLift : X.p.IsHomLift (𝟙 (X.p.obj a)) e.inv := by
    change X.p.IsHomLift (𝟙 (X.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso X.p (X.p.map φ)
        (hc.map (X.p.map φ) ⟨b, rfl⟩) φ).inv)
    infer_instance
  have hHomLift : X.p.IsHomLift (𝟙 (X.p.obj a)) e.hom := by
    change X.p.IsHomLift (𝟙 (X.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso X.p (X.p.map φ)
        (hc.map (X.p.map φ) ⟨b, rfl⟩) φ).hom)
    infer_instance
  let eFiber :
      (((canonicalPullbackChoice X.p).pullbackFunctor (X.p.map φ)).obj ⟨b, rfl⟩) ≅
        ⟨a, rfl⟩ :=
    { hom := ⟨e.inv, hInvLift⟩
      inv := ⟨e.hom, hHomLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id }
  rw [Quotient.eq'']
  exact ⟨eFiber⟩

/-- Helper for Lemma 4.39.6: chosen representatives of a map on fiberwise isomorphism classes
admit canonical lifts over each source morphism. -/
private noncomputable def iso_class_representative_lift
    {X Y : FibredInSetoidsOver C}
    (α : X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf)
    (repr : ∀ a : X.S, Y.p.Fiber (X.p.obj a))
    (hrepr : ∀ a : X.S,
      Quotient.mk'' (repr a) =
        α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩))
    {a b : X.S} (φ : a ⟶ b) :
    { ψ : (repr a).1 ⟶ (repr b).1 // Y.p.IsHomLift (X.p.map φ) ψ } := by
  let hc := canonicalPullbackChoice Y.p
  let pullbackRepr :=
    ((hc.pullbackFunctor (X.p.map φ)).obj (repr b))
  have hclass :
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
          (repr a) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
          pullbackRepr := by
    -- Naturality of `α` identifies the chosen representative of `a` with the canonical pullback
    -- of the chosen representative of `b`.
    have hsource :
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
            (repr a) =
          α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩) := hrepr a
    have hsourceMap :
        α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩) =
          α.app (op (X.p.obj a))
            ((X.p.fiberIsoClassPresheaf).map (X.p.map φ).op
              (Quotient.mk'' ⟨b, rfl⟩)) := by
      rw [← fiber_iso_class_map_eq X φ]
    have hnat :
        α.app (op (X.p.obj a))
            ((X.p.fiberIsoClassPresheaf).map (X.p.map φ).op
              (Quotient.mk'' ⟨b, rfl⟩)) =
          (Y.p.fiberIsoClassPresheaf).map (X.p.map φ).op
            (@Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj b)))
              (repr b)) := by
      have hnat' :
          α.app (op (X.p.obj a))
              ((X.p.fiberIsoClassPresheaf).map (X.p.map φ).op
                (Quotient.mk'' ⟨b, rfl⟩)) =
            (Y.p.fiberIsoClassPresheaf).map (X.p.map φ).op
              (α.app (op (X.p.obj b)) (Quotient.mk'' ⟨b, rfl⟩)) := by
        simpa using
          congrFun (α.naturality (X.p.map φ).op) (Quotient.mk'' ⟨b, rfl⟩)
      rw [← hrepr b] at hnat'
      exact hnat'
    have hpullbackClass :
        (Y.p.fiberIsoClassPresheaf).map (X.p.map φ).op
            (@Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj b)))
              (repr b)) =
          @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (X.p.obj a)))
            pullbackRepr := by
      rfl
    exact hsource.trans (hsourceMap.trans (hnat.trans hpullbackClass))
  let e : repr a ≅ pullbackRepr :=
    Classical.choice (Quotient.exact hclass)
  letI : Y.p.IsHomLift (𝟙 (X.p.obj a)) e.hom.1 :=
    e.hom.2
  have hpullback :
      Y.p.IsHomLift (X.p.map φ) (hc.map (X.p.map φ) (repr b)) := by
    exact (hc.isStronglyCartesian (X.p.map φ) (repr b)).toIsHomLift
  have hlift :
      Y.p.IsHomLift (X.p.map φ) (e.hom.1 ≫ hc.map (X.p.map φ) (repr b)) := by
    -- Compute the image in the base category and then package the result as a hom lift.
    have hmapPullback :
        Y.p.map (hc.map (X.p.map φ) (repr b)) =
          eqToHom pullbackRepr.2 ≫ X.p.map φ ≫ eqToHom (repr b).2.symm := by
      simpa using IsHomLift.fac' Y.p (X.p.map φ) (hc.map (X.p.map φ) (repr b))
    have hmap :
        Y.p.map (e.hom.1 ≫ hc.map (X.p.map φ) (repr b)) =
          eqToHom (repr a).2 ≫ X.p.map φ ≫ eqToHom (repr b).2.symm := by
      calc
        Y.p.map (e.hom.1 ≫ hc.map (X.p.map φ) (repr b)) =
            Y.p.map e.hom.1 ≫ Y.p.map (hc.map (X.p.map φ) (repr b)) := by
              simp
        _ =
            (eqToHom (repr a).2 ≫ 𝟙 (X.p.obj a) ≫ eqToHom pullbackRepr.2.symm) ≫
              Y.p.map (hc.map (X.p.map φ) (repr b)) := by
              rw [IsHomLift.fac' Y.p (𝟙 (X.p.obj a)) e.hom.1]
        _ =
            (eqToHom (repr a).2 ≫ 𝟙 (X.p.obj a) ≫ eqToHom pullbackRepr.2.symm) ≫
              (eqToHom pullbackRepr.2 ≫ X.p.map φ ≫ eqToHom (repr b).2.symm) := by
              exact congrArg
                (fun t ↦
                  (eqToHom (repr a).2 ≫ 𝟙 (X.p.obj a) ≫ eqToHom pullbackRepr.2.symm) ≫ t)
                hmapPullback
        _ = eqToHom (repr a).2 ≫ X.p.map φ ≫ eqToHom (repr b).2.symm := by
              simp
    exact IsHomLift.of_fac' Y.p (X.p.map φ)
      (e.hom.1 ≫ hc.map (X.p.map φ) (repr b)) (repr a).2 (repr b).2 hmap
  -- Compose the vertical comparison with the canonical pullback map to obtain the required lift.
  exact ⟨e.hom.1 ≫ hc.map (X.p.map φ) (repr b), hlift⟩

/-- Helper for Lemma 4.39.6: after rewriting the endpoints of a lift by the chosen fiber
equalities, the corresponding subtype of lifts is still a subsingleton. -/
private theorem fibredInSetoids_hom_lift_subsingleton_transport
    (Y : FibredInSetoidsOver C) {a b : Y.S} {U V : C}
    (ha : Y.p.obj a = U) (hb : Y.p.obj b = V) (f : U ⟶ V) :
    Subsingleton { φ : a ⟶ b // Y.p.IsHomLift f φ } := by
  -- Writing the base arrow with explicit endpoint equalities does not change the thinness of the
  -- target fiber; it only matches the interface expected by `IsHomLift`.
  simpa using
    (fibredInSetoids_hom_lift_subsingleton
      (Y := Y) (a := a) (b := b) (f := eqToHom ha ≫ f ≫ eqToHom hb.symm))

/-- Helper for Lemma 4.39.6: every presheaf morphism on fiberwise isomorphism classes should be
induced by a morphism of categories fibred in setoids. The source-proof route chooses
representatives in each target fiber and then uses thinness of setoid fibers to define the action
on morphisms. -/
private theorem fibredInSetoidsToPresheaf_map_surjective
    (X Y : FibredInSetoidsOver C) :
    Function.Surjective (fun F : X ⟶ Y ↦ fibredInSetoidsToPresheaf.map F) := by
  intro α
  classical
  let repr : ∀ a : X.S, Y.p.Fiber (X.p.obj a) := fun a ↦
    Quotient.out (α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩))
  have hrepr :
      ∀ a : X.S,
        Quotient.mk'' (repr a) =
          α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩) := by
    intro a
    exact Quotient.out_eq _
  let G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
    { toFunctor :=
        { obj := fun a ↦ (repr a).1
          map := fun φ ↦ (iso_class_representative_lift α repr hrepr φ).1
          map_id := by
            intro a
            -- Both arrows are lifts over the identity in the same thin target fiber.
            let liftId := iso_class_representative_lift α repr hrepr (𝟙 a)
            letI :
                Subsingleton { ψ : (repr a).1 ⟶ (repr a).1 //
                  Y.p.IsHomLift (X.p.map (𝟙 a)) ψ } :=
              fibredInSetoids_hom_lift_subsingleton_transport
                (Y := Y) (a := (repr a).1) (b := (repr a).1)
                (ha := (repr a).2) (hb := (repr a).2) (f := X.p.map (𝟙 a))
            have hId : Y.p.IsHomLift (X.p.map (𝟙 a)) (𝟙 ((repr a).1)) := by
              refine IsHomLift.of_fac' Y.p (X.p.map (𝟙 a)) (𝟙 ((repr a).1))
                (repr a).2 (repr a).2 ?_
              simp
            exact congrArg Subtype.val <|
              Subsingleton.elim
                liftId
                ⟨𝟙 ((repr a).1), hId⟩
          map_comp := by
            intro a b c φ ψ
            -- The chosen lift of a composite is uniquely determined by its base arrow, so it
            -- agrees with the composite of the chosen lifts.
            let liftφ := iso_class_representative_lift α repr hrepr φ
            let liftψ := iso_class_representative_lift α repr hrepr ψ
            let liftComp := iso_class_representative_lift α repr hrepr (φ ≫ ψ)
            letI : Y.p.IsHomLift (X.p.map φ) liftφ.1 := liftφ.2
            letI : Y.p.IsHomLift (X.p.map ψ) liftψ.1 := liftψ.2
            letI :
                Subsingleton { χ : (repr a).1 ⟶ (repr c).1 //
                  Y.p.IsHomLift (X.p.map (φ ≫ ψ)) χ } :=
              fibredInSetoids_hom_lift_subsingleton_transport
                (Y := Y) (a := (repr a).1) (b := (repr c).1)
                (ha := (repr a).2) (hb := (repr c).2) (f := X.p.map (φ ≫ ψ))
            have hcomp :
                Y.p.IsHomLift (X.p.map (φ ≫ ψ))
                  (liftφ.1 ≫ liftψ.1) := by
              have hmap :
                  Y.p.map (liftφ.1 ≫ liftψ.1) =
                    eqToHom (repr a).2 ≫ X.p.map (φ ≫ ψ) ≫ eqToHom (repr c).2.symm := by
                calc
                  Y.p.map (liftφ.1 ≫ liftψ.1) =
                    Y.p.map liftφ.1 ≫ Y.p.map liftψ.1 := by
                        simp
                  _ =
                      (eqToHom (repr a).2 ≫ X.p.map φ ≫ eqToHom (repr b).2.symm) ≫
                        (eqToHom (repr b).2 ≫ X.p.map ψ ≫ eqToHom (repr c).2.symm) := by
                        rw [IsHomLift.fac' Y.p (X.p.map φ) liftφ.1]
                        rw [IsHomLift.fac' Y.p (X.p.map ψ) liftψ.1]
                  _ = eqToHom (repr a).2 ≫ X.p.map (φ ≫ ψ) ≫ eqToHom (repr c).2.symm := by
                        simp [Category.assoc]
              exact IsHomLift.of_fac' Y.p (X.p.map (φ ≫ ψ))
                (liftφ.1 ≫ liftψ.1)
                (repr a).2 (repr c).2 hmap
            exact congrArg Subtype.val <|
              Subsingleton.elim
                liftComp
                ⟨_, hcomp⟩ }
      w := by
        -- The representative lift was constructed precisely so that every chosen morphism lies over
        -- the original base arrow in `X`.
        refine Functor.ext ?_ ?_
        · intro a
          simpa using (repr a).2
        · intro a b φ
          let liftφ := iso_class_representative_lift α repr hrepr φ
          letI : Y.p.IsHomLift (X.p.map φ) liftφ.1 := liftφ.2
          simpa using
            IsHomLift.fac' Y.p (X.p.map φ) liftφ.1 }
  let F : X ⟶ Y := FibredInSetoidsOver.ofBasedFunctor G
  refine ⟨F, ?_⟩
  ext U q
  cases U
  rename_i U
  refine Quotient.inductionOn q ?_
  intro x
  -- Reduce an arbitrary fiber representative to the canonical form `⟨a, rfl⟩`.
  cases x with
  | mk a ha =>
      cases ha
      -- On the normalized representative, the induced presheaf map returns the chosen object
      -- `repr a`, whose quotient class was defined to be `α` applied to `[a]`.
      change Quotient.mk'' (((FibredInGroupoidsMor.fiberFunctor F.toHom (X.p.obj a)).obj ⟨a, rfl⟩)) =
        α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩)
      change Quotient.mk'' (repr a) =
        α.app (op (X.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩)
      exact hrepr a

-- Proof sketch: combine the quotient-level presheaf statement below with the equivalence of
-- Lemma 4.38.6 between presheaves and categories fibred in sets.
/-- Every morphism between the associated categories fibred in sets comes from a `1`-morphism of
categories fibred in setoids. -/
theorem fibredInSetoidsToFibredInSets_map_surjective
    (X Y : FibredInSetoidsOver C) :
    Function.Surjective
      (fun F : X ⟶ Y ↦ fibredInSetoidsToFibredInSets.map F) := by
  intro H
  -- Transport `H` back to the presheaf side, then use the explicit setoid-side lift of that
  -- presheaf morphism.
  have hbij :=
    presheafToFibredInSetsOverLocal_hom_bijective
      (X.p.fiberIsoClassPresheaf) (Y.p.fiberIsoClassPresheaf)
  rcases hbij.2 H with ⟨α, hα⟩
  rcases fibredInSetoidsToPresheaf_map_surjective X Y α with ⟨F, hF⟩
  refine ⟨F, ?_⟩
  change
    presheafToFibredInSetsOverLocal.map (fibredInSetoidsToPresheaf.map F) = H
  exact (congrArg (Functor.map presheafToFibredInSetsOverLocal) hF).trans hα

-- Proof sketch: a `2`-isomorphism between `F` and `G` is a vertical natural isomorphism whose
-- components lie in setoid fibers of `Y`; each component therefore identifies the images of every
-- source object in the quotient by isomorphism classes, so the induced morphisms in
-- `FibredInSetsOver C` agree.
/-- A `2`-isomorphism between morphisms of categories fibred in setoids induces equality after
applying `fibredInSetoidsToFibredInSets`. -/
theorem fibredInSetoidsToFibredInSets_map_eq_of_isomorphic
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y} (τ : F ≅ G) :
    fibredInSetoidsToFibredInSets.map F =
      fibredInSetoidsToFibredInSets.map G := by
  -- The fibred-in-sets comparison is obtained by applying the category-of-elements functor to
  -- the presheaf-side comparison, so equality follows from the presheaf-level equality helper.
  have hPresheaf :
      fibredInSetoidsToPresheaf.map F =
        fibredInSetoidsToPresheaf.map G := by
    let τAmbient : F.toHom ≅ G.toHom :=
      Functor.mapIso (((fibredInSetoidsOverSubTwoCategory C).hom X Y).inclusion) τ
    let τBased := FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso τAmbient
    ext U q
    refine Quotient.inductionOn q ?_
    intro x
    -- Fiberwise, the component of the induced based-functor isomorphism is a vertical morphism,
    -- hence it identifies the two quotient classes.
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (unop U)))
        ((FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (unop U)))
        ((FibredInGroupoidsMor.fiberFunctor G (unop U)).obj x)
    let xF : Y.p.Fiber (unop U) := (FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x
    let xG : Y.p.Fiber (unop U) := (FibredInGroupoidsMor.fiberFunctor G (unop U)).obj x
    have hτlift : Functor.IsHomLift Y.p (𝟙 (unop U)) (τBased.hom.app x.1) := by
      exact BasedNatTrans.isHomLift τBased.hom (by simp [x.2])
    let m : xF ⟶ xG := by
      exact ⟨τBased.hom.app x.1, hτlift⟩
    rw [Quotient.eq'']
    simpa [xF, xG] using ⟨asIso m⟩
  change
    presheafToFibredInSetsOverLocal.map (fibredInSetoidsToPresheaf.map F) =
      presheafToFibredInSetsOverLocal.map (fibredInSetoidsToPresheaf.map G)
  exact congrArg (Functor.map presheafToFibredInSetsOverLocal)
    hPresheaf

-- Proof sketch: pass to the quotient of `X ⟶ Y` by `2`-isomorphism and use the previous theorem
-- to show that the induced target morphism depends only on the isomorphism class.
/-- The canonical map sending a `2`-isomorphism class of `1`-morphisms of categories fibred in
setoids over `C` to the induced morphism between their associated categories fibred in sets. -/
noncomputable def fibredInSetoidsHomIsoClassesToFibredInSetsHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) →
      (fibredInSetoidsToFibredInSets.obj X ⟶ fibredInSetoidsToFibredInSets.obj Y) :=
  fun q ↦
    Quotient.liftOn q
      (fun F : X ⟶ Y ↦ fibredInSetoidsToFibredInSets.map F)
      (fun _ _ hFG ↦ by
        rcases hFG with ⟨τ⟩
        exact fibredInSetoidsToFibredInSets_map_eq_of_isomorphic τ)

-- Proof sketch: surjectivity is exactly Lemma 4.39.6 (2). For injectivity, if two classes map to
-- the same target morphism, Lemma 4.39.6 (1) gives a `2`-isomorphism between chosen
-- representatives, and `fibredInSetoidsOverTwoIso_subsingleton` supplies its uniqueness, so the
-- quotient classes coincide.
/-- Lemma 4.39.6 (2): on each hom-category, passing to `2`-isomorphism classes identifies `1`-morphisms of
categories fibred in setoids with morphisms between their images under
`fibredInSetoidsToFibredInSets`. -/
theorem fibredInSetoidsHomIsoClassesToFibredInSetsHom_bijective
    (X Y : FibredInSetoidsOver C) :
    Function.Bijective (fibredInSetoidsHomIsoClassesToFibredInSetsHom X Y) := by
  constructor
  · intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro F G
    change fibredInSetoidsHomIsoClassesToFibredInSetsHom X Y (Quotient.mk'' F) =
        fibredInSetoidsHomIsoClassesToFibredInSetsHom X Y (Quotient.mk'' G) →
      Quotient.mk'' F = Quotient.mk'' G
    intro hFG
    change fibredInSetoidsToFibredInSets.map F =
        fibredInSetoidsToFibredInSets.map G at hFG
    apply Quot.sound
    exact ⟨Classical.choice
      (fibredInSetoidsToFibredInSets_nonempty_iso_of_map_eq
        (X := X) (Y := Y) (F := F) (G := G) hFG)⟩
  · intro H
    rcases fibredInSetoidsToFibredInSets_map_surjective X Y H with ⟨F, hF⟩
    refine ⟨Quotient.mk'' F, ?_⟩
    simpa [fibredInSetoidsHomIsoClassesToFibredInSetsHom] using hF

-- Proof sketch: if `X` is already fibred in sets, then its fibers are discrete, so the presheaf
-- of isomorphism classes is canonically identified with the presheaf of objects in the fibers.
-- Lemma 4.38.6 then shows that this canonical comparison exhibits `X` as lying in the image of
-- `fibredInSetoidsToFibredInSets`, and in particular as an equivalence over `C`.
/-- Lemma 4.39.6 (3): if `X` is already fibred in sets, then the canonical comparison from `X`,
viewed as a fibred-in-setoids object, to its image under `fibredInSetoidsToFibredInSets` is an
equivalence over the base. -/
theorem fibredInSetoidsToFibredInSets_obj_isEquivalenceOverBase_of_fibredInSets
    (X : FibredInSetsOver C) :
    FibredInSetoidsOver.IsEquivalenceOverBase
      (FibredInSetoidsOver.toFibredInSets (X : FibredInSetoidsOver C)) := by
  -- The object part of `fibredInSetoidsToFibredInSets` is exactly the associated fibred-in-sets
  -- object from Lemma 4.39.5, so the comparison equivalence is the canonical one proved there.
  simpa [fibredInSetoidsToFibredInSets, fibredInSetoidsToPresheaf,
    presheafToFibredInSetsOverLocal] using
    FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase (X : FibredInSetoidsOver C)

-- Proof sketch: a `2`-isomorphism between `F` and `G` is a vertical natural isomorphism whose
-- components lie in setoid fibers of `Y`; each component therefore identifies the images of every
-- source object in the quotient by isomorphism classes, so the induced presheaf maps are equal.
private theorem fibredInSetoidsToPresheaf_map_eq_of_isomorphic
    {X Y : FibredInSetoidsOver C} {F G : X ⟶ Y} (τ : F ≅ G) :
    fibredInSetoidsToPresheaf.map F =
      fibredInSetoidsToPresheaf.map G := by
  let τAmbient : F.toHom ≅ G.toHom :=
    Functor.mapIso (((fibredInSetoidsOverSubTwoCategory C).hom X Y).inclusion) τ
  let τBased := FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso τAmbient
  ext U q
  refine Quotient.inductionOn q ?_
  intro x
  -- The component of the induced based-functor isomorphism is vertical in the target fiber, so
  -- it identifies the two images in the quotient by fiberwise isomorphism classes.
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (unop U)))
      ((FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x) =
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber (unop U)))
      ((FibredInGroupoidsMor.fiberFunctor G (unop U)).obj x)
  let xF : Y.p.Fiber (unop U) := (FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x
  let xG : Y.p.Fiber (unop U) := (FibredInGroupoidsMor.fiberFunctor G (unop U)).obj x
  have hτlift : Functor.IsHomLift Y.p (𝟙 (unop U)) (τBased.hom.app x.1) := by
    exact BasedNatTrans.isHomLift τBased.hom (by simp [x.2])
  let m : xF ⟶ xG := by
    exact ⟨τBased.hom.app x.1, hτlift⟩
  rw [Quotient.eq'']
  simpa [xF, xG] using ⟨asIso m⟩

-- Proof sketch: an element of `isomorphismClasses.obj (Cat.of (X ⟶ Y))` is a
-- quotient by the relation of admitting a natural isomorphism; the previous theorem shows the map
-- to presheaf morphisms is constant on each equivalence class.
theorem fibredInSetoidsToPresheaf_map_respects_isomorphismClasses
    (X Y : FibredInSetoidsOver C)
    {F G : X ⟶ Y}
    (hFG : CategoryTheory.IsIsomorphic F G) :
    fibredInSetoidsToPresheaf.map F =
      fibredInSetoidsToPresheaf.map G := by
  -- The quotient relation is generated by actual `2`-isomorphisms, and those already force
  -- equality of the induced presheaf maps.
  rcases hFG with ⟨τ⟩
  exact fibredInSetoidsToPresheaf_map_eq_of_isomorphic τ

-- Proof sketch: an element of `isomorphismClasses.obj (Cat.of (X ⟶ Y))` is a
-- quotient by the relation of admitting a natural isomorphism; the theorem above on unique
-- `2`-isomorphisms shows that the induced presheaf map depends only on the isomorphism class.
/-- The canonical map sending a `2`-isomorphism class of `1`-morphisms of categories fibred in
setoids over `C` to the induced morphism of presheaves of isomorphism classes. -/
noncomputable def fibredInSetoidsHomIsoClassesToPresheafHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) →
      (X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf) :=
  fun q ↦
    Quotient.liftOn q
      (fun F : X ⟶ Y ↦ fibredInSetoidsToPresheaf.map F)
      (fun _ _ hFG ↦
        fibredInSetoidsToPresheaf_map_respects_isomorphismClasses X Y hFG)

-- Proof sketch: the induced map to presheaf morphisms is well defined on `2`-isomorphism classes
-- by the previous helper. Fullness is the existence statement from the quotient construction of
-- Lemma 4.39.5, while faithfulness reduces equal induced presheaf maps to a unique vertical
-- natural isomorphism between the corresponding based functors because every fiber of the target
-- is a setoid.
/-- On each hom-category, the canonical map from `2`-isomorphism classes of `1`-morphisms to
morphisms of the associated presheaves of isomorphism classes is bijective. -/
theorem fibredInSetoidsHomIsoClassesToPresheafHom_bijective
    (X Y : FibredInSetoidsOver C) :
    Function.Bijective (fibredInSetoidsHomIsoClassesToPresheafHom X Y) := by
  constructor
  · intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro F G
    change fibredInSetoidsToPresheaf.map F =
        fibredInSetoidsToPresheaf.map G →
      Quotient.mk'' F = Quotient.mk'' G
    intro hFG
    apply Quot.sound
    have hAssoc :
        fibredInSetoidsToFibredInSets.map F =
          fibredInSetoidsToFibredInSets.map G := by
      change
        presheafToFibredInSetsOverLocal.map (fibredInSetoidsToPresheaf.map F) =
          presheafToFibredInSetsOverLocal.map (fibredInSetoidsToPresheaf.map G)
      exact congrArg (Functor.map presheafToFibredInSetsOverLocal) hFG
    exact ⟨Classical.choice
      (fibredInSetoidsToFibredInSets_nonempty_iso_of_map_eq
        (X := X) (Y := Y) (F := F) (G := G) hAssoc)⟩
  · intro α
    rcases fibredInSetoidsToPresheaf_map_surjective X Y α with ⟨F, hF⟩
    refine ⟨Quotient.mk'' F, ?_⟩
    simpa [fibredInSetoidsHomIsoClassesToPresheafHom] using hF

namespace FibredInSetoidsOver

/-- On each hom-category, passing to `2`-isomorphism classes identifies
`1`-morphisms of categories fibred in setoids with morphisms between their associated categories
fibred in sets. -/
noncomputable def hom_isoClasses_equiv_fibredInSetsHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) ≃
      (fibredInSetoidsToFibredInSets.obj X ⟶ fibredInSetoidsToFibredInSets.obj Y) :=
  Equiv.ofBijective
    (fibredInSetoidsHomIsoClassesToFibredInSetsHom X Y)
    (fibredInSetoidsHomIsoClassesToFibredInSetsHom_bijective X Y)

/-- Passing to `2`-isomorphism classes of `1`-morphisms identifies
them canonically with morphisms of the associated presheaves of isomorphism classes. -/
noncomputable def hom_isoClasses_equiv_presheafHom
    (X Y : FibredInSetoidsOver C) :
    isomorphismClasses.obj (Cat.of (X ⟶ Y)) ≃
      (X.p.fiberIsoClassPresheaf ⟶ Y.p.fiberIsoClassPresheaf) :=
  Equiv.ofBijective
    (fibredInSetoidsHomIsoClassesToPresheafHom X Y)
    (fibredInSetoidsHomIsoClassesToPresheafHom_bijective X Y)

end FibredInSetoidsOver

end CategoryTheory
