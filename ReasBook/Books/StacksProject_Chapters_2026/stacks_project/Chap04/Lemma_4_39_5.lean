module

public import stacks_project.Chap04.Definition_4_32_1
public import stacks_project.Chap04.Definition_4_38_3
public import stacks_project.Chap04.Definition_4_39_3
public import stacks_project.Chap04.Example_4_38_5
public import stacks_project.Chap04.Lemma_4_33_7
public import stacks_project.Chap04.Lemma_4_35_2
public import stacks_project.Chap04.Lemma_4_35_9
public import stacks_project.Chap04.Definition_4_39_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite
open BasedFunctor
open CategoryOfElements

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- The restriction map on isomorphism classes induced by the canonical pullback functor. -/
noncomputable def fiberIsoClassPresheafMap
    (p : S ⥤ C) [p.IsFibered] {U V : Cᵒᵖ} (f : U ⟶ V) :
    isomorphismClasses.obj (Cat.of (p.Fiber (unop U))) →
      isomorphismClasses.obj (Cat.of (p.Fiber (unop V))) :=
  isomorphismClasses.map ((canonicalPullbackChoice p).pullbackFunctor f.unop).toCatHom

/-- Pullback along an identity morphism acts trivially on isomorphism classes in the fibers. -/
theorem fiberIsoClassPresheafMap_id
    (p : S ⥤ C) [p.IsFibered] (U : Cᵒᵖ) :
    fiberIsoClassPresheafMap p (𝟙 U) = id := by
  -- Compare the chosen identity pullback object with the original fiber object via the
  -- canonical pullback-identity isomorphism, then pass to isomorphism classes.
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop U)))
        (((canonicalPullbackChoice p).pullbackFunctor (𝟙 (unop U))).obj x) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop U))) x
  rw [Quotient.eq'']
  exact ⟨((canonicalPullbackChoice p).pullbackIdIso (unop U)).symm.app x⟩

/-- Pullback on isomorphism classes is contravariantly functorial in the base morphism. -/
theorem fiberIsoClassPresheafMap_comp
    (p : S ⥤ C) [p.IsFibered] {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    fiberIsoClassPresheafMap p (f ≫ g) =
      fiberIsoClassPresheafMap p g ∘
        fiberIsoClassPresheafMap p f := by
  -- Compare the chosen pullback of the composite with the iterated chosen pullback using the
  -- canonical composition isomorphism, then quotient by isomorphism.
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop W)))
        (((canonicalPullbackChoice p).pullbackFunctor (g.unop ≫ f.unop)).obj x) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop W)))
        ((((canonicalPullbackChoice p).pullbackFunctor f.unop ⋙
          (canonicalPullbackChoice p).pullbackFunctor g.unop).obj x))
  rw [Quotient.eq'']
  exact ⟨((canonicalPullbackChoice p).pullbackCompIso f.unop g.unop).app x⟩

/-- The presheaf sending `U` to the set of isomorphism classes of objects in the fiber `p⁻¹(U)`.
-/
noncomputable def fiberIsoClassPresheaf
    (p : S ⥤ C) [p.IsFibered] : Presheaf.{u₂} C where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber (unop U)))
  map f := fiberIsoClassPresheafMap p f
  map_id := fiberIsoClassPresheafMap_id p
  map_comp := fiberIsoClassPresheafMap_comp p

end Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {X : BasedCategory C}

/- Domain-style sampling for Lemma 4.39.5:
- primary domain: categories over a fixed base, compared by based equivalences and by the induced
  maps on isomorphism classes in each fiber;
- sampled owner-level declarations:
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.fiberFunctor`,
  `IsFibredInSetoids`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `Functor.fiberIsoClassPresheaf`,
  `presheafToFibredInSetsOver`,
  `FibredInSetoidsOver.ofAmbientHom`;
- best owner abstraction: the based functor over `C` for the fiberwise clauses, and the canonical
  associated fibred-in-sets object `FibredInSetoidsOver.associatedFibredInSets` for the
  replacement-by-sets clause; the comparison morphism should expose only the owner hom, with its
  underlying based functor kept as internal bridge data;
- primitive data: bundled categories over `C` and, for the replacement-by-sets clause, the
  underlying based functor from `Z` to the category of elements of `Z.p.fiberIsoClassPresheaf`;
- derived API: the transported setoid condition, the induced bijection on isomorphism classes in
  each fiber, and the canonical comparison with the associated fibred-in-sets model.

Source/core/bridge triage:
- `source-facing`: the first two clauses of the lemma together with the canonical replacement by
  an associated fibred-in-sets object;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `BasedFunctor.fiberFunctor`,
  `IsFibredInSetoids`, `Functor.fiberIsoClassPresheaf`, and
  `FibredInSetoidsOver.associatedFibredInSets Z`;
- `bridge/view`: the internal based functor to the category of elements of
  `Z.p.fiberIsoClassPresheaf`, and the induced owner morphism `Z.toFibredInSets`. -/

namespace BasedFunctor

section

/-- In a discrete category, taking isomorphism classes is canonically equivalent to taking
objects. -/
noncomputable def isoClassesEquivOfIsDiscrete
    (D : Type u₂) [Category.{v₂} D] [IsDiscrete D] :
    isomorphismClasses.obj (Cat.of D) ≃ D :=
  (Equiv.ofBijective
      (fun x : D ↦ Quotient.mk'' x)
      (by
        constructor
        · intro x y hxy
          exact Quotient.exact hxy |>.elim fun i ↦ obj_ext_of_isDiscrete i.hom
        · intro q
          refine Quotient.inductionOn q ?_
          intro x
          exact ⟨x, rfl⟩)).symm

/-- An equivalence over the base induces a bijection on isomorphism classes in each fiber. -/
theorem fiberIsoClassMap_bijective_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) (U : C) :
    Function.Bijective (isomorphismClasses.map (F.fiberFunctor U).toCatHom) := by
  letI : (F.fiberFunctor U).IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
  let e := (F.fiberFunctor U).asEquivalence
  have hleft :
      Function.LeftInverse
        (isomorphismClasses.map e.inverse.toCatHom)
        (isomorphismClasses.map (F.fiberFunctor U).toCatHom) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber U))
          (e.inverse.obj ((F.fiberFunctor U).obj x)) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber U)) x
    rw [Quotient.eq'']
    exact ⟨e.unitIso.symm.app x⟩
  constructor
  · intro q₁ q₂ hq
    -- Cancel the forward map on the left by applying the inverse equivalence on classes.
    exact hleft.injective hq
  · intro q
    -- Represent any target isomorphism class by an actual fiber object and then pull it back
    -- along the quasi-inverse.
    refine Quotient.inductionOn q ?_
    intro y
    refine ⟨Quotient.mk'' (e.inverse.obj y), ?_⟩
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
          ((F.fiberFunctor U).obj (e.inverse.obj y)) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U)) y
    rw [Quotient.eq'']
    exact ⟨e.counitIso.app y⟩

/-- If the target is fibred in sets, then its fiber over `U` is canonically identified with the
set of isomorphism classes in the source fiber over `U`. -/
noncomputable def fiberIsoClassesEquivFiber_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    [IsFibredInSets Y.p] (U : C) :
    isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U :=
  (Equiv.ofBijective
      (isomorphismClasses.map (F.fiberFunctor U).toCatHom)
      (fiberIsoClassMap_bijective_of_isEquivalenceOverBase F hF U)).trans
    (isoClassesEquivOfIsDiscrete (Y.p.Fiber U))

end

end BasedFunctor

namespace FibredInSetoidsOver

/-- Lemma 4.39.5: the category fibred in sets associated to `Z`, obtained from the category of
elements of the presheaf of fiberwise isomorphism classes. -/
noncomputable def associatedFibredInSets
    (Z : FibredInSetoidsOver C) :
    FibredInSetsOver C :=
  FibredInSetsOver.ofFunctor ((CategoryOfElements.π Z.p.fiberIsoClassPresheaf).leftOp)

noncomputable def fiberIsoClassElement
    (Z : FibredInSetoidsOver C) :
    Z.S → (Z.p.fiberIsoClassPresheaf).Elements :=
  fun a ↦
    (Z.p.fiberIsoClassPresheaf).elementsMk (op (Z.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩)

/-- Helper for Lemma 4.39.5: pulling back the isomorphism class of `b` along the base map of
`φ : a ⟶ b` recovers the isomorphism class of `a`. -/
private theorem fiberIsoClassElement_map_eq
    (Z : FibredInSetoidsOver C) {a b : Z.S} (φ : a ⟶ b) :
    (Z.p.fiberIsoClassPresheaf).map (Z.p.map φ).op (Quotient.mk'' ⟨b, rfl⟩) =
      Quotient.mk'' ⟨a, rfl⟩ := by
  -- Compare `φ` with the chosen pullback map of `b` along the same base arrow; cartesian
  -- uniqueness gives an isomorphism between their domains, hence equality of classes.
  let hc := canonicalPullbackChoice Z.p
  letI : Z.p.IsStronglyCartesian (Z.p.map φ) (hc.map (Z.p.map φ) ⟨b, rfl⟩) :=
    hc.isStronglyCartesian (Z.p.map φ) ⟨b, rfl⟩
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber (Z.p.obj a)))
        (((canonicalPullbackChoice Z.p).pullbackFunctor (Z.p.map φ)).obj ⟨b, rfl⟩) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber (Z.p.obj a))) ⟨a, rfl⟩
  let e := Functor.IsCartesian.domainUniqueUpToIso Z.p (Z.p.map φ)
    (hc.map (Z.p.map φ) ⟨b, rfl⟩) φ
  have hInvLift : Z.p.IsHomLift (𝟙 (Z.p.obj a)) e.inv := by
    change Z.p.IsHomLift (𝟙 (Z.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso Z.p (Z.p.map φ)
        (hc.map (Z.p.map φ) ⟨b, rfl⟩) φ).inv)
    infer_instance
  have hHomLift : Z.p.IsHomLift (𝟙 (Z.p.obj a)) e.hom := by
    change Z.p.IsHomLift (𝟙 (Z.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso Z.p (Z.p.map φ)
        (hc.map (Z.p.map φ) ⟨b, rfl⟩) φ).hom)
    infer_instance
  let eFiber :
      (((canonicalPullbackChoice Z.p).pullbackFunctor (Z.p.map φ)).obj ⟨b, rfl⟩) ≅
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

noncomputable def toFibredInSetsBasedFunctor
    (Z : FibredInSetoidsOver C) :
    Z.toBasedCategory ⥤ᵇ Z.associatedFibredInSets.toBasedCategory :=
  { toFunctor :=
      { obj := fun a ↦ op (fiberIsoClassElement Z a)
        map := fun {a b} φ ↦
          Quiver.Hom.op <|
            homMk
              (fiberIsoClassElement Z b)
              (fiberIsoClassElement Z a)
              (Z.p.map φ).op
              (by
                -- The category-of-elements morphism is well defined precisely because the source
                -- morphism transports the class of `b` to the class of `a`.
                simpa using fiberIsoClassElement_map_eq Z φ)
        map_id := by
          intro a
          apply Quiver.Hom.unop_inj
          apply ext (Z.p.fiberIsoClassPresheaf)
          change (Z.p.map (𝟙 a)).op = 𝟙 (op (Z.p.obj a))
          simp
        map_comp := by
          intro a b c φ ψ
          apply Quiver.Hom.unop_inj
          apply ext (Z.p.fiberIsoClassPresheaf)
          change (Z.p.map (φ ≫ ψ)).op = (Z.p.map ψ).op ≫ (Z.p.map φ).op
          simp }
    w := rfl }

/-- The canonical comparison from a category fibred in setoids over `C` to the associated
category fibred in sets `Z.associatedFibredInSets`, given by the category of elements of the
owner presheaf `Z.p.fiberIsoClassPresheaf`. -/
noncomputable abbrev toFibredInSets
    (Z : FibredInSetoidsOver C) :
    Z ⟶ Z.associatedFibredInSets :=
  ofBasedFunctor (toFibredInSetsBasedFunctor Z)

/-- Helper for Lemma 4.39.5: the canonical comparison viewed in the ambient
`FibredInGroupoidsOver` owner. -/
private noncomputable abbrev toFibredInSets_ambientHom
    (Z : FibredInSetoidsOver C) :
    Z.toFibredInGroupoidsOver ⟶ Z.associatedFibredInSets.toFibredInGroupoidsOver :=
  FibredInGroupoidsMor.ofBasedFunctor (toFibredInSetsBasedFunctor Z)

/-- Helper for Lemma 4.39.5: the functor induced on the fiber over `U` by the canonical
comparison `Z.toFibredInSets`. -/
private noncomputable abbrev toFibredInSets_fiberFunctor
    (Z : FibredInSetoidsOver C) (U : C) :=
  (toFibredInSetsBasedFunctor Z).fiberFunctor U

/-- Helper for Lemma 4.39.5: the ambient owner fiber functor of the canonical comparison agrees
definitionally with the local fiber functor used in the quotient-by-isomorphism-classes proof. -/
private theorem toFibredInSets_fiberFunctor_defeq
    (Z : FibredInSetoidsOver C) (U : C) :
    _root_.CategoryTheory.FibredInGroupoidsMor.fiberFunctor
        (toFibredInSets_ambientHom Z) U =
      toFibredInSets_fiberFunctor Z U :=
  rfl

/-- Helper for Lemma 4.39.5: the fiber of the associated fibred-in-sets object over `U` is
identified with the set of isomorphism classes in the source fiber over `U`. -/
private noncomputable def associated_fiber_equiv_iso_classes
    (Z : FibredInSetoidsOver C) (U : C) :
    Z.associatedFibredInSets.p.Fiber U ≃ isomorphismClasses.obj (Cat.of (Z.p.Fiber U)) where
  toFun y := by
    rcases y with ⟨y, hy⟩
    cases h : y.unop with
    | mk U' q =>
        have hyobj : y = op ⟨U', q⟩ := by
          apply Opposite.unop_injective
          simp [h]
        subst y
        have hy' : unop U' = U := by
          simpa [FibredInSetoidsOver.associatedFibredInSets, FibredInSetsOver.ofFunctor,
            FibredInSetsOver.p, FibredInGroupoidsOver.ofFunctor, FibredInGroupoidsOver.p,
            FibredCategoryOver.ofFunctor, FibredCategoryOver.p] using hy
        cases hy'
        simpa using q
  invFun q := ⟨op ((Z.p.fiberIsoClassPresheaf).elementsMk (op U) q), rfl⟩
  left_inv := by
    intro y
    rcases y with ⟨y, hy⟩
    cases h : y.unop with
    | mk U' q =>
        have hyobj : y = op ⟨U', q⟩ := by
          apply Opposite.unop_injective
          simp [h]
        subst y
        have hy' : unop U' = U := by
          simpa [FibredInSetoidsOver.associatedFibredInSets, FibredInSetsOver.ofFunctor,
            FibredInSetsOver.p, FibredInGroupoidsOver.ofFunctor, FibredInGroupoidsOver.p,
            FibredCategoryOver.ofFunctor, FibredCategoryOver.p] using hy
        cases hy'
        rfl
  right_inv := by
    intro q
    rfl

/-- Helper for Lemma 4.39.5: every quotient class is sent back by the inverse equivalence to the
corresponding image object in the associated fiber. -/
private theorem associated_fiber_equiv_iso_classes_symm_obj
    (Z : FibredInSetoidsOver C) (U : C) (x : Z.p.Fiber U) :
    (associated_fiber_equiv_iso_classes Z U).symm (Quotient.mk'' x) =
      (toFibredInSets_fiberFunctor Z U).obj x := by
  rcases x with ⟨x, hx⟩
  cases hx
  rfl

/-- Helper for Lemma 4.39.5: the above fiber equivalence sends the image of a source fiber object
to its isomorphism class. -/
private theorem associated_fiber_equiv_iso_classes_apply_obj
    (Z : FibredInSetoidsOver C) (U : C) (x : Z.p.Fiber U) :
    associated_fiber_equiv_iso_classes Z U ((toFibredInSets_fiberFunctor Z U).obj x) =
      Quotient.mk'' x := by
  have h :=
    congrArg (associated_fiber_equiv_iso_classes Z U)
      (associated_fiber_equiv_iso_classes_symm_obj Z U x)
  simpa using h.symm

/-- Helper for Lemma 4.39.5: every object of the target fiber is represented by the image of some
object of the source fiber. -/
private theorem toFibredInSets_fiberFunctor_obj_preimage
    (Z : FibredInSetoidsOver C) (U : C) (y : Z.associatedFibredInSets.p.Fiber U) :
    ∃ x : Z.p.Fiber U, Nonempty ((toFibredInSets_fiberFunctor Z U).obj x ≅ y) := by
  let e := associated_fiber_equiv_iso_classes Z U
  have hpre :
      ∀ q : isomorphismClasses.obj (Cat.of (Z.p.Fiber U)),
        ∃ x : Z.p.Fiber U, Nonempty ((toFibredInSets_fiberFunctor Z U).obj x ≅ e.symm q) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    refine ⟨x, ?_⟩
    -- A chosen representative lands exactly on the inverse image of its class.
    exact ⟨eqToIso (associated_fiber_equiv_iso_classes_symm_obj Z U x).symm⟩
  simpa using hpre (e y)

/-- Helper for Lemma 4.39.5: if two source-fiber objects have the same image in the associated
fiber, then they define the same isomorphism class in the source fiber. -/
private theorem fiberIsoClass_eq_of_toFibredInSets_obj_eq
    (Z : FibredInSetoidsOver C) (U : C) {x y : Z.p.Fiber U}
    (hxy :
      (toFibredInSets_fiberFunctor Z U).obj x =
        (toFibredInSets_fiberFunctor Z U).obj y) :
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) x =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) y := by
  -- Compare the two equal target objects through the explicit quotient description of the target
  -- fiber, which turns object equality into equality of source isomorphism classes.
  have heq :
      (associated_fiber_equiv_iso_classes Z U)
          ((toFibredInSets_fiberFunctor Z U).obj x) =
        (associated_fiber_equiv_iso_classes Z U)
          ((toFibredInSets_fiberFunctor Z U).obj y) := by
    exact congrArg (fun z ↦ associated_fiber_equiv_iso_classes Z U z) hxy
  exact
    (associated_fiber_equiv_iso_classes_apply_obj Z U x).symm.trans
      (heq.trans (associated_fiber_equiv_iso_classes_apply_obj Z U y))

/-- Helper for Lemma 4.39.5: on each fiber, the canonical comparison is an equivalence between
the thin source groupoid and the discrete quotient by isomorphism classes. -/
private theorem toFibredInSets_fiberFunctor_isEquivalence
    (Z : FibredInSetoidsOver C) (U : C) :
    (toFibredInSets_fiberFunctor Z U).IsEquivalence := by
  let F := toFibredInSets_fiberFunctor Z U
  letI : F.Faithful := by
    refine ⟨?_⟩
    intro x y φ ψ hφψ
    -- The source fiber is thin, so there is at most one morphism to compare.
    exact Subsingleton.elim φ ψ
  letI : F.Full := by
    refine ⟨?_⟩
    intro x y φ
    -- Discreteness of the target fiber turns the target morphism into equality of image objects.
    have hobj : F.obj x = F.obj y := obj_ext_of_isDiscrete φ
    have hclass :
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) x =
          @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) y :=
      fiberIsoClass_eq_of_toFibredInSets_obj_eq Z U hobj
    rcases Quotient.exact hclass with ⟨i⟩
    refine ⟨i.hom, ?_⟩
    -- The target fiber is also thin, so the lifted morphism is forced to equal `φ`.
    exact Subsingleton.elim _ _
  -- Chosen representatives for quotient classes give objectwise preimages in the target fiber.
  exact
    Functor.fully_faithful_isEquivalence_of_objwise_iso (F := F)
      (fun y ↦ Classical.choose (toFibredInSets_fiberFunctor_obj_preimage Z U y))
      (fun y ↦
        (Classical.choice
          (Classical.choose_spec (toFibredInSets_fiberFunctor_obj_preimage Z U y))).symm)

/-- The canonical comparison from a category fibred in setoids over `C` to its associated
category fibred in sets is an equivalence over the base. -/
-- Route correction: instead of trying to transport fibred-in-setoids structure abstractly across
-- an arbitrary equivalence over the base, we follow the source proof and identify each target
-- fiber with isomorphism classes in the source fiber, then prove the canonical comparison is a
-- fiberwise equivalence.
-- Proof sketch: identify the target with the category of elements of the presheaf of fiberwise
-- isomorphism classes and apply the fiberwise equivalence criterion from the first part of the
-- lemma to the canonical comparison functor `Z.toFibredInSets`.
theorem toFibredInSets_isEquivalenceOverBase
    (Z : FibredInSetoidsOver C) :
    IsEquivalenceOverBase (Z.toFibredInSets) :=
  by
    let F : Z.toFibredInGroupoidsOver ⟶ Z.associatedFibredInSets.toFibredInGroupoidsOver :=
      toFibredInSets_ambientHom Z
    have hFiber :
        ∀ U : C, (_root_.CategoryTheory.FibredInGroupoidsMor.fiberFunctor F U).IsEquivalence := by
      intro U
      -- Rewrite the owner-level fiber functor to the local canonical one and apply the fiberwise
      -- equivalence already proved above.
      simpa [F, toFibredInSets_fiberFunctor_defeq] using
        toFibredInSets_fiberFunctor_isEquivalence Z U
    have hEq : (FibredInGroupoidsMor.G F).IsEquivalence := by
      -- Apply the owner-level fiberwise criterion after proving each fiber functor is an equivalence.
      exact (_root_.CategoryTheory.FibredInGroupoidsMor.isEquivalence_iff_fiberwise (F := F)).2
        hFiber
    -- Upgrade the ambient equivalence to an equivalence over the base category.
    simpa [FibredInSetoidsOver.IsEquivalenceOverBase] using
      _root_.CategoryTheory.FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence (F := F) hEq

end FibredInSetoidsOver

end CategoryTheory
