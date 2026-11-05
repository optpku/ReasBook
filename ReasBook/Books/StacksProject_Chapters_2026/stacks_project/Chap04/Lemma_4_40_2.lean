module

public import Mathlib.CategoryTheory.RepresentedBy
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Example_4_38_7
public import stacks_project.Chap04.Lemma_4_39_5
public import stacks_project.Chap04.Lemma_4_40_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Functor BasedFunctor
open CategoryOfElements
open Opposite
open scoped RepresentablePresheaf
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsOver

/- Domain-style sampling for Lemma 4.40.2:
- primary domain: representable categories fibred in groupoids over a fixed base and their
  comparison with fibred-in-setoids models and representable presheaves;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.IsRepresentable`,
  `FibredInGroupoidsOver.isRepresentable_iff_exists_presentation`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInGroupoidsOver.overMap`,
  `FibredInGroupoidsOver.mor_isoClasses_equiv_hom`,
  `RepresentableBy.uniqueUpToIso`;
- best owner abstraction: the bundled object `FibredInGroupoidsOver C`, with presentation data
  expressed by morphisms in that owner category rather than by raw based-functor types. The
  bundled object `FibredInGroupoidsOver.ofFunctor p` is already universe-general, so the source-
  facing statement should use its owner predicate directly rather than a parallel wrapper;
- primitive data: the bundled owner object `P : FibredInGroupoidsOver C` and the chosen
  presentations by slice projections;
- derived API: the representability criterion via the iso-class presheaf and the uniqueness of the
  representing object via `Functor.RepresentableBy` on the iso-class presheaf.

Source/core/bridge triage:
- `source-facing`: the representability criterion and uniqueness of representing objects;
- `core/canonical`: `FibredInGroupoidsOver.IsRepresentable`, `Functor.IsRepresentable`,
  `Functor.fiberIsoClassPresheaf`, and `RepresentableBy.uniqueUpToIso`;
- `bridge/view`: the presentation morphisms over `C`, expressed in the owner category
  `FibredInGroupoidsOver C`, and the canonical slice comparison `overMap`. -/

-- Proof sketch: if `p` is representable, choose an equivalence with a slice category `C/X`; then
-- Lemma `4.39.5` gives the setoid condition, while Lemma `4.38.6` together with Example `4.38.7`
-- identifies the iso-class presheaf with the representable presheaf `h_X`. Conversely, if `p` is
-- fibred in setoids and this presheaf is representable, apply Lemma `4.39.5` to replace `p` by a
-- fibred-in-sets model and then use Lemma `4.38.6` to identify that model with a slice category.
/-- Helper for Lemma 4.40.2: an equivalence over `C` from `P` to a slice projection `C/X ⥤ C`
forces the fibers of `P` to be setoids. -/
private theorem isFibredInSetoids_of_equivalence_to_over
    {P : FibredInGroupoidsOver C} {X : C}
    (e : P ≌ ofFunctor (Over.forget X)) :
    IsFibredInSetoids P.p := by
  let hBase : (FibredInGroupoidsMor.toBasedFunctor e.hom).IsEquivalenceOverBase :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase e
  refine { fiber_isThin := ?_ }
  intro U
  let F := FibredInGroupoidsMor.fiberFunctor e.hom U
  letI : F.IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (FibredInGroupoidsMor.toBasedFunctor e.hom) hBase U
  letI : F.Faithful := by
    infer_instance
  -- Transport thinness from the slice fiber across the fiberwise equivalence.
  have hThinTarget : Quiver.IsThin ((Over.forget X).Fiber U) := by
    intro a b
    refine ⟨?_⟩
    intro f g
    apply Functor.Fiber.hom_ext
    apply Over.OverMorphism.ext
    have hf := @IsHomLift.fac' _ _ _ _ (Over.forget X) U U _ _ (𝟙 U)
      (Functor.Fiber.fiberInclusion.map f) f.2
    have hg := @IsHomLift.fac' _ _ _ _ (Over.forget X) U U _ _ (𝟙 U)
      (Functor.Fiber.fiberInclusion.map g) g.2
    simpa using hf.trans hg.symm
  intro a b
  refine ⟨?_⟩
  intro f g
  apply F.map_injective
  have hsub : Subsingleton (F.obj a ⟶ F.obj b) := hThinTarget (F.obj a) (F.obj b)
  exact @Subsingleton.elim _ hsub _ _

private noncomputable def fiberIsoClassPresheaf_point_of_equivalence
    {P : FibredInGroupoidsOver C} {X : C}
    (e : P ≌ ofFunctor (Over.forget X)) :
    (fiberIsoClassPresheaf P.p).obj (op X) :=
  let hx : P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X))) = X := by
    simpa using
      (show
          P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X))) =
            (Over.forget X).obj (Over.mk (𝟙 X)) from
          congrArg
            (fun F : Over X ⥤ C ↦ F.obj (Over.mk (𝟙 X)))
            (FibredInGroupoidsMor.comm e.inv))
  let x : P.p.Fiber X :=
    ⟨(FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X)), hx⟩
  Quotient.mk'' x

/-- Helper for Lemma 4.40.2: an object of the fiber of `Over.forget X` over `Y` determines its
underlying arrow `Y ⟶ X`. -/
private noncomputable def overFiberToHom (X Y : C) :
    ((Over.forget X).Fiber Y) → (Y ⟶ X) :=
  fun a ↦ eqToHom a.2.symm ≫ a.1.hom

/-- Helper for Lemma 4.40.2: the fiber of the slice projection `Over.forget X` over `Y` is
canonically identified with the hom-set `Y ⟶ X`. -/
private theorem overFiberToHom_bijective (X Y : C) :
    Function.Bijective (overFiberToHom X Y) := by
  constructor
  · intro a b h
    cases a with
    | mk a ha =>
        cases b with
        | mk b hb =>
            dsimp [overFiberToHom] at h ⊢
            cases a with
            | mk la ra ha' =>
                cases b with
                | mk lb rb hb' =>
                    cases ha
                    cases hb
                    cases ra
                    cases rb
                    have h' : ha' = hb' := by
                      simpa [Over.forget_obj] using h
                    subst h'
                    rfl
  · intro f
    refine ⟨⟨Over.mk f, rfl⟩, ?_⟩
    simp [overFiberToHom]

/-- Helper for Lemma 4.40.2: a morphism in a slice fiber identifies the underlying arrows to
`X`, so `overFiberToHom` is constant on isomorphism classes. -/
private theorem overFiberToHom_eq_of_hom
    {X Y : C} {a b : (Over.forget X).Fiber Y} (h : a ⟶ b) :
    overFiberToHom X Y a = overFiberToHom X Y b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  simp [overFiberToHom]
  have hw : (Functor.Fiber.fiberInclusion.map h).left ≫ fb = fa := by
    simpa using Over.w (Functor.Fiber.fiberInclusion.map h)
  have hleft : (Functor.Fiber.fiberInclusion.map h).left = 𝟙 Y := by
    simpa using (@IsHomLift.fac' _ _ _ _ (Over.forget X) Y Y _ _ (𝟙 Y)
      (Functor.Fiber.fiberInclusion.map h) h.2)
  rw [hleft] at hw
  have hid : 𝟙 Y ≫ fb = fb := by
    simp
  have hw' : fb = fa := hid.symm.trans hw
  simpa using hw'.symm

/-- Helper for Lemma 4.40.2: the set of isomorphism classes in the slice fiber over `Y` is
canonically identified with the hom-set `Y ⟶ X`. -/
private noncomputable def overFiberIsoClassToHom (X Y : C) :
    isomorphismClasses.obj (Cat.of ((Over.forget X).Fiber Y)) → (Y ⟶ X) :=
  fun q ↦
    Quotient.liftOn q
      (overFiberToHom X Y)
      (fun a b h ↦ by
        rcases h with ⟨i⟩
        exact overFiberToHom_eq_of_hom i.hom)

/-- Helper for Lemma 4.40.2: quotienting the slice fiber by isomorphism classes does not lose
the underlying arrow to `X`. -/
private theorem overFiberIsoClassToHom_bijective (X Y : C) :
    Function.Bijective (overFiberIsoClassToHom X Y) := by
  constructor
  · intro q₁ q₂ hq
    refine Quotient.inductionOn₂ q₁ q₂ ?_ hq
    intro a b hab
    exact
      _root_.Quotient.sound
        (show CategoryTheory.IsIsomorphic a b from
          ⟨eqToIso ((overFiberToHom_bijective X Y).1 hab)⟩)
  · intro f
    exact ⟨Quotient.mk'' ⟨Over.mk f, rfl⟩, by
      change overFiberToHom X Y ⟨Over.mk f, rfl⟩ = f
      simp [overFiberToHom]⟩

/-- Helper for Lemma 4.40.2: a morphism in `Over X` lying over `f : Y ⟶ Z` identifies the
underlying arrow of the source with `f` followed by the underlying arrow of the target. -/
private theorem overFiberToHom_eq_comp_of_isHomLift
    {X Y Z : C} {a : (Over.forget X).Fiber Y} {b : (Over.forget X).Fiber Z}
    {f : Y ⟶ Z} {h : a.1 ⟶ b.1} [IsHomLift (Over.forget X) f h] :
    overFiberToHom X Y a = f ≫ overFiberToHom X Z b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases a with ⟨la, ra, fa⟩
  rcases b with ⟨lb, rb, fb⟩
  dsimp at ha hb
  cases ha
  cases hb
  -- Read the base component of `h` from the hom-lift condition and combine it with `Over.w`.
  have hfac : (Over.forget X).map h = f := by
    simpa using (@IsHomLift.fac' _ _ _ _ (Over.forget X) Y Z _ _ f h inferInstance)
  have hw : h.left ≫ fb = fa := by
    simpa using Over.w h
  have hw' : fa = f ≫ fb := by
    rw [← hfac]
    simpa using hw.symm
  simpa [overFiberToHom] using hw'

/-- Helper for Lemma 4.40.2: a natural isomorphism of presheaves induces an equivalence between
their categories of elements. -/
private noncomputable def elementsEquivalenceOfIso
    {F G : Cᵒᵖ ⥤ Type (max u v)} (e : F ≅ G) :
    F.Elements ≌ G.Elements where
  functor := CategoryOfElements.map e.hom
  inverse := CategoryOfElements.map e.inv
  unitIso :=
    NatIso.ofComponents
      (fun x ↦ CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp))
      (fun f ↦ by
        apply CategoryOfElements.ext
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun x ↦ CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp))
      (fun f ↦ by
        apply CategoryOfElements.ext
        simp)
  functor_unitIso_comp x := by
    apply CategoryOfElements.ext
    simp

/-- Helper for Lemma 4.40.2: applying a morphism of fibred groupoids to a chosen pullback object
gives an object isomorphic to the chosen pullback of the image object in the target fiber. -/
private theorem fiberIsoClassPullbackComparisonIso
    {P Q : FibredInGroupoidsOver C} (F : FibredInGroupoidsMor P Q)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : P.p.Fiber (unop U)) :
    Nonempty
      (((FibredInGroupoidsMor.fiberFunctor F (unop V)).obj
        (((canonicalPullbackChoice P.p).pullbackFunctor f.unop).obj x)) ≅
      ((canonicalPullbackChoice Q.p).pullbackFunctor f.unop).obj
        ((FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x)) := by
  let hP := canonicalPullbackChoice P.p
  let hQ := canonicalPullbackChoice Q.p
  let xPull := ((hP.pullbackFunctor f.unop).obj x)
  let yImg := (FibredInGroupoidsMor.fiberFunctor F (unop U)).obj x
  let yPull := ((hQ.pullbackFunctor f.unop).obj yImg)
  have hf : f.unop = 𝟙 (unop V) ≫ f.unop := by
    simp
  -- The chosen pullback in `P` maps to a lift over `f`, so strong cartesianness in `Q`
  -- produces a vertical comparison to the chosen pullback of the image object.
  letI : P.p.IsHomLift f.unop (hP.map f.unop x) :=
    (hP.isStronglyCartesian f.unop x).toIsHomLift
  have hτ :
      Q.p.IsHomLift f.unop
        ((FibredInGroupoidsMor.toBasedFunctor F).map (hP.map f.unop x)) := by
    simpa using
      (show Q.p.IsHomLift f.unop
        ((FibredInGroupoidsMor.toBasedFunctor F).map (hP.map f.unop x)) from inferInstance)
  letI :
      Q.p.IsHomLift f.unop
        ((FibredInGroupoidsMor.toBasedFunctor F).map (hP.map f.unop x)) :=
    hτ
  let τ' := (FibredInGroupoidsMor.toBasedFunctor F).map (hP.map f.unop x)
  let ψ :=
    @IsStronglyCartesian.map _ _ _ _ Q.p
      (unop V)
      (unop U)
      yPull.1
      yImg.1
      f.unop
      (hQ.map f.unop yImg)
      (hQ.isStronglyCartesian f.unop yImg)
      (unop V)
      ((FibredInGroupoidsMor.toBasedFunctor F).obj xPull.1)
      (𝟙 (unop V))
      f.unop
      hf
      τ'
      hτ
  have hψ : Q.p.IsHomLift (𝟙 (unop V)) ψ := by
    dsimp [ψ]
    infer_instance
  let m :
      ((FibredInGroupoidsMor.fiberFunctor F (unop V)).obj xPull) ⟶ yPull :=
    ⟨ψ, hψ⟩
  -- Any vertical morphism in a fiber of a fibred groupoid is automatically invertible.
  exact ⟨asIso m⟩

/-- Helper for Lemma 4.40.2: a natural transformation of presheaves induces a morphism over `C`
between the opposite categories of elements. -/
private noncomputable def presheafElementsOpMap
    {F G : Cᵒᵖ ⥤ Type (max u v)} (α : F ⟶ G) :
    FibredInGroupoidsMor
      (FibredInGroupoidsOver.ofFunctor ((CategoryOfElements.π F).leftOp))
      (FibredInGroupoidsOver.ofFunctor ((CategoryOfElements.π G).leftOp)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := (CategoryOfElements.map α).op
      w := rfl }

/-- Helper for Lemma 4.40.2: if a natural transformation of presheaves is an isomorphism, then
the induced morphism on opposite categories of elements is an equivalence over `C`. -/
private theorem presheafElementsOpMap_isEquivalenceOverBase_of_iso
    {F G : Cᵒᵖ ⥤ Type (max u v)} (e : F ≅ G) :
    (presheafElementsOpMap e.hom).IsEquivalenceOverBase := by
  let E : F.Elementsᵒᵖ ≌ G.Elementsᵒᵖ := (elementsEquivalenceOfIso e).op
  have hEq : (FibredInGroupoidsMor.G (presheafElementsOpMap e.hom)).IsEquivalence := by
    simpa [E, presheafElementsOpMap, elementsEquivalenceOfIso] using
      (inferInstance : E.functor.IsEquivalence)
  exact FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence (F := presheafElementsOpMap e.hom) hEq

/-- Helper for Lemma 4.40.2: the canonical arrow from a costructured arrow for
`uliftYoneda.obj X` to `Over X` is compatible with the base projection. -/
private theorem costructuredArrowULiftYonedaToOver_w (X : C)
    {Y Z : CostructuredArrow uliftYoneda.{u} (uliftYoneda.{u}.obj X)} (g : Y ⟶ Z) :
    (CostructuredArrow.proj uliftYoneda.{u} (uliftYoneda.{u}.obj X)).map g ≫
        (uliftYonedaEquiv.{u} Z.hom).down =
      (uliftYonedaEquiv.{u} Y.hom).down := by
  simpa [FunctorToTypes.map_comp_apply, ← CostructuredArrow.w g] using
    congrArg ULift.down
      (uliftYonedaEquiv_naturality (F := uliftYoneda.{u}.obj X) Z.hom g.left.op)

/-- Helper for Lemma 4.40.2: costructured arrows into `uliftYoneda.obj X` give the slice category
over `X`. -/
private noncomputable def costructuredArrowULiftYonedaToOver (X : C) :
    CostructuredArrow uliftYoneda.{u} (uliftYoneda.{u}.obj X) ⥤ Over X :=
  -- Package the Yoneda-classified arrow carried by each costructured arrow as an object of
  -- the slice category over `X`.
  Functor.toOver (CostructuredArrow.proj uliftYoneda.{u} (uliftYoneda.{u}.obj X)) X
    (fun Y ↦ (uliftYonedaEquiv.{u} Y.hom).down)
    (fun g ↦ costructuredArrowULiftYonedaToOver_w X g)

/-- Helper for Lemma 4.40.2: the chosen arrow recovered from a costructured arrow into
`uliftYoneda.obj X` gives back the original costructured-arrow morphism under `uliftYoneda`. -/
private theorem costructuredArrowULiftYonedaToOver_unit_hom_eq
    (X : C) (Z : CostructuredArrow uliftYoneda.{u} (uliftYoneda.{u}.obj X)) :
    uliftYoneda.{u}.map ((uliftYonedaEquiv.{u} Z.hom).down) = Z.hom := by
  -- This is exactly the left-inverse computation from the ULift-Yoneda lemma, specialized to
  -- the arrow carried by the costructured-arrow object `Z`.
  ext Y y
  apply ULift.ext
  have h :=
    congrArg ULift.down (FunctorToTypes.naturality _ _ Z.hom y.down.op (ULift.up (𝟙 _)))
  simpa [uliftYoneda, uliftYonedaEquiv] using h.symm

/-- Helper for Lemma 4.40.2: applying `uliftYonedaEquiv` to the slice arrow `Y.hom` recovers
that arrow after taking `ULift.down`. -/
private theorem costructuredArrowULiftYonedaToOver_counit_hom_eq
    (X : C) (Y : Over X) :
    (uliftYonedaEquiv.{u} (uliftYoneda.{u}.map Y.hom)).down = Y.hom := by
  -- The ULift-Yoneda equivalence sends the represented morphism `Y.hom` to its universal
  -- element `ULift.up Y.hom`.
  simpa using congrArg ULift.down (uliftYonedaEquiv_uliftYoneda_map.{u, v, u} Y.hom)

/-- Helper for Lemma 4.40.2: the costructured-arrow model of `uliftYoneda.obj X` is canonically
equivalent to the slice category `Over X`. -/
private noncomputable def costructuredArrowULiftYonedaOverEquivalence (X : C) :
    CostructuredArrow uliftYoneda.{u} (uliftYoneda.{u}.obj X) ≌ Over X where
  functor := costructuredArrowULiftYonedaToOver X
  inverse := CostructuredArrow.post (𝟭 C) uliftYoneda.{u} X
  unitIso :=
    NatIso.ofComponents
      (fun Z ↦
        CostructuredArrow.isoMk (Iso.refl _) (by
          simpa [costructuredArrowULiftYonedaToOver] using
            costructuredArrowULiftYonedaToOver_unit_hom_eq X Z))
      (by
        intro Y Z f
        apply CostructuredArrow.hom_ext
        simp [costructuredArrowULiftYonedaToOver])
  counitIso :=
    NatIso.ofComponents
      (fun Y ↦
        Over.isoMk (Iso.refl _) (by
          simpa [costructuredArrowULiftYonedaToOver] using
            (costructuredArrowULiftYonedaToOver_counit_hom_eq X Y).symm))
      (by
        intro Y Z f
        ext
        simp [costructuredArrowULiftYonedaToOver])
  functor_unitIso_comp Z := by
    ext
    simp [costructuredArrowULiftYonedaToOver]

/-- Helper for Lemma 4.40.2: the opposite category of elements of `uliftYoneda.obj X` is
canonically equivalent to `Over X`. -/
private noncomputable def uliftRepresentableElementsOpToOverEquivalence (X : C) :
    (uliftYoneda.{u}.obj X).Elementsᵒᵖ ≌ Over X :=
  -- First identify elements with costructured arrows, then pass to the slice model.
  (CategoryOfElements.costructuredArrowULiftYonedaEquivalence (uliftYoneda.{u}.obj X)).trans
    (costructuredArrowULiftYonedaOverEquivalence X)

/-- Helper for Lemma 4.40.2: the ULift-Yoneda elements-to-slice equivalence is strict over the
base category `C`. -/
private theorem uliftRepresentableElementsOpToOver_comp_forget (X : C) :
    (uliftRepresentableElementsOpToOverEquivalence X).functor ⋙ Over.forget X =
      (CategoryOfElements.π (uliftYoneda.{u}.obj X)).leftOp := by
  have hToOver :
      costructuredArrowULiftYonedaToOver X ⋙ Over.forget X =
        CostructuredArrow.proj uliftYoneda.{u} (uliftYoneda.{u}.obj X) := by
    simpa [costructuredArrowULiftYonedaToOver] using
      (Functor.toOver_comp_forget
        (CostructuredArrow.proj uliftYoneda.{u} (uliftYoneda.{u}.obj X)) X
        (fun Y ↦ (uliftYonedaEquiv.{u} Y.hom).down)
        (fun g ↦ costructuredArrowULiftYonedaToOver_w X g))
  calc
    (uliftRepresentableElementsOpToOverEquivalence X).functor ⋙ Over.forget X =
        (CategoryOfElements.costructuredArrowULiftYonedaEquivalence
          (uliftYoneda.{u}.obj X)).functor ⋙
            costructuredArrowULiftYonedaToOver X ⋙ Over.forget X := rfl
    _ =
        (CategoryOfElements.costructuredArrowULiftYonedaEquivalence
          (uliftYoneda.{u}.obj X)).functor ⋙
            CostructuredArrow.proj uliftYoneda.{u} (uliftYoneda.{u}.obj X) := by
          exact congrArg
            (fun F : CostructuredArrow uliftYoneda.{u} (uliftYoneda.{u}.obj X) ⥤ C ↦
              (CategoryOfElements.costructuredArrowULiftYonedaEquivalence
                (uliftYoneda.{u}.obj X)).functor ⋙ F)
            hToOver
    _ = (CategoryOfElements.π (uliftYoneda.{u}.obj X)).leftOp := rfl

/-- Helper for Lemma 4.40.2: the source-facing owner morphism from the opposite category of
elements of `uliftYoneda.obj X` to the slice projection `Over.forget X`. -/
private noncomputable abbrev uliftRepresentableElementsOpToOver (X : C) :
    FibredInGroupoidsMor
      (FibredInGroupoidsOver.ofFunctor ((CategoryOfElements.π (uliftYoneda.{u}.obj X)).leftOp))
      (FibredInGroupoidsOver.ofFunctor (Over.forget X)) :=
  FibredInGroupoidsMor.ofBasedFunctor
    { toFunctor := (uliftRepresentableElementsOpToOverEquivalence X).functor
      w := uliftRepresentableElementsOpToOver_comp_forget X }

/-- Helper for Lemma 4.40.2: the owner morphism from the opposite category of elements of
`uliftYoneda.obj X` to `Over.forget X` is an equivalence over `C`. -/
private theorem uliftRepresentableElementsOpToOver_isEquivalenceOverBase (X : C) :
    (uliftRepresentableElementsOpToOver X).IsEquivalenceOverBase := by
  -- Forgetting the base data, the functor is the equivalence functor constructed above.
  apply FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence
  simpa [uliftRepresentableElementsOpToOver] using
    (inferInstance : (uliftRepresentableElementsOpToOverEquivalence X).functor.IsEquivalence)

/-- Helper for Lemma 4.40.2: if a presheaf `F` is representable, then the opposite category of
elements of `F` is equivalent over `C` to the slice projection `Over.forget F.reprX`. -/
private noncomputable def represented_iso_class_presheaf_elements_to_over
    (F : Cᵒᵖ ⥤ Type (max u v)) [F.IsRepresentable] :
    FibredInGroupoidsMor
      (ofFunctor ((CategoryOfElements.π F).leftOp))
      (ofFunctor (Over.forget F.reprX)) :=
  -- Transport the category of elements directly to the ULift-Yoneda slice model and then use the
  -- canonical ULift-Yoneda identification with the slice category.
  presheafElementsOpMap F.uliftYonedaReprXIso.symm.hom ≫
    uliftRepresentableElementsOpToOver F.reprX

/-- Helper for Lemma 4.40.2: the comparison from the opposite category of elements of a
represented presheaf to the corresponding slice projection is an equivalence over the base. -/
private theorem represented_iso_class_presheaf_elements_to_over_isEquivalenceOverBase
    (F : Cᵒᵖ ⥤ Type (max u v)) [F.IsRepresentable] :
    (represented_iso_class_presheaf_elements_to_over F).IsEquivalenceOverBase := by
  let E : F.Elementsᵒᵖ ≌ Over F.reprX :=
    (elementsEquivalenceOfIso F.uliftYonedaReprXIso.symm).op.trans
      (uliftRepresentableElementsOpToOverEquivalence F.reprX)
  have hEq :
      (FibredInGroupoidsMor.G (represented_iso_class_presheaf_elements_to_over F)).IsEquivalence := by
    -- The comparison functor is exactly the functor underlying the composed equivalence above.
    simpa [E, represented_iso_class_presheaf_elements_to_over, presheafElementsOpMap,
      uliftRepresentableElementsOpToOver, elementsEquivalenceOfIso] using
      (inferInstance : E.functor.IsEquivalence)
  exact FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence
    (F := represented_iso_class_presheaf_elements_to_over F) hEq

-- Proof sketch: identify each fiber of `P` with the corresponding slice fiber via the chosen
-- equivalence over `C`; in the slice model, the universal element is `id_X`, and pullback along
-- `f : Y ⟶ X` is literally the object `Over.mk f`.
private theorem fiberIsoClassPresheaf_isRepresentedBy_of_equivalence
    {P : FibredInGroupoidsOver C} {X : C}
    (e : P ≌ ofFunctor (Over.forget X)) :
    (fiberIsoClassPresheaf P.p).IsRepresentedBy
      (fiberIsoClassPresheaf_point_of_equivalence e) := by
  rw [isRepresentedBy_iff]
  intro Y
  let hBase : (FibredInGroupoidsMor.toBasedFunctor e.hom).IsEquivalenceOverBase :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase e
  let F := FibredInGroupoidsMor.fiberFunctor e.hom Y
  letI : F.IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (FibredInGroupoidsMor.toBasedFunctor e.hom) hBase Y
  have hClassBij :
      Function.Bijective
        (isomorphismClasses.map F.toCatHom :
          isomorphismClasses.obj (Cat.of (P.p.Fiber Y)) →
            isomorphismClasses.obj (Cat.of ((Over.forget X).Fiber Y))) := by
    let E := F.asEquivalence
    have hleft :
        Function.LeftInverse
          (isomorphismClasses.map E.inverse.toCatHom)
          (isomorphismClasses.map F.toCatHom) := by
      intro q
      refine Quotient.inductionOn q ?_
      intro x
      -- The fiberwise unit identifies the pulled-back class with the original one.
      exact _root_.Quotient.sound
        (show CategoryTheory.IsIsomorphic (E.inverse.obj (F.obj x)) x from
          ⟨E.unitIso.symm.app x⟩)
    constructor
    · intro q₁ q₂ hq
      exact hleft.injective hq
    · intro q
      refine Quotient.inductionOn q ?_
      intro y
      refine ⟨Quotient.mk'' (E.inverse.obj y), ?_⟩
      -- The fiberwise counit produces a representative of every target class.
      exact _root_.Quotient.sound
        (show CategoryTheory.IsIsomorphic (F.obj (E.inverse.obj y)) y from
          ⟨E.counitIso.app y⟩)
  let hClasses :
      isomorphismClasses.obj (Cat.of (P.p.Fiber Y)) ≃
        isomorphismClasses.obj (Cat.of ((Over.forget X).Fiber Y)) :=
    Equiv.ofBijective (isomorphismClasses.map F.toCatHom) hClassBij
  let hEquiv : isomorphismClasses.obj (Cat.of (P.p.Fiber Y)) ≃ (Y ⟶ X) :=
    hClasses.trans (Equiv.ofBijective (overFiberIsoClassToHom X Y)
      (overFiberIsoClassToHom_bijective X Y))
  have hMapEq :
      (fun f : Y ⟶ X ↦
        (fiberIsoClassPresheaf P.p).map f.op (fiberIsoClassPresheaf_point_of_equivalence e)) =
      hEquiv.symm := by
    let x : P.p.Fiber X :=
      ⟨(FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X)), by
        simpa using
          (show
              P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X))) =
                (Over.forget X).obj (Over.mk (𝟙 X)) from
              congrArg
                (fun F : Over X ⥤ C ↦ F.obj (Over.mk (𝟙 X)))
                (FibredInGroupoidsMor.comm e.inv))⟩
    have hPoint :
        overFiberToHom X X ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x) = 𝟙 X := by
      let τ := FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.counit
      have hτ : (Over.forget X).IsHomLift (𝟙 X) (τ.hom.app (Over.mk (𝟙 X))) := by
        simpa using BasedNatTrans.isHomLift τ.hom (rfl : (Over.forget X).obj (Over.mk (𝟙 X)) = X)
      let m : ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x) ⟶ ⟨Over.mk (𝟙 X), rfl⟩ :=
        ⟨τ.hom.app (Over.mk (𝟙 X)), hτ⟩
      simpa [overFiberToHom] using overFiberToHom_eq_of_hom m
    funext f
    apply hEquiv.injective
    -- After transporting to the slice fiber, the chosen universal element becomes `id_X`,
    -- and pullback along `f` recovers the class of the arrow `f`.
    let i :=
      Classical.choice (fiberIsoClassPullbackComparisonIso (F := e.hom) (f := f.op) x)
    have hCompare :
        overFiberToHom X Y
            ((FibredInGroupoidsMor.fiberFunctor e.hom Y).obj
              (((canonicalPullbackChoice P.p).pullbackFunctor f).obj x)) =
          overFiberToHom X Y
            (((canonicalPullbackChoice (Over.forget X)).pullbackFunctor f).obj
              ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x)) := by
      exact overFiberToHom_eq_of_hom i.hom
    have hPull :
        overFiberToHom X Y
            (((canonicalPullbackChoice (Over.forget X)).pullbackFunctor f).obj
              ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x)) =
          f ≫ overFiberToHom X X ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x) := by
      let a :=
        ((canonicalPullbackChoice (Over.forget X)).pullbackFunctor f).obj
          ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x)
      let b := (FibredInGroupoidsMor.fiberFunctor e.hom X).obj x
      let hMap := (canonicalPullbackChoice (Over.forget X)).map f b
      have hLift : (Over.forget X).IsHomLift f hMap :=
        ((canonicalPullbackChoice (Over.forget X)).isStronglyCartesian f
          ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x)).toIsHomLift
      simpa [a, b, hMap] using
        (@overFiberToHom_eq_comp_of_isHomLift C _ X Y X a b f hMap hLift)
    have hFinal :
        overFiberToHom X Y
            ((FibredInGroupoidsMor.fiberFunctor e.hom Y).obj
              (((canonicalPullbackChoice P.p).pullbackFunctor f).obj x)) = f := by
      calc
        overFiberToHom X Y
            ((FibredInGroupoidsMor.fiberFunctor e.hom Y).obj
              (((canonicalPullbackChoice P.p).pullbackFunctor f).obj x)) =
          overFiberToHom X Y
            (((canonicalPullbackChoice (Over.forget X)).pullbackFunctor f).obj
              ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x)) := hCompare
        _ = f ≫ overFiberToHom X X ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x) := hPull
        _ = f := by simp [hPoint]
    simpa [hEquiv, hClasses, fiberIsoClassPresheaf_point_of_equivalence, x] using hFinal
  simpa [hMapEq] using hEquiv.symm.bijective

/-- Lemma 4.40.2 (1): a category fibred in groupoids over `C` is representable if and only if its
projection is fibred in setoids and the presheaf of isomorphism classes in its fibers is
representable. -/
private theorem isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_representable_aux
    (P : FibredInGroupoidsOver C) :
    P.IsRepresentable ↔
      IsFibredInSetoids P.p ∧ (fiberIsoClassPresheaf P.p).IsRepresentable := by
  constructor
  · intro hP
    rcases (FibredInGroupoidsOver.isRepresentable_iff_exists_presentation P).1 hP with
      ⟨X, j, hj⟩
    rcases FibredInGroupoidsMor.exists_equivalence j hj with ⟨e, he⟩
    refine ⟨?_, ?_⟩
    · -- The slice presentation transports the setoid condition back to `P`.
      simpa [he] using isFibredInSetoids_of_equivalence_to_over e
    · -- The representing object of the slice model gives a representing element for the
      -- iso-class presheaf of `P`.
      simpa [he] using
        (fiberIsoClassPresheaf_isRepresentedBy_of_equivalence e).representableBy.isRepresentable
  · rintro ⟨hSetoids, hRepresentable⟩
    let Z : FibredInSetoidsOver C := ⟨P, hSetoids⟩
    let _ : (fiberIsoClassPresheaf P.p).IsRepresentable := hRepresentable
    let j₁ :
        P ⟶ ofFunctor ((CategoryOfElements.π (fiberIsoClassPresheaf P.p)).leftOp) :=
      FibredInGroupoidsMor.ofBasedFunctor (FibredInSetoidsOver.toBasedFunctor Z.toFibredInSets)
    let j :
        P ⟶ ofFunctor (Over.forget (fiberIsoClassPresheaf P.p).reprX) :=
      j₁ ≫
        represented_iso_class_presheaf_elements_to_over (fiberIsoClassPresheaf P.p)
    have hjFunctor :
        (FibredInGroupoidsMor.G j).IsEquivalence := by
      have hLeft :
          (FibredInGroupoidsMor.G j₁).IsEquivalence := by
        -- The associated fibred-in-sets model is equivalent to `P` over the base.
        exact BasedFunctor.isEquivalence_of_isEquivalenceOverBase
          (FibredInGroupoidsMor.toBasedFunctor j₁)
          (FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase Z)
      have hRight :
          (FibredInGroupoidsMor.G
            (represented_iso_class_presheaf_elements_to_over (fiberIsoClassPresheaf P.p))).IsEquivalence := by
        -- The represented presheaf model is equivalent over `C` to the slice projection.
        exact BasedFunctor.isEquivalence_of_isEquivalenceOverBase
          (FibredInGroupoidsMor.toBasedFunctor
            (represented_iso_class_presheaf_elements_to_over (fiberIsoClassPresheaf P.p)))
          (represented_iso_class_presheaf_elements_to_over_isEquivalenceOverBase
            (fiberIsoClassPresheaf P.p))
      letI : (FibredInGroupoidsMor.G j₁).IsEquivalence := hLeft
      letI :
          (FibredInGroupoidsMor.G
            (represented_iso_class_presheaf_elements_to_over
              (fiberIsoClassPresheaf P.p))).IsEquivalence := hRight
      -- Route correction: compose the two established equivalences of total categories instead
      -- of re-entering the quotient-level fiber comparison.
      simpa [j] using
        (inferInstance :
          (FibredInGroupoidsMor.G j₁ ⋙
            FibredInGroupoidsMor.G
              (represented_iso_class_presheaf_elements_to_over
                (fiberIsoClassPresheaf P.p))).IsEquivalence)
    have hj : FibredInGroupoidsMor.IsEquivalenceOverBase j := by
      -- Upgrade the total-category equivalence to the required owner-level equivalence over `C`.
      exact FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence (F := j) hjFunctor
    exact
      (FibredInGroupoidsOver.isRepresentable_iff_exists_presentation P).2
        ⟨(fiberIsoClassPresheaf P.p).reprX, j, hj⟩

end FibredInGroupoidsOver

end CategoryTheory

namespace CategoryTheory

open BasedFunctor
open FibredInGroupoidsMor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsOver

open Functor Opposite

variable {P : FibredInGroupoidsOver C}
variable {X X' : C}

/-- Owner-level reformulation of Lemma 4.40.2 (1), re-exported on `FibredInGroupoidsOver` from the
statement-pipeline entry declaration. -/
theorem isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_isRepresentable
    (P : FibredInGroupoidsOver C) :
    P.IsRepresentable ↔
      IsFibredInSetoids P.p ∧ (fiberIsoClassPresheaf P.p).IsRepresentable := by
  simpa using isRepresentable_iff_isFibredInSetoids_and_fiberIsoClassPresheaf_representable_aux P

-- Proof sketch: a presentation morphism over `C` upgrades to a bicategorical equivalence by
-- `FibredInGroupoidsMor.exists_equivalence`; the corresponding represented object of the iso-class
-- presheaf is then obtained from the equivalence-level construction above.
private noncomputable def presentation_representableBy
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (hj : j.IsEquivalenceOverBase) :
    (fiberIsoClassPresheaf P.p).RepresentableBy X := by
  classical
  let e := Classical.choose (FibredInGroupoidsMor.exists_equivalence j hj)
  have he : e.hom = j := Classical.choose_spec (FibredInGroupoidsMor.exists_equivalence j hj)
  simpa [he] using (fiberIsoClassPresheaf_isRepresentedBy_of_equivalence e).representableBy

/-- The canonical comparison morphism on the representing base objects attached to two slice
presentations of the same represented fibred category in groupoids. It is extracted from the
identity morphism of `P` via the owner equivalence `mor_isoClasses_equiv_hom`. -/
noncomputable def presentationComparisonHom
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    X ⟶ X' :=
  mor_isoClasses_equiv_hom j j' hj hj' (Quotient.mk'' (𝟙 P))

/-- Lemma 4.40.2 (2): if `P : FibredInGroupoidsOver C` is represented over `C` both by `C/X`
and by `C/X'`, then the identity morphism of `P` induces the canonical comparison morphism
`X ⟶ X'` between the representing objects attached to the two presentations. Equivalently, the two
presentation morphisms differ only by whiskering with `overMap` on this comparison morphism, up to
`2`-isomorphism over `C`. This is the morphism-level bridge behind the pair-level uniqueness
statement below. -/
theorem presentationComparisonHom_induces
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    FibredInGroupoidsMor.InducesHom
      (𝟙 P) j j' (presentationComparisonHom j j' hj hj') := by
  exact
    (inducesHom_iff_mor_isoClasses_equiv_hom_eq j j' hj hj' (𝟙 P)
      (presentationComparisonHom j j' hj hj')).2 rfl

/-- The canonical isomorphism between the representing objects of two slice presentations of the
same represented fibred category in groupoids. This is the owner-level uniqueness isomorphism for
the represented iso-class presheaf, expressed through `RepresentableBy.uniqueUpToIso`. -/
private noncomputable def presentationIsoWitness
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    X ≅ X' :=
  RepresentableBy.uniqueUpToIso
    (presentation_representableBy j hj)
    (presentation_representableBy j' hj')

/-- Helper for Lemma 4.40.2: evaluating the Yoneda uniqueness morphism for the two presentation
witnesses in the target representing bijection recovers the universal element attached to the
source presentation. -/
private theorem presentationIsoWitness_homEquiv_eq_universal_element
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (presentation_representableBy j' hj').homEquiv
        (presentationIsoWitness j j' hj hj').hom =
      (presentation_representableBy j hj).homEquiv (𝟙 X) := by
  -- The private witness is the Yoneda uniqueness isomorphism between the two representing
  -- objects, so its image under the target representing bijection is the source universal
  -- element by the defining `homEquiv` formula of `RepresentableBy.uniqueUpToIso`.
  change
    (presentation_representableBy j' hj').homEquiv
        ((Functor.RepresentableBy.uniqueUpToIso
          (presentation_representableBy j hj)
          (presentation_representableBy j' hj')).hom) =
      (presentation_representableBy j hj).homEquiv (𝟙 X)
  rw [Functor.RepresentableBy.uniqueUpToIso_hom]
  rw [Yoneda.fullyFaithful_preimage]
  simp

/-- Helper for Lemma 4.40.2: the universal element of a presentation is the explicit class
obtained from the chosen equivalence to the slice category. -/
private theorem presentation_universal_element_eq_point_of_equivalence
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (hj : j.IsEquivalenceOverBase) :
    let e := Classical.choose (FibredInGroupoidsMor.exists_equivalence j hj)
    (presentation_representableBy j hj).homEquiv (𝟙 X) =
      fiberIsoClassPresheaf_point_of_equivalence e := by
  classical
  let e := Classical.choose (FibredInGroupoidsMor.exists_equivalence j hj)
  have he : e.hom = j := Classical.choose_spec (FibredInGroupoidsMor.exists_equivalence j hj)
  -- Unfold the chosen representing witness and read off its universal element at `𝟙 X`.
  dsimp [e]
  have hRep :
      presentation_representableBy j hj =
        (fiberIsoClassPresheaf_isRepresentedBy_of_equivalence e).representableBy := by
    simp [presentation_representableBy]
  rw [hRep]
  simp [e]

/-- Helper for Lemma 4.40.2: an equivalence over `C` transports isomorphism classes in the fiber
over `Y` to isomorphism classes in the corresponding slice fiber over `Y`. -/
private noncomputable def fiberIsoClass_equiv_overFiberIsoClass_of_equivalence
    {P : FibredInGroupoidsOver C} {X : C}
    (e : P ≌ ofFunctor (Over.forget X)) (Y : C) :
    isomorphismClasses.obj (Cat.of (P.p.Fiber Y)) ≃
      isomorphismClasses.obj (Cat.of ((Over.forget X).Fiber Y)) := by
  let hBase : (FibredInGroupoidsMor.toBasedFunctor e.hom).IsEquivalenceOverBase :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase e
  let F := FibredInGroupoidsMor.fiberFunctor e.hom Y
  letI : F.IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
      (FibredInGroupoidsMor.toBasedFunctor e.hom) hBase Y
  have hClassBij :
      Function.Bijective
        (isomorphismClasses.map F.toCatHom :
          isomorphismClasses.obj (Cat.of (P.p.Fiber Y)) →
            isomorphismClasses.obj (Cat.of ((Over.forget X).Fiber Y))) := by
    let E := F.asEquivalence
    have hleft :
        Function.LeftInverse
          (isomorphismClasses.map E.inverse.toCatHom)
          (isomorphismClasses.map F.toCatHom) := by
      intro q
      refine Quotient.inductionOn q ?_
      intro x
      -- The fiberwise unit transports the forward image of `x` back to `x`.
      exact _root_.Quotient.sound
        (show CategoryTheory.IsIsomorphic (E.inverse.obj (F.obj x)) x from
          ⟨E.unitIso.symm.app x⟩)
    constructor
    · intro q₁ q₂ hq
      exact hleft.injective hq
    · intro q
      refine Quotient.inductionOn q ?_
      intro y
      refine ⟨Quotient.mk'' (E.inverse.obj y), ?_⟩
      -- The fiberwise counit realizes every slice-fiber class as an image class.
      exact _root_.Quotient.sound
        (show CategoryTheory.IsIsomorphic (F.obj (E.inverse.obj y)) y from
          ⟨E.counitIso.app y⟩)
  exact Equiv.ofBijective (isomorphismClasses.map F.toCatHom) hClassBij

/-- Helper for Lemma 4.40.2: after transporting through an equivalence to a slice category, the
pullback of the target universal class along `φ` is read by `overFiberIsoClassToHom` as the arrow
`φ` itself. -/
private theorem fiberIsoClassPresheaf_map_point_of_equivalence_overFiberToHom_eq
    {P : FibredInGroupoidsOver C} {X X' : C}
    (e : P ≌ ofFunctor (Over.forget X')) (φ : X ⟶ X') :
    overFiberIsoClassToHom X' X
      (fiberIsoClass_equiv_overFiberIsoClass_of_equivalence e X
        ((fiberIsoClassPresheaf P.p).map φ.op
          (fiberIsoClassPresheaf_point_of_equivalence e))) = φ := by
  let x : P.p.Fiber X' :=
    ⟨(FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X')), by
      simpa using
        (show
            P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X'))) =
              (Over.forget X').obj (Over.mk (𝟙 X')) from
            congrArg
              (fun F : Over X' ⥤ C ↦ F.obj (Over.mk (𝟙 X')))
              (FibredInGroupoidsMor.comm e.inv))⟩
  have hPoint :
      overFiberToHom X' X' ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x) = 𝟙 X' := by
    let τ := FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.counit
    have hτ : (Over.forget X').IsHomLift (𝟙 X') (τ.hom.app (Over.mk (𝟙 X'))) := by
      simpa using
        BasedNatTrans.isHomLift τ.hom
          (rfl : (Over.forget X').obj (Over.mk (𝟙 X')) = X')
    let m : ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x) ⟶ ⟨Over.mk (𝟙 X'), rfl⟩ :=
      ⟨τ.hom.app (Over.mk (𝟙 X')), hτ⟩
    -- The counit identifies the transported universal object with `id_{X'}` in the slice fiber.
    simpa [overFiberToHom] using overFiberToHom_eq_of_hom m
  let i :=
    Classical.choice (fiberIsoClassPullbackComparisonIso (F := e.hom) (f := φ.op) x)
  have hCompare :
      overFiberToHom X' X
          ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj
            (((canonicalPullbackChoice P.p).pullbackFunctor φ).obj x)) =
        overFiberToHom X' X
          (((canonicalPullbackChoice (Over.forget X')).pullbackFunctor φ).obj
            ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x)) := by
    -- The pullback comparison isomorphism identifies the two slice-fiber representatives.
    exact overFiberToHom_eq_of_hom i.hom
  have hPull :
      overFiberToHom X' X
          (((canonicalPullbackChoice (Over.forget X')).pullbackFunctor φ).obj
            ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x)) =
        φ ≫ overFiberToHom X' X' ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x) := by
    let a :=
      ((canonicalPullbackChoice (Over.forget X')).pullbackFunctor φ).obj
        ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x)
    let b := (FibredInGroupoidsMor.fiberFunctor e.hom X').obj x
    let hMap := (canonicalPullbackChoice (Over.forget X')).map φ b
    have hLift : (Over.forget X').IsHomLift φ hMap :=
      ((canonicalPullbackChoice (Over.forget X')).isStronglyCartesian φ
        ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x)).toIsHomLift
    -- In the slice model, the chosen pullback over `φ` records postcomposition by `φ`.
    simpa [a, b, hMap] using
      (@overFiberToHom_eq_comp_of_isHomLift C _ X' X X' a b φ hMap hLift)
  have hFinal :
      overFiberToHom X' X
          ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj
            (((canonicalPullbackChoice P.p).pullbackFunctor φ).obj x)) = φ := by
    calc
      overFiberToHom X' X
          ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj
            (((canonicalPullbackChoice P.p).pullbackFunctor φ).obj x)) =
        overFiberToHom X' X
          (((canonicalPullbackChoice (Over.forget X')).pullbackFunctor φ).obj
            ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x)) := hCompare
      _ = φ ≫ overFiberToHom X' X' ((FibredInGroupoidsMor.fiberFunctor e.hom X').obj x) := hPull
      _ = φ := by simp [hPoint]
  -- Transport the already-computed slice representative back to the quotient-level statement.
  simpa [fiberIsoClass_equiv_overFiberIsoClass_of_equivalence,
    fiberIsoClassPresheaf_point_of_equivalence, x] using hFinal

/-- Helper for Lemma 4.40.2: evaluating the canonical comparison morphism in the target
representing bijection recovers the universal element of the source presentation. -/
private theorem presentation_source_universal_element_overFiberToHom_eq
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase)
    (e : P ≌ ofFunctor (Over.forget X))
    (e' : P ≌ ofFunctor (Over.forget X'))
    (he : e.hom = j)
    (he' : e'.hom = j') :
    overFiberIsoClassToHom X' X
      (fiberIsoClass_equiv_overFiberIsoClass_of_equivalence e' X
        (fiberIsoClassPresheaf_point_of_equivalence e)) =
      presentationComparisonHom j j' hj hj' := by
  classical
  let x : P.p.Fiber X :=
    ⟨(FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X)), by
      simpa using
        (show
            P.p.obj ((FibredInGroupoidsMor.G e.inv).obj (Over.mk (𝟙 X))) =
              (Over.forget X).obj (Over.mk (𝟙 X)) from
            congrArg
              (fun F : Over X ⥤ C ↦ F.obj (Over.mk (𝟙 X)))
              (FibredInGroupoidsMor.comm e.inv))⟩
  let φ := presentationComparisonHom j j' hj hj'
  let τsource := FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso e.counit
  let τcompare :=
    FibredInGroupoidsMor.basedFunctorIsoOfOwnerIso
      (Classical.choice (presentationComparisonHom_induces j j' hj hj'))
  let mSourceEquiv :
      ((FibredInGroupoidsMor.fiberFunctor e.hom X).obj x) ⟶ ⟨Over.mk (𝟙 X), rfl⟩ :=
    ⟨τsource.hom.app (Over.mk (𝟙 X)), by
      simpa using BasedNatTrans.isHomLift τsource.hom
        (rfl : (Over.forget X).obj (Over.mk (𝟙 X)) = X)⟩
  let mSource :
      ((FibredInGroupoidsMor.fiberFunctor j X).obj x) ⟶ ⟨Over.mk (𝟙 X), rfl⟩ := by
    simpa [he] using mSourceEquiv
  let y : (Over.forget X').Fiber X :=
    ⟨(Over.map φ).obj ((FibredInGroupoidsMor.fiberFunctor j X).obj x).1, by
      simpa using ((FibredInGroupoidsMor.fiberFunctor j X).obj x).2⟩
  let mCompare :
      ((FibredInGroupoidsMor.fiberFunctor j' X).obj x) ⟶ y :=
    ⟨τcompare.hom.app x.1, by
      simpa [he, he', φ, x, y, Functor.comp_obj, FibredInGroupoidsOver.overMap] using
        BasedNatTrans.isHomLift τcompare.hom x.2⟩
  let mTarget :
      y ⟶ ⟨(Over.map φ).obj (Over.mk (𝟙 X)), by simp⟩ :=
    ⟨(Over.map φ).map mSource.1, by
      have hMap :
          (Over.forget X').IsHomLift (𝟙 X)
            ((Over.map φ).map mSource.1) := by
        exact
          ((FibredInGroupoidsMor.toBasedFunctor (overMap φ)).isHomLift_iff (𝟙 X) mSource.1).2
            mSource.2
      simpa [y] using hMap⟩
  let m :
      ((FibredInGroupoidsMor.fiberFunctor j' X).obj x) ⟶
        ⟨(Over.map φ).obj (Over.mk (𝟙 X)), by
          change X = X
          rfl⟩ :=
    ⟨mCompare.1 ≫ mTarget.1, by
      let hCompare : (Over.forget X').IsHomLift (𝟙 X) mCompare.1 := mCompare.2
      let hTarget : (Over.forget X').IsHomLift (𝟙 X) mTarget.1 := mTarget.2
      exact @IsHomLift.comp_lift_id_right' _ _ _ _ (Over.forget X') _ _ _ _ _
        (𝟙 X) mCompare.1 hCompare X mTarget.1 hTarget⟩
  -- Evaluate the induced `2`-isomorphism at the source universal object and then compose with
  -- the source counit comparison transported by `Over.map φ`.
  have hm :
      overFiberToHom X' X ((FibredInGroupoidsMor.fiberFunctor j' X).obj x) = φ := by
    simpa [overFiberToHom] using overFiberToHom_eq_of_hom m
  simpa [fiberIsoClass_equiv_overFiberIsoClass_of_equivalence, overFiberIsoClassToHom,
    fiberIsoClassPresheaf_point_of_equivalence, he, he', x] using hm

/-- Helper for Lemma 4.40.2: evaluating the canonical comparison morphism in the target
representing bijection recovers the universal element of the source presentation. -/
private theorem presentationComparisonHom_map_universal_element
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (fiberIsoClassPresheaf P.p).map (presentationComparisonHom j j' hj hj').op
        ((presentation_representableBy j' hj').homEquiv (𝟙 X')) =
      (presentation_representableBy j hj).homEquiv (𝟙 X) := by
  classical
  let e := Classical.choose (FibredInGroupoidsMor.exists_equivalence j hj)
  let e' := Classical.choose (FibredInGroupoidsMor.exists_equivalence j' hj')
  have he : e.hom = j := Classical.choose_spec (FibredInGroupoidsMor.exists_equivalence j hj)
  have he' : e'.hom = j' := Classical.choose_spec (FibredInGroupoidsMor.exists_equivalence j' hj')
  let φ := presentationComparisonHom j j' hj hj'
  -- Rewrite both universal elements to the explicit fiber classes attached to the chosen
  -- source and target presentation equivalences.
  rw [presentation_universal_element_eq_point_of_equivalence j hj]
  rw [presentation_universal_element_eq_point_of_equivalence j' hj']
  -- Route correction: compare the two classes after transporting them to the target slice fiber,
  -- where `overFiberIsoClassToHom` reads both classes as the same arrow `φ : X ⟶ X'`.
  apply (fiberIsoClass_equiv_overFiberIsoClass_of_equivalence e' X).injective
  apply (overFiberIsoClassToHom_bijective X' X).1
  calc
    overFiberIsoClassToHom X' X
        ((fiberIsoClass_equiv_overFiberIsoClass_of_equivalence e' X)
          ((fiberIsoClassPresheaf P.p).map φ.op (fiberIsoClassPresheaf_point_of_equivalence e'))) =
      φ := fiberIsoClassPresheaf_map_point_of_equivalence_overFiberToHom_eq e' φ
    _ = overFiberIsoClassToHom X' X
          ((fiberIsoClass_equiv_overFiberIsoClass_of_equivalence e' X)
            (fiberIsoClassPresheaf_point_of_equivalence e)) := by
          symm
          exact
            presentation_source_universal_element_overFiberToHom_eq
              j j' hj hj' e e' he he'

/-- Helper for Lemma 4.40.2: evaluating the canonical comparison morphism in the target
representing bijection recovers the universal element of the source presentation. -/
private theorem presentationComparisonHom_homEquiv_eq_universal_element
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (presentation_representableBy j' hj').homEquiv
        (presentationComparisonHom j j' hj hj') =
      (presentation_representableBy j hj).homEquiv (𝟙 X) := by
  -- Rewrite the representing bijection evaluation into the presheaf map on the target universal
  -- element, which isolates the remaining comparison as a presheaf-level identity.
  rw [Functor.RepresentableBy.homEquiv_eq]
  exact presentationComparisonHom_map_universal_element j j' hj hj'

/-- The private witness isomorphism between two representing objects has underlying morphism equal
to the canonical comparison morphism induced from the identity presentation of `P`. -/
@[simp] private theorem presentationIsoWitness_hom
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (presentationIsoWitness j j' hj hj').hom =
      presentationComparisonHom j j' hj hj' := by
  -- Route correction: the direct rewrite against `RepresentableBy.uniqueUpToIso_hom` was too
  -- opaque. The stable route is to compare both arrows after applying the target representing
  -- bijection, where the Yoneda witness is already identified by the helper above.
  apply (presentation_representableBy j' hj').homEquiv.injective
  rw [presentationIsoWitness_homEquiv_eq_universal_element j j' hj hj']
  symm
  exact presentationComparisonHom_homEquiv_eq_universal_element j j' hj hj'

/-- The canonical comparison morphism between the two representing objects of slice presentations
is an isomorphism. The proof uses the private representability witness, while the public statement
is expressed entirely in terms of the canonical comparison morphism. -/
theorem presentationComparisonHom_isIso
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    IsIso (presentationComparisonHom j j' hj hj') := by
  simpa [presentationIsoWitness_hom j j' hj hj'] using
    (presentationIsoWitness j j' hj hj').isIso_hom

/-- The canonical isomorphism between the representing objects of two slice presentations of the
same represented fibred category in groupoids. It is the `asIso` of the canonical comparison
morphism `presentationComparisonHom`. -/
noncomputable def presentationIso
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    X ≅ X' :=
  letI := presentationComparisonHom_isIso j j' hj hj'
  asIso (presentationComparisonHom j j' hj hj')

/-- The canonical uniqueness isomorphism between two representing objects has underlying morphism
equal to the canonical comparison morphism induced from the identity presentation of `P`. -/
@[simp] theorem presentationIso_hom
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    (presentationIso j j' hj hj').hom =
      presentationComparisonHom j j' hj hj' := by
  simp [presentationIso]

/-- Lemma 4.40.2 (3): if `P : FibredInGroupoidsOver C` is represented over `C` both by `C/X`
and by `C/X'`, then the representing pair is unique up to isomorphism: the second presentation is
`2`-isomorphic over `C` to the first presentation whiskered by the canonical isomorphism of
representing objects. -/
theorem presentation_unique
    (j : FibredInGroupoidsMor P (ofFunctor (Over.forget X)))
    (j' : FibredInGroupoidsMor P (ofFunctor (Over.forget X')))
    (hj : j.IsEquivalenceOverBase)
    (hj' : j'.IsEquivalenceOverBase) :
    Nonempty
      (j' ≅
        j ≫ overMap (presentationIso j j' hj hj').hom) := by
  simpa [FibredInGroupoidsMor.InducesHom] using
    presentationComparisonHom_induces j j' hj hj'
end FibredInGroupoidsOver

end CategoryTheory
