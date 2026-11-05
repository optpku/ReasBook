module

public import stacks_project.Chap04.Lemma_4_36_4.Strictification.Core

@[expose] public section

universe v₁ v₂ v₃ vS u₁ u₂ u₃ w

namespace CategoryTheory

open Bicategory
open BasedFunctor
open Functor
open Fiber
open Opposite
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/-- Helper for Lemma 4.36.4: an object in the strict fiber over `V` is a target object together
with a chosen pullback presentation over `V`. -/
structure PullbackStrictificationObj
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (V : C) where
  target : C
  arrow : V ⟶ target
  fiberObj : Fiber p target

/-- Helper for Lemma 4.36.4: the strict fiber over `V` forgets a presentation `(f, x)` to the
actual pullback object `f^* x` in the standard fiber over `V`. -/
noncomputable def pullbackStrictificationFiberForget
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (V : C) :
    PullbackStrictificationObj p hc V → Fiber p V
  | ⟨_, f, x⟩ => (hc.pullbackFunctor f).obj x

/-- Helper for Lemma 4.36.4: the strict fiber over `V` uses the same objects as
`PullbackStrictificationObj p hc V`, with morphisms given by the corresponding vertical morphisms
between the actual pullback objects in `Fiber p V`. -/
abbrev PullbackStrictificationFiber
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (V : C) :=
  PullbackStrictificationObj p hc V

/-- Helper for Lemma 4.36.4: the strict fiber inherits a category structure from the actual fiber
`Fiber p V` by evaluating each presentation at its chosen pullback object. -/
noncomputable instance pullbackStrictificationFiberCategory
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (V : C) :
    Category (PullbackStrictificationFiber p hc V) where
  Hom X Y := pullbackStrictificationFiberForget p hc V X ⟶
    pullbackStrictificationFiberForget p hc V Y
  id X := 𝟙 (pullbackStrictificationFiberForget p hc V X)
  comp φ ψ := φ ≫ ψ

/-- Helper for Lemma 4.36.4: forgetting the pullback-presentation tags gives a literal functor
from the strict fiber over `V` to the usual fiber of `p` over `V`. -/
noncomputable def pullbackStrictificationFiberForgetFunctor
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (V : C) :
    PullbackStrictificationFiber p hc V ⥤ Fiber p V where
  obj := pullbackStrictificationFiberForget p hc V
  map := fun φ ↦ φ
  map_id := fun _ ↦ rfl
  map_comp := fun _ _ ↦ rfl

/-- Helper for Lemma 4.36.4: the strict fiber over `U` is equivalent to the ordinary fiber of
`p` over `U` by forgetting a pullback presentation and retaining only the represented object. -/
theorem pullback_strictification_fiber_forget_isEquivalence
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (U : C) :
    (pullbackStrictificationFiberForgetFunctor p hc U).IsEquivalence := by
  let F := pullbackStrictificationFiberForgetFunctor p hc U
  letI : F.Faithful := by
    -- The strict fiber uses the same hom-sets as the usual fiber, so `F.map` is injective.
    refine ⟨?_⟩
    intro X Y φ ψ hφψ
    exact hφψ
  letI : F.Full := by
    -- The same literal identification of hom-sets makes `F.map` surjective as well.
    refine ⟨?_⟩
    intro X Y φ
    exact ⟨φ, rfl⟩
  letI : F.EssSurj := by
    -- Every usual fiber object is represented by its identity presentation in the strict fiber.
    refine ⟨?_⟩
    intro y
    refine ⟨{ target := U, arrow := 𝟙 U, fiberObj := y }, ?_⟩
    refine ⟨?_⟩
    simpa [pullbackStrictificationFiberForgetFunctor, pullbackStrictificationFiberForget] using
      (((hc.pullbackIdIso U).app y).symm)
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Helper for Lemma 4.36.4: reindexing along `g` is literal postcomposition on the chosen arrow
tag of a strictification object. -/
noncomputable def pullbackStrictificationReindexObj
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U) :
    PullbackStrictificationFiber p hc U → PullbackStrictificationFiber p hc V
  | ⟨target, f, x⟩ => ⟨target, g ≫ f, x⟩

/-- Helper for Lemma 4.36.4: on objects, reindexing along the identity only rewrites
`𝟙 ≫ f` to `f`. -/
theorem pullback_strictification_reindex_obj_id
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p) (U : C)
    (X : PullbackStrictificationFiber p hc U) :
    pullbackStrictificationReindexObj p hc (𝟙 U) X = X := by
  -- The identity reindexing changes only the arrow tag, which simplifies by `Category.id_comp`.
  cases X with
  | mk target arrow fiberObj =>
      simp [pullbackStrictificationReindexObj]

/-- Helper for Lemma 4.36.4: on objects, two successive reindexings are the same as reindexing
once along the composite arrow. -/
theorem pullback_strictification_reindex_obj_comp
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (X : PullbackStrictificationFiber p hc U) :
    pullbackStrictificationReindexObj p hc (g ≫ f) X =
      pullbackStrictificationReindexObj p hc g (pullbackStrictificationReindexObj p hc f X) := by
  -- Both sides keep the same target object and fiber object, and only differ by associativity of
  -- the arrow tag.
  cases X with
  | mk target arrow fiberObj =>
      simp [pullbackStrictificationReindexObj, Category.assoc]

/-- Helper for Lemma 4.36.4: reindexing a vertical morphism uses the chosen pullback functor along
`g`, transported across the comparison isomorphisms for composite pullbacks. -/
noncomputable def pullbackStrictificationReindexMap
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U)
    {X Y : PullbackStrictificationFiber p hc U} (φ : X ⟶ Y) :
    pullbackStrictificationFiberForget p hc V (pullbackStrictificationReindexObj p hc g X) ⟶
      pullbackStrictificationFiberForget p hc V (pullbackStrictificationReindexObj p hc g Y) :=
  ((hc.pullbackCompIso X.arrow g).hom.app X.fiberObj) ≫
    (hc.pullbackFunctor g).map φ ≫
    ((hc.pullbackCompIso Y.arrow g).inv.app Y.fiberObj)

/-- Helper for Lemma 4.36.4: the strict reindexing map sends identities to identities because the
comparison isomorphisms cancel and `g^*` is already a functor on the actual fibers. -/
theorem pullbackStrictificationReindexMap_id
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U) (X : PullbackStrictificationFiber p hc U) :
    pullbackStrictificationReindexMap p hc g (𝟙 X) =
      𝟙 (pullbackStrictificationReindexObj p hc g X) := by
  -- The only data here are the inverse pair of comparison isomorphisms around the identity map of
  -- `g^*`.
  -- After unfolding to the underlying fiber morphism, functoriality gives `g^*(𝟙) = 𝟙` and the
  -- comparison component cancels with its inverse.
  cases X with
  | mk target arrow fiberObj =>
      change (hc.pullbackCompIso arrow g).hom.app fiberObj ≫
            (hc.pullbackFunctor g).map (𝟙 ((hc.pullbackFunctor arrow).obj fiberObj)) ≫
            (hc.pullbackCompIso arrow g).inv.app fiberObj =
          𝟙 ((hc.pullbackFunctor (g ≫ arrow)).obj fiberObj)
      rw [Functor.map_id]
      simpa [Category.assoc] using Iso.hom_inv_id_app (hc.pullbackCompIso arrow g) fiberObj

/-- Helper for Lemma 4.36.4: the strict reindexing map respects composition because both
comparison isomorphisms at the middle object cancel. -/
theorem pullbackStrictificationReindexMap_comp
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (g : V ⟶ U)
    {X Y Z : PullbackStrictificationFiber p hc U} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    pullbackStrictificationReindexMap p hc g (φ ≫ ψ) =
      pullbackStrictificationReindexMap p hc g φ ≫
        pullbackStrictificationReindexMap p hc g ψ := by
  -- After expanding both sides, the middle comparison isomorphisms cancel and `g^*` preserves
  -- composition.
  cases X with
  | mk targetX arrowX fiberObjX =>
      cases Y with
      | mk targetY arrowY fiberObjY =>
          cases Z with
          | mk targetZ arrowZ fiberObjZ =>
              -- Once the strictification data are unpacked, this is the ordinary functoriality
              -- of `g^*` with the middle comparison isomorphism cancelling to the identity.
              change (hc.pullbackCompIso arrowX g).hom.app fiberObjX ≫
                    (hc.pullbackFunctor g).map (φ ≫ ψ) ≫
                    (hc.pullbackCompIso arrowZ g).inv.app fiberObjZ =
                  ((hc.pullbackCompIso arrowX g).hom.app fiberObjX ≫
                      (hc.pullbackFunctor g).map φ ≫
                      (hc.pullbackCompIso arrowY g).inv.app fiberObjY) ≫
                    ((hc.pullbackCompIso arrowY g).hom.app fiberObjY ≫
                      (hc.pullbackFunctor g).map ψ ≫
                      (hc.pullbackCompIso arrowZ g).inv.app fiberObjZ)
              rw [Functor.map_comp]
              have hmid :
                  (hc.pullbackCompIso arrowY g).inv.app fiberObjY ≫
                      (hc.pullbackCompIso arrowY g).hom.app fiberObjY ≫
                      ((hc.pullbackFunctor g).map ψ ≫
                        (hc.pullbackCompIso arrowZ g).inv.app fiberObjZ) =
                    (hc.pullbackFunctor g).map ψ ≫
                      (hc.pullbackCompIso arrowZ g).inv.app fiberObjZ := by
                simpa [Category.assoc] using
                  Iso.inv_hom_id_assoc ((hc.pullbackCompIso arrowY g).app fiberObjY)
                    ((hc.pullbackFunctor g).map ψ ≫
                      (hc.pullbackCompIso arrowZ g).inv.app fiberObjZ)
              have hcancel := congrArg
                (fun k ↦ (hc.pullbackCompIso arrowX g).hom.app fiberObjX ≫
                  (hc.pullbackFunctor g).map φ ≫ k)
                hmid
              have hcancel' := hcancel.symm
              simpa [Category.assoc] using hcancel'

/-- Helper for Lemma 4.36.4: after forgetting to the total category, the chosen pullback functor
map factors through the chosen pullback arrow exactly as in the standard fiber. -/
theorem pullback_strictification_pullbackFunctor_map_fac
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y =
      hc.map f x ≫ φ.1 := by
  -- Unfold the chosen pullback map as the universal morphism into the strongly cartesian lift.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift f (hc.map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f (hc.map f x) U φ.1
  -- The factorization property of the chosen pullback map is exactly the desired equality.
  change IsStronglyCartesian.map p f (hc.map f y) (Category.id_comp f).symm
      (hc.map f x ≫ φ.1) ≫ hc.map f y = hc.map f x ≫ φ.1
  simpa using
    (IsStronglyCartesian.fac p f (hc.map f y) (Category.id_comp f).symm (hc.map f x ≫ φ.1))

/-- Helper for Lemma 4.36.4: transporting between equal pullback arrows induces the corresponding
transport map between the chosen pullback objects, and postcomposing with the chosen pullback arrow
recovers the original comparison map in the total category. -/
theorem pullback_strictification_eqToHom_component_postcompose_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} {f g : V ⟶ U} (e : f = g) (x : Fiber p U) :
    Fiber.fiberInclusion.map ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) e)).app x) ≫
        hc.map g x =
      hc.map f x := by
  -- In the reflexive case the transported comparison is the identity, so the claim is tautological.
  cases e
  simp

/-- Helper for Lemma 4.36.4: a morphism into a chosen pullback object is determined by its
postcomposition with the chosen strongly cartesian pullback arrow. -/
theorem pullback_strictification_hom_ext
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V : C} (f : V ⟶ U) {x : Fiber p U} {y : Fiber p V}
    {ψ ψ' : y ⟶ (hc.pullbackFunctor f).obj x}
    (h : ψ.1 ≫ hc.map f x = ψ'.1 ≫ hc.map f x) :
    ψ = ψ' := by
  -- Forget to the total category and compare the two lifts into the same chosen strongly
  -- cartesian morphism.
  apply Fiber.hom_ext
  change ψ.1 = ψ'.1
  letI : p.IsHomLift (𝟙 V) ψ.1 := ψ.2
  letI : p.IsHomLift (𝟙 V) ψ'.1 := ψ'.2
  have hψlift : p.IsHomLift (𝟙 V) ψ.1 := inferInstance
  have hψ'lift : p.IsHomLift (𝟙 V) ψ'.1 := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f (hc.map f x) inferInstance _ _ (𝟙 V) ψ.1 ψ'.1 hψlift hψ'lift h

/-- Helper for Lemma 4.36.4: the source identity-comparison chain postcomposes with the chosen
pullback arrow exactly to the expected composite pullback map. -/
theorem pullback_strictification_id_source_transport_postcompose_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
          (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
          hc.map f x =
      hc.map (𝟙 U ≫ f) x := by
  -- Unfold the identity comparison to `hc.map (𝟙 U)` and then apply the composition comparison
  -- factorization.
  have hstep1 :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
            (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
            hc.map f x
        =
      ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫
        hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
          hc.map f x := by
    rw [Functor.map_comp]
    simpa [PullbackChoice.pullbackIdIso, Category.assoc] using
      congrArg
        (fun k ↦ ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫ k ≫ hc.map f x)
        (hc.pullbackIdComponentIso_inv_eq U ((hc.pullbackFunctor f).obj x))
  have hstep2 :
      ((hc.pullbackCompIso f (𝟙 U)).hom.app x).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    simpa [PullbackChoice.pullbackCompIso, Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := f) (g := 𝟙 U) x
  exact hstep1.trans hstep2

/-- Helper for Lemma 4.36.4: the target identity-comparison chain postcomposes with the chosen
composite pullback arrow to the original chosen pullback map. -/
theorem pullback_strictification_id_target_transport_postcompose_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
          (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
          hc.map (𝟙 U ≫ f) x =
      hc.map f x := by
  -- Move the composite comparison through the chosen pullback map and then contract the identity
  -- pullback component.
  have hstep1 :
      Fiber.fiberInclusion.map
          ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
            (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
            hc.map (𝟙 U ≫ f) x
        =
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
        hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
          hc.map f x := by
    rw [Functor.map_comp]
    simpa [PullbackChoice.pullbackIdIso, Category.assoc] using
      congrArg
        (fun k ↦ ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫ k)
        (hc.pullbackCompComponentIso_inv_fac (f := f) (g := 𝟙 U) x)
  have hstep2 :
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
          hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
            hc.map f x =
        hc.map f x := by
    have hfac :
        ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
            hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) =
          𝟙 ((hc.pullbackFunctor f).obj x).1 := by
      simpa [PullbackChoice.pullbackIdIso] using
        (hc.pullbackIdComponentIso_fac U ((hc.pullbackFunctor f).obj x))
    calc
      ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
            hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x) ≫
              hc.map f x
          =
        (((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x)).1 ≫
              hc.map (𝟙 U) ((hc.pullbackFunctor f).obj x)) ≫
            hc.map f x := by
              simp [Category.assoc]
      _ = hc.map f x := by
            rw [hfac]
            simp
  exact hstep1.trans hstep2

/-- Helper for Lemma 4.36.4: the transport from `(𝟙 U ≫ f)^* x` to `f^* x` induced by
`Category.id_comp` is the explicit source comparison chain. -/
theorem pullback_strictification_id_eqToHom
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)) =
      (hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
        (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x) := by
  -- Compare the two transport morphisms after postcomposition with the chosen pullback arrow.
  apply pullback_strictification_hom_ext p hc f
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f))) ≫
          hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    have htmp :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) (Category.id_comp f))).app x) ≫
            hc.map f x =
          hc.map (𝟙 U ≫ f) x := by
      exact
        (pullback_strictification_eqToHom_component_postcompose_eq
          (p := p) (hc := hc) (f := 𝟙 U ≫ f) (g := f)
          (e := Category.id_comp f) (x := x))
    simpa using htmp
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f (𝟙 U)).hom.app x ≫
            (hc.pullbackIdIso U).inv.app ((hc.pullbackFunctor f).obj x)) ≫
          hc.map f x =
        hc.map (𝟙 U ≫ f) x := by
    have htransport :=
      (pullback_strictification_id_source_transport_postcompose_eq
        (p := p) (hc := hc) (f := f) (x := x))
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.4: the inverse of the identity-reindexing object equality is
represented on the forgotten fiber object by the target transport chain. -/
theorem pullback_strictification_id_eqToHom_symm
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U T : C} (f : U ⟶ T) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)).symm =
      (hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
        (hc.pullbackCompIso f (𝟙 U)).inv.app x := by
  -- Compare the two inverse transports after postcomposition with the composite pullback arrow.
  apply pullback_strictification_hom_ext p hc (𝟙 U ≫ f)
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.id_comp f)).symm) ≫
          hc.map (𝟙 U ≫ f) x =
        hc.map f x := by
    have htmp :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) (Category.id_comp f)).symm).app x) ≫
            hc.map (𝟙 U ≫ f) x =
          hc.map f x := by
      exact
        (pullback_strictification_eqToHom_component_postcompose_eq
          (p := p) (hc := hc) (f := f) (g := 𝟙 U ≫ f)
          (e := (Category.id_comp f).symm) (x := x))
    simpa using htmp
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackIdIso U).hom.app ((hc.pullbackFunctor f).obj x) ≫
            (hc.pullbackCompIso f (𝟙 U)).inv.app x) ≫
          hc.map (𝟙 U ≫ f) x =
        hc.map f x := by
    have htransport :=
      (pullback_strictification_id_target_transport_postcompose_eq
        (p := p) (hc := hc) (f := f) (x := x))
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.4: the comparison isomorphism for composite pullbacks is natural after
postcomposing with the inverse comparison component on the target. -/
theorem pullback_strictification_compIso_naturality_inv
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) {x y : Fiber p U} (φ : x ⟶ y) :
    (hc.pullbackCompIso f g).hom.app x ≫
        ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) ≫
        (hc.pullbackCompIso f g).inv.app y =
      (hc.pullbackFunctor (g ≫ f)).map φ := by
  -- The forward naturality square becomes the desired equality after cancelling the target
  -- comparison isomorphism.
  have hnatRaw := (hc.pullbackCompIso f g).hom.naturality φ
  have hcancel :
      (hc.pullbackCompIso f g).hom.app y ≫ (hc.pullbackCompIso f g).inv.app y =
        𝟙 ((hc.pullbackFunctor (g ≫ f)).obj y) := by
    simpa using Iso.hom_inv_id_app (hc.pullbackCompIso f g) y
  calc
    (hc.pullbackCompIso f g).hom.app x ≫
          ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) ≫
          (hc.pullbackCompIso f g).inv.app y
        =
      ((hc.pullbackFunctor (g ≫ f)).map φ ≫
          (hc.pullbackCompIso f g).hom.app y) ≫
          (hc.pullbackCompIso f g).inv.app y := by
            simpa [Functor.comp_map, Category.assoc] using
              congrArg (fun k ↦ k ≫ (hc.pullbackCompIso f g).inv.app y) hnatRaw.symm
    _ = (hc.pullbackFunctor (g ≫ f)).map φ := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (hc.pullbackFunctor (g ≫ f)).map φ ≫ k) hcancel

/-- Helper for Lemma 4.36.4: the associativity transport chain from the left-associated chosen
pullback to the right-associated chosen pullback postcomposes with the target pullback arrow to
the original left-associated pullback map. -/
theorem pullback_strictification_comp_source_transport_postcompose_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T U V W : C} (a : U ⟶ T) (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackCompIso a (g ≫ f)).hom.app x ≫
          (hc.pullbackCompIso f g).hom.app ((hc.pullbackFunctor a).obj x) ≫
          (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).inv.app x) ≫
          (hc.pullbackCompIso (f ≫ a) g).inv.app x) ≫
        hc.map (g ≫ f ≫ a) x =
      hc.map ((g ≫ f) ≫ a) x := by
  -- Collapse the four comparison factors one by one after forgetting to the ambient category.
  have h4 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso (f ≫ a) g).inv.app x) ≫
          hc.map (g ≫ f ≫ a) x =
        hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫ hc.map (f ≫ a) x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_inv_fac (f := f ≫ a) (g := g) x
  have h3 :
      Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).inv.app x)) ≫
          hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) =
        hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
          Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).inv.app x) := by
    simpa [Category.assoc] using
      pullback_strictification_pullbackFunctor_map_fac
        (p := p) (hc := hc) g ((hc.pullbackCompIso a f).inv.app x)
  have h2 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).inv.app x) ≫ hc.map (f ≫ a) x =
        hc.map f ((hc.pullbackFunctor a).obj x) ≫ hc.map a x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_inv_fac (f := a) (g := f) x
  have hcomp :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f g).hom.app ((hc.pullbackFunctor a).obj x)) ≫
          hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
          hc.map f ((hc.pullbackFunctor a).obj x) =
        hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x) := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := f) (g := g) ((hc.pullbackFunctor a).obj x)
  have h1 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso a (g ≫ f)).hom.app x) ≫
          hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x) ≫
          hc.map a x =
        hc.map ((g ≫ f) ≫ a) x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := a) (g := g ≫ f) x
  let α₁ := Fiber.fiberInclusion.map ((hc.pullbackCompIso a (g ≫ f)).hom.app x)
  let α₂ := Fiber.fiberInclusion.map
    ((hc.pullbackCompIso f g).hom.app ((hc.pullbackFunctor a).obj x))
  let α₃ := Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).inv.app x))
  let α₄ := Fiber.fiberInclusion.map ((hc.pullbackCompIso (f ≫ a) g).inv.app x)
  have hmain :
      α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ hc.map (g ≫ f ≫ a) x =
        hc.map ((g ≫ f) ≫ a) x := by
    calc
      α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ hc.map (g ≫ f ≫ a) x
          = α₁ ≫ α₂ ≫ α₃ ≫ (α₄ ≫ hc.map (g ≫ f ≫ a) x) := by
              simp
      _ = α₁ ≫ α₂ ≫ α₃ ≫
            (hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫ hc.map (f ≫ a) x) := by
            exact congrArg (fun k ↦ α₁ ≫ α₂ ≫ α₃ ≫ k) h4
      _ = α₁ ≫ α₂ ≫ (α₃ ≫ hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x)) ≫
            hc.map (f ≫ a) x := by
            simp [Category.assoc]
      _ = α₁ ≫ α₂ ≫
            (hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
              Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).inv.app x)) ≫
            hc.map (f ≫ a) x := by
            exact congrArg (fun k ↦ α₁ ≫ α₂ ≫ k ≫ hc.map (f ≫ a) x) h3
      _ = α₁ ≫ α₂ ≫ hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
            Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).inv.app x) ≫
            hc.map (f ≫ a) x := by
            simp [Category.assoc]
      _ = α₁ ≫ α₂ ≫ hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
            (hc.map f ((hc.pullbackFunctor a).obj x) ≫ hc.map a x) := by
            exact congrArg
              (fun k ↦ α₁ ≫ α₂ ≫ hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
                k) h2
      _ = α₁ ≫
            (α₂ ≫ hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
              hc.map f ((hc.pullbackFunctor a).obj x)) ≫
            hc.map a x := by
            simp [Category.assoc]
      _ = α₁ ≫ hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x) ≫ hc.map a x := by
            exact congrArg (fun k ↦ α₁ ≫ k ≫ hc.map a x) hcomp
      _ = hc.map ((g ≫ f) ≫ a) x := h1
  simpa [α₁, α₂, α₃, α₄, Category.assoc] using hmain

/-- Helper for Lemma 4.36.4: the associativity transport chain from the right-associated chosen
pullback to the left-associated chosen pullback postcomposes with the left-associated pullback
arrow to the expected right-associated pullback map. -/
theorem pullback_strictification_comp_target_transport_postcompose_eq
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T U V W : C} (a : U ⟶ T) (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p T) :
    Fiber.fiberInclusion.map
        ((hc.pullbackCompIso (f ≫ a) g).hom.app x ≫
          (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) ≫
          (hc.pullbackCompIso f g).inv.app ((hc.pullbackFunctor a).obj x) ≫
          (hc.pullbackCompIso a (g ≫ f)).inv.app x) ≫
        hc.map ((g ≫ f) ≫ a) x =
      hc.map (g ≫ f ≫ a) x := by
  -- Reverse the previous collapse chain by pushing the chosen pullback map through each
  -- comparison isomorphism from right to left.
  have h4 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso a (g ≫ f)).inv.app x) ≫
          hc.map ((g ≫ f) ≫ a) x =
        hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x) ≫ hc.map a x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_inv_fac (f := a) (g := g ≫ f) x
  have h3 :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso f g).inv.app ((hc.pullbackFunctor a).obj x)) ≫
          hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x) =
        hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
          hc.map f ((hc.pullbackFunctor a).obj x) := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_inv_fac (f := f) (g := g) ((hc.pullbackFunctor a).obj x)
  have h2 :
      Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x)) ≫
          hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) =
        hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫
          Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).hom.app x) := by
    simpa [Category.assoc] using
      pullback_strictification_pullbackFunctor_map_fac
        (p := p) (hc := hc) g ((hc.pullbackCompIso a f).hom.app x)
  have h1 :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso (f ≫ a) g).hom.app x) ≫
          hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫
          hc.map (f ≫ a) x =
        hc.map (g ≫ f ≫ a) x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := f ≫ a) (g := g) x
  have hcomp :
      Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).hom.app x) ≫ hc.map f ((hc.pullbackFunctor a).obj x) ≫
          hc.map a x =
        hc.map (f ≫ a) x := by
    simpa [Category.assoc] using
      hc.pullbackCompComponentIso_fac (f := a) (g := f) x
  let α₁ := Fiber.fiberInclusion.map ((hc.pullbackCompIso (f ≫ a) g).hom.app x)
  let α₂ := Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x))
  let α₃ := Fiber.fiberInclusion.map
    ((hc.pullbackCompIso f g).inv.app ((hc.pullbackFunctor a).obj x))
  let α₄ := Fiber.fiberInclusion.map ((hc.pullbackCompIso a (g ≫ f)).inv.app x)
  have hmain :
      α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ hc.map ((g ≫ f) ≫ a) x =
        hc.map (g ≫ f ≫ a) x := by
    calc
      α₁ ≫ α₂ ≫ α₃ ≫ α₄ ≫ hc.map ((g ≫ f) ≫ a) x
          = α₁ ≫ α₂ ≫ α₃ ≫ (α₄ ≫ hc.map ((g ≫ f) ≫ a) x) := by
              simp
      _ = α₁ ≫ α₂ ≫ α₃ ≫
            (hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x) ≫ hc.map a x) := by
            exact congrArg (fun k ↦ α₁ ≫ α₂ ≫ α₃ ≫ k) h4
      _ = α₁ ≫ α₂ ≫
            (α₃ ≫ hc.map (g ≫ f) ((hc.pullbackFunctor a).obj x)) ≫
            hc.map a x := by
            simp [Category.assoc]
      _ = α₁ ≫ α₂ ≫
            (hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x)) ≫
              hc.map f ((hc.pullbackFunctor a).obj x)) ≫
            hc.map a x := by
            exact congrArg (fun k ↦ α₁ ≫ α₂ ≫ k ≫ hc.map a x) h3
      _ = α₁ ≫ (α₂ ≫ hc.map g ((hc.pullbackFunctor f).obj ((hc.pullbackFunctor a).obj x))) ≫
            hc.map f ((hc.pullbackFunctor a).obj x) ≫
            hc.map a x := by
            simp [Category.assoc]
      _ = α₁ ≫
            (hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫
              Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).hom.app x)) ≫
            hc.map f ((hc.pullbackFunctor a).obj x) ≫
            hc.map a x := by
            exact congrArg
              (fun k ↦ α₁ ≫ k ≫ hc.map f ((hc.pullbackFunctor a).obj x) ≫ hc.map a x) h2
      _ = α₁ ≫ hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫
            Fiber.fiberInclusion.map ((hc.pullbackCompIso a f).hom.app x) ≫
            hc.map f ((hc.pullbackFunctor a).obj x) ≫
            hc.map a x := by
            simp [Category.assoc]
      _ = α₁ ≫ hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫ hc.map (f ≫ a) x := by
            exact congrArg
              (fun k ↦ α₁ ≫ hc.map g ((hc.pullbackFunctor (f ≫ a)).obj x) ≫ k) hcomp
      _ = hc.map (g ≫ f ≫ a) x := h1
  simpa [α₁, α₂, α₃, α₄, Category.assoc] using hmain

/-- Helper for Lemma 4.36.4: the transport from `(((g ≫ f) ≫ a)^* x)` to `(g ≫ (f ≫ a))^* x`
induced by `Category.assoc` is the explicit source comparison chain. -/
theorem pullback_strictification_comp_eqToHom
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T U V W : C} (a : U ⟶ T) (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.assoc g f a)) =
      (hc.pullbackCompIso a (g ≫ f)).hom.app x ≫
        (hc.pullbackCompIso f g).hom.app ((hc.pullbackFunctor a).obj x) ≫
        (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).inv.app x) ≫
        (hc.pullbackCompIso (f ≫ a) g).inv.app x := by
  -- Compare both candidate transports after postcomposition with the chosen pullback arrow for the
  -- right-associated composite.
  apply pullback_strictification_hom_ext p hc (g ≫ f ≫ a)
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.assoc g f a))) ≫
          hc.map (g ≫ f ≫ a) x =
        hc.map ((g ≫ f) ≫ a) x := by
    have htmp :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k) (Category.assoc g f a))).app x) ≫
            hc.map (g ≫ f ≫ a) x =
          hc.map ((g ≫ f) ≫ a) x := by
      exact
        (pullback_strictification_eqToHom_component_postcompose_eq
          (p := p) (hc := hc) (f := (g ≫ f) ≫ a) (g := g ≫ f ≫ a)
          (e := Category.assoc g f a) (x := x))
    simpa using htmp
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso a (g ≫ f)).hom.app x ≫
            (hc.pullbackCompIso f g).hom.app ((hc.pullbackFunctor a).obj x) ≫
            (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).inv.app x) ≫
            (hc.pullbackCompIso (f ≫ a) g).inv.app x) ≫
          hc.map (g ≫ f ≫ a) x =
        hc.map ((g ≫ f) ≫ a) x := by
    have htransport :=
      pullback_strictification_comp_source_transport_postcompose_eq
        (p := p) (hc := hc) (a := a) (f := f) (g := g) (x := x)
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

/-- Helper for Lemma 4.36.4: the inverse of the associativity transport from
`(((g ≫ f) ≫ a)^* x)` to `(g ≫ (f ≫ a))^* x` is the explicit target comparison chain. -/
theorem pullback_strictification_comp_eqToHom_symm
    (p : S ⥤ C) [p.IsFibered] (hc : PullbackChoice p)
    {T U V W : C} (a : U ⟶ T) (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p T) :
    eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.assoc g f a)).symm =
      (hc.pullbackCompIso (f ≫ a) g).hom.app x ≫
        (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) ≫
        (hc.pullbackCompIso f g).inv.app ((hc.pullbackFunctor a).obj x) ≫
        (hc.pullbackCompIso a (g ≫ f)).inv.app x := by
  -- Compare the inverse transport and the explicit target comparison after postcomposition with
  -- the left-associated chosen pullback arrow.
  apply pullback_strictification_hom_ext p hc (((g ≫ f) ≫ a))
  have hleft :
      Fiber.fiberInclusion.map
          (eqToHom (congrArg (fun k ↦ (hc.pullbackFunctor k).obj x) (Category.assoc g f a)).symm) ≫
          hc.map (((g ≫ f) ≫ a)) x =
        hc.map (g ≫ f ≫ a) x := by
    have htmp :
        Fiber.fiberInclusion.map
            ((eqToHom (congrArg (fun k ↦ hc.pullbackFunctor k)
              (Category.assoc g f a)).symm).app x) ≫
            hc.map (((g ≫ f) ≫ a)) x =
          hc.map (g ≫ f ≫ a) x := by
      exact
        (pullback_strictification_eqToHom_component_postcompose_eq
          (p := p) (hc := hc) (f := g ≫ f ≫ a) (g := ((g ≫ f) ≫ a))
          (e := (Category.assoc g f a).symm) (x := x))
    simpa using htmp
  have hright :
      Fiber.fiberInclusion.map
          ((hc.pullbackCompIso (f ≫ a) g).hom.app x ≫
            (hc.pullbackFunctor g).map ((hc.pullbackCompIso a f).hom.app x) ≫
            (hc.pullbackCompIso f g).inv.app ((hc.pullbackFunctor a).obj x) ≫
            (hc.pullbackCompIso a (g ≫ f)).inv.app x) ≫
          hc.map (((g ≫ f) ≫ a)) x =
        hc.map (g ≫ f ≫ a) x := by
    have htransport :=
      pullback_strictification_comp_target_transport_postcompose_eq
        (p := p) (hc := hc) (a := a) (f := f) (g := g) (x := x)
    rw [Functor.map_comp] at htransport
    simpa [Category.assoc] using htransport
  exact hleft.trans hright.symm

end CategoryTheory
