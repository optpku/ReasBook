module

public import stacks_project.Chap04.CanonicalPullbackChoice
public import stacks_project.Chap04.Definition_4_33_6

@[expose] public section

/-!
# Canonical fiber pseudofunctor comparison package

This slim owner keeps the source-text parts (1) to (4) of Lemma 4.33.7 together: the chosen
comparison isomorphisms for composite pullbacks and identities, together with their uniqueness
characterizations. Downstream files that only need the comparison package should import this file
instead of the monolithic compatibility owner.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace PullbackChoice

variable {p : S ⥤ C} (hc : PullbackChoice p)

/-- The component at `x` of the comparison isomorphism
`(g ≫ f)^* ≅ f^* ⋙ g^*` from Lemma 4.33.7 (1). -/
noncomputable def pullbackCompComponentIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (g ≫ f) ^*[hc] x ≅ g ^*[hc] (f ^*[hc] x) :=
  let _ : p.IsFibered := hc.isFibered
  let e := IsCartesian.domainUniqueUpToIso p (g ≫ f)
    (hc.map g (f ^*[hc] x) ≫ hc.map f x)
    (hc.map (g ≫ f) x)
  { hom := ⟨e.hom, inferInstance⟩
    inv := ⟨e.inv, inferInstance⟩
    hom_inv_id := by
      apply Fiber.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      apply Fiber.hom_ext
      exact e.inv_hom_id }

-- Proof sketch: the chosen component is the morphism furnished by uniqueness of morphisms into the
-- strongly cartesian arrow `hc.map g (f ^*[hc] x) ≫ hc.map f x`, so its defining factorization is
-- exactly the commutative square from the textbook statement.
/-- The comparison component for iterated pullback factors the chosen pullback morphisms through the
same map to `x`. -/
theorem pullbackCompComponentIso_fac
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (hc.pullbackCompComponentIso f g x).hom.1 ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x =
      hc.map (g ≫ f) x := by
  -- Unfold the comparison isomorphism and read off the defining factorization of its hom.
  simpa only [pullbackCompComponentIso] using
    (IsCartesian.fac p (g ≫ f) (hc.map g (f ^*[hc] x) ≫ hc.map f x) (hc.map (g ≫ f) x))

/-- Helper for Lemma 4.33.7: the inverse composition comparison component factors the chosen
composite pullback map through the iterated pullback maps. -/
theorem pullbackCompComponentIso_inv_fac
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (hc.pullbackCompComponentIso f g x).inv.1 ≫ hc.map (g ≫ f) x =
      hc.map g (f ^*[hc] x) ≫ hc.map f x := by
  -- Insert the hom-factorization and cancel the inverse-hom pair of the comparison isomorphism.
  have hIso :
      (hc.pullbackCompComponentIso f g x).inv.1 ≫ (hc.pullbackCompComponentIso f g x).hom.1 =
        𝟙 (((g ^*[hc] (f ^*[hc] x))).1) := by
    exact congrArg (fun k ↦ k.1) (hc.pullbackCompComponentIso f g x).inv_hom_id
  calc
    (hc.pullbackCompComponentIso f g x).inv.1 ≫ hc.map (g ≫ f) x
        = (hc.pullbackCompComponentIso f g x).inv.1 ≫
            ((hc.pullbackCompComponentIso f g x).hom.1 ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x) := by
              rw [hc.pullbackCompComponentIso_fac]
    _ = ((hc.pullbackCompComponentIso f g x).inv.1 ≫ (hc.pullbackCompComponentIso f g x).hom.1) ≫
          hc.map g (f ^*[hc] x) ≫ hc.map f x := by
            simp [Category.assoc]
    _ = hc.map g (f ^*[hc] x) ≫ hc.map f x := by
          rw [hIso]
          simp

/-- Helper for Lemma 4.33.7: the chosen pullback functor map factors through the chosen pullback
arrow. This is public because the coherence owner reuses the same factorization route rather than
rebuilding it. -/
theorem pullbackFunctor_map_fac
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    ((hc.pullbackFunctor f).map φ).1 ≫ hc.map f y = hc.map f x ≫ φ.1 := by
  -- Unfold the pullback map as the universal arrow induced by strong cartesianness.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  letI : p.IsHomLift f (hc.map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f (hc.map f x) U φ.1
  change IsStronglyCartesian.map p f (hc.map f y) (Category.id_comp f).symm (hc.map f x ≫ φ.1) ≫
      hc.map f y = hc.map f x ≫ φ.1
  simpa using
    (IsStronglyCartesian.fac p f (hc.map f y) (Category.id_comp f).symm (hc.map f x ≫ φ.1))

/-- Helper for Lemma 4.33.7: the two candidate naturality morphisms for the composition
comparison become equal after forgetting to `S` and postcomposing with the chosen composite
strongly cartesian arrow. -/
private theorem pullbackCompIso_postcompose_eq
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) {x y : Fiber p U} (φ : x ⟶ y) :
    Fiber.fiberInclusion.map (((hc.pullbackFunctor (g ≫ f)).map φ) ≫
        (hc.pullbackCompComponentIso f g y).hom) ≫
        hc.map g (f ^*[hc] y) ≫ hc.map f y =
      Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f g x).hom ≫
        ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ)) ≫
        hc.map g (f ^*[hc] y) ≫ hc.map f y := by
  -- Route correction: compare the two ambient arrows only after postcomposition with the chosen
  -- strongly cartesian target, so the `IsHomLift` bookkeeping stays explicit and stable.
  have hleft :
      Fiber.fiberInclusion.map (((hc.pullbackFunctor (g ≫ f)).map φ) ≫
          (hc.pullbackCompComponentIso f g y).hom) ≫
          hc.map g (f ^*[hc] y) ≫ hc.map f y =
        hc.map (g ≫ f) x ≫ φ.1 := by
    have hstep1 :
        Fiber.fiberInclusion.map (((hc.pullbackFunctor (g ≫ f)).map φ) ≫
            (hc.pullbackCompComponentIso f g y).hom) ≫
            hc.map g (f ^*[hc] y) ≫ hc.map f y =
          Fiber.fiberInclusion.map ((hc.pullbackFunctor (g ≫ f)).map φ) ≫ hc.map (g ≫ f) y := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ Fiber.fiberInclusion.map ((hc.pullbackFunctor (g ≫ f)).map φ) ≫ k)
          (hc.pullbackCompComponentIso_fac f g y)
    have hstep2 :
        Fiber.fiberInclusion.map ((hc.pullbackFunctor (g ≫ f)).map φ) ≫ hc.map (g ≫ f) y =
          hc.map (g ≫ f) x ≫ φ.1 := by
      simpa using hc.pullbackFunctor_map_fac (g ≫ f) φ
    exact hstep1.trans hstep2
  have hright :
      Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f g x).hom ≫
          ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ)) ≫
          hc.map g (f ^*[hc] y) ≫ hc.map f y =
        hc.map (g ≫ f) x ≫ φ.1 := by
    have hstep1 :
        Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f g x).hom ≫
            ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ)) ≫
            hc.map g (f ^*[hc] y) ≫ hc.map f y =
          Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
            hc.map g (f ^*[hc] x) ≫
            Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y := by
      have hg :
          Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map φ)) ≫
              hc.map g (f ^*[hc] y) =
            hc.map g (f ^*[hc] x) ≫ Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) := by
        simpa using hc.pullbackFunctor_map_fac g ((hc.pullbackFunctor f).map φ)
      have hstep1a :
          Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f g x).hom ≫
              ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ)) ≫
              hc.map g (f ^*[hc] y) ≫ hc.map f y =
            (Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
                Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map φ))) ≫
              hc.map g (f ^*[hc] y) ≫ hc.map f y := by
        rw [Functor.comp_map]
        rfl
      have hstep1b :
          (Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map φ))) ≫
              hc.map g (f ^*[hc] y) ≫ hc.map f y =
            Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              (Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map φ)) ≫
                hc.map g (f ^*[hc] y)) ≫ hc.map f y := by
        simp [Category.assoc]
      have hstep1c :
          Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              (Fiber.fiberInclusion.map ((hc.pullbackFunctor g).map ((hc.pullbackFunctor f).map φ)) ≫
                hc.map g (f ^*[hc] y)) ≫ hc.map f y =
            Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              (hc.map g (f ^*[hc] x) ≫ Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ)) ≫
              hc.map f y := by
        exact
          congrArg
            (fun k ↦ Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              k ≫ hc.map f y)
            hg
      have hstep1d :
          Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              (hc.map g (f ^*[hc] x) ≫ Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ)) ≫
              hc.map f y =
            Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
              hc.map g (f ^*[hc] x) ≫
              Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y := by
        simp [Category.assoc]
      exact hstep1a.trans (hstep1b.trans (hstep1c.trans hstep1d))
    have hstep2 :
        Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
            hc.map g (f ^*[hc] x) ≫
            Fiber.fiberInclusion.map ((hc.pullbackFunctor f).map φ) ≫ hc.map f y =
          Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
            hc.map g (f ^*[hc] x) ≫ hc.map f x ≫ φ.1 := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
            hc.map g (f ^*[hc] x) ≫ k)
          (hc.pullbackFunctor_map_fac f φ)
    have hstep3 :
        Fiber.fiberInclusion.map (hc.pullbackCompComponentIso f g x).hom ≫
            hc.map g (f ^*[hc] x) ≫ hc.map f x ≫ φ.1 =
          hc.map (g ≫ f) x ≫ φ.1 := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ φ.1) (hc.pullbackCompComponentIso_fac f g x)
    exact hstep1.trans (hstep2.trans hstep3)
  exact hleft.trans hright.symm

-- Proof sketch: both sides are morphisms in the fiber over `W`; after forgetting to the total
-- category, they are the unique morphisms compatible with the factorization property of the two
-- chosen strongly cartesian lifts, so equality follows from uniqueness.
theorem pullbackCompIso_naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    ∀ {x y : Fiber p U} (φ : x ⟶ y),
      (hc.pullbackFunctor (g ≫ f)).map φ ≫
          (hc.pullbackCompComponentIso f g y).hom =
        (hc.pullbackCompComponentIso f g x).hom ≫
          ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ) := by
  intro x y φ
  -- Compare the two fiber morphisms after forgetting to the ambient category.
  apply Fiber.hom_ext
  let ψ :=
    Fiber.fiberInclusion.map (((hc.pullbackFunctor (g ≫ f)).map φ) ≫
      (hc.pullbackCompComponentIso f g y).hom)
  let ψ' :=
    Fiber.fiberInclusion.map ((hc.pullbackCompComponentIso f g x).hom ≫
      ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ))
  letI : p.IsHomLift (𝟙 W) ψ := by
    dsimp [ψ]
    exact (((hc.pullbackFunctor (g ≫ f)).map φ) ≫ (hc.pullbackCompComponentIso f g y).hom).2
  letI : p.IsHomLift (𝟙 W) ψ' := by
    dsimp [ψ']
    exact ((hc.pullbackCompComponentIso f g x).hom ≫
      ((hc.pullbackFunctor f ⋙ hc.pullbackFunctor g).map φ)).2
  -- The postcomposition helper packages the common factorization into the chosen lift to `y`.
  change ψ = ψ'
  have hψ : p.IsHomLift (𝟙 W) ψ := inferInstance
  have hψ' : p.IsHomLift (𝟙 W) ψ' := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (g ≫ f) (hc.map g (f ^*[hc] y) ≫ hc.map f y) inferInstance _ _ (𝟙 W) ψ ψ' hψ hψ'
      (by exact hc.pullbackCompIso_postcompose_eq f g φ)

/-- Lemma 4.33.7 (1): for composable morphisms `f : V ⟶ U` and `g : W ⟶ V`, a chosen pullback
system on the fibred category `p : S ⥤ C` provides the canonical isomorphism
`(g ≫ f)^* ≅ f^* ⋙ g^*` between pullback functors on the standard fibers. -/
noncomputable def pullbackCompIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    hc.pullbackFunctor (g ≫ f) ≅ hc.pullbackFunctor f ⋙ hc.pullbackFunctor g :=
  NatIso.ofComponents (hc.pullbackCompComponentIso f g) (hc.pullbackCompIso_naturality f g)

-- Proof sketch: the source-text commuting square determines each component uniquely in the fiber
-- over `W`, hence two comparison isomorphisms with the stated factorization property agree
-- componentwise and therefore as natural isomorphisms.
/-- Helper for Lemma 4.33.7 (1): the comparison isomorphism `(g ≫ f)^* ≅ f^* ⋙ g^*`
is uniquely determined by the requirement that each component factors the chosen pullback
morphisms through the same map to the original object. -/
theorem pullbackCompIso_unique
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (α : hc.pullbackFunctor (g ≫ f) ≅ hc.pullbackFunctor f ⋙ hc.pullbackFunctor g)
    (hα : ∀ x : Fiber p U,
      (α.hom.app x).1 ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x = hc.map (g ≫ f) x) :
    α = hc.pullbackCompIso f g := by
  -- The defining commuting triangle determines each comparison component uniquely in the fiber.
  ext x
  let ψ := Fiber.fiberInclusion.map (α.hom.app x)
  let ψ' := Fiber.fiberInclusion.map ((hc.pullbackCompIso f g).hom.app x)
  letI : p.IsHomLift (𝟙 W) ψ := by
    dsimp [ψ]
    exact (α.hom.app x).2
  letI : p.IsHomLift (𝟙 W) ψ' := by
    dsimp [ψ', pullbackCompIso]
    exact (hc.pullbackCompComponentIso f g x).hom.2
  change ψ = ψ'
  have hψ : ψ ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x = hc.map (g ≫ f) x := by
    simpa [ψ] using hα x
  have hψ' : ψ' ≫ hc.map g (f ^*[hc] x) ≫ hc.map f x = hc.map (g ≫ f) x := by
    simpa [ψ', pullbackCompIso] using hc.pullbackCompComponentIso_fac f g x
  have hψlift : p.IsHomLift (𝟙 W) ψ := inferInstance
  have hψ'lift : p.IsHomLift (𝟙 W) ψ' := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (g ≫ f) (hc.map g (f ^*[hc] x) ≫ hc.map f x) inferInstance _ _ (𝟙 W) ψ ψ'
      hψlift hψ'lift (hψ.trans hψ'.symm)

-- Proof sketch: the identity of an object in the fiber lies over `𝟙 U` and is an isomorphism, so
-- the standard fact that isomorphisms over a base morphism are strongly cartesian applies.
theorem fiberId_isStronglyCartesian
    (U : C) (x : Fiber p U) :
    p.IsStronglyCartesian (𝟙 U) (𝟙 (x.1)) := by
  -- The identity in the fiber is an isomorphism over the identity in the base.
  letI : p.IsHomLift (𝟙 U) (𝟙 (x.1)) := by
    change p.IsHomLift (𝟙 U) ((𝟙 x : x ⟶ x).1)
    exact (𝟙 x : x ⟶ x).2
  exact IsStronglyCartesian.of_isIso p (𝟙 U) (𝟙 (x.1))

/-- The component at `x` of the unit comparison `α_U : 𝟭 ≅ (𝟙 U)^*` from Lemma 4.33.7 (2). -/
noncomputable def pullbackIdComponentIso
    (U : C) (x : Fiber p U) :
    x ≅ (𝟙 U) ^*[hc] x :=
  let _ : p.IsFibered := hc.isFibered
  let _ : p.IsStronglyCartesian (𝟙 U) (𝟙 (x.1)) := fiberId_isStronglyCartesian U x
  let _ : p.IsCartesian (𝟙 U) (𝟙 (x.1)) := inferInstance
  let e := IsCartesian.domainUniqueUpToIso p (𝟙 U) (hc.map (𝟙 U) x) (𝟙 (x.1))
  { hom := ⟨e.hom, inferInstance⟩
    inv := ⟨e.inv, inferInstance⟩
    hom_inv_id := by
      apply Fiber.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      apply Fiber.hom_ext
      exact e.inv_hom_id }

-- Proof sketch: the identity of `x` and the chosen pullback arrow `hc.map (𝟙 U) x` are both
-- strongly cartesian over `𝟙 U`, so the chosen comparison component is characterized by the
-- displayed triangle and hence satisfies the required factorization equality.
/-- The identity-pullback comparison component factors the chosen pullback arrow through the
identity of `x`. -/
theorem pullbackIdComponentIso_fac
    (U : C) (x : Fiber p U) :
    (hc.pullbackIdComponentIso U x).hom.1 ≫ hc.map (𝟙 U) x = 𝟙 (x.1) := by
  -- Unfold the comparison isomorphism and read off the defining factorization of its hom.
  letI : p.IsHomLift (𝟙 U) (𝟙 (x.1)) := by
    change p.IsHomLift (𝟙 U) ((𝟙 x : x ⟶ x).1)
    exact (𝟙 x : x ⟶ x).2
  simpa only [pullbackIdComponentIso] using
    (IsCartesian.fac p (𝟙 U) (hc.map (𝟙 U) x) (𝟙 (x.1)))

/-- Helper for Lemma 4.33.7: the inverse unit comparison component is the chosen identity
pullback map. -/
theorem pullbackIdComponentIso_inv_eq
    (U : C) (x : Fiber p U) :
    (hc.pullbackIdComponentIso U x).inv.1 = hc.map (𝟙 U) x := by
  -- Insert the defining triangle for the hom and cancel the inverse-hom pair.
  have hIso :
      (hc.pullbackIdComponentIso U x).inv.1 ≫ (hc.pullbackIdComponentIso U x).hom.1 =
        𝟙 (((𝟙 U) ^*[hc] x).1) := by
    exact congrArg (fun k ↦ k.1) (hc.pullbackIdComponentIso U x).inv_hom_id
  calc
    (hc.pullbackIdComponentIso U x).inv.1
        = (hc.pullbackIdComponentIso U x).inv.1 ≫
            ((hc.pullbackIdComponentIso U x).hom.1 ≫ hc.map (𝟙 U) x) := by
              rw [hc.pullbackIdComponentIso_fac]
              simp
    _ = ((hc.pullbackIdComponentIso U x).inv.1 ≫ (hc.pullbackIdComponentIso U x).hom.1) ≫
          hc.map (𝟙 U) x := by
            simp [Category.assoc]
    _ = hc.map (𝟙 U) x := by
          rw [hIso]
          simp

/-- Helper for Lemma 4.33.7: the two candidate naturality morphisms for the unit comparison become
equal after forgetting to `S` and postcomposing with the chosen identity pullback arrow. -/
private theorem pullbackIdIso_postcompose_eq
    (U : C) {x y : Fiber p U} (φ : x ⟶ y) :
    Fiber.fiberInclusion.map (φ ≫ (hc.pullbackIdComponentIso U y).hom) ≫ hc.map (𝟙 U) y =
      Fiber.fiberInclusion.map ((hc.pullbackIdComponentIso U x).hom ≫
        (hc.pullbackFunctor (𝟙 U)).map φ) ≫ hc.map (𝟙 U) y := by
  -- Postcomposing with the chosen identity pullback map exposes the common triangle from the text.
  have hleft :
      Fiber.fiberInclusion.map (φ ≫ (hc.pullbackIdComponentIso U y).hom) ≫ hc.map (𝟙 U) y = φ.1 := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ φ.1 ≫ k) (hc.pullbackIdComponentIso_fac U y)
  have hright :
      Fiber.fiberInclusion.map ((hc.pullbackIdComponentIso U x).hom ≫
          (hc.pullbackFunctor (𝟙 U)).map φ) ≫ hc.map (𝟙 U) y = φ.1 := by
    calc
      Fiber.fiberInclusion.map ((hc.pullbackIdComponentIso U x).hom ≫
          (hc.pullbackFunctor (𝟙 U)).map φ) ≫ hc.map (𝟙 U) y
          = Fiber.fiberInclusion.map (hc.pullbackIdComponentIso U x).hom ≫
              hc.map (𝟙 U) x ≫ φ.1 := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ Fiber.fiberInclusion.map (hc.pullbackIdComponentIso U x).hom ≫ k)
                    (hc.pullbackFunctor_map_fac (𝟙 U) φ)
      _ = φ.1 := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ φ.1) (hc.pullbackIdComponentIso_fac U x)
  exact hleft.trans hright.symm

-- Proof sketch: after forgetting to the total category, both composites express the same morphism
-- over `𝟙 U` compatible with the defining triangle for the identity pullback comparison; uniqueness
-- in the fiber gives naturality.
theorem pullbackIdIso_naturality
    (U : C) :
    ∀ {x y : Fiber p U} (φ : x ⟶ y),
      φ ≫ (hc.pullbackIdComponentIso U y).hom =
        (hc.pullbackIdComponentIso U x).hom ≫ (hc.pullbackFunctor (𝟙 U)).map φ := by
  intro x y φ
  -- Compare the two identity-comparison candidates after forgetting to the ambient category.
  apply Fiber.hom_ext
  let ψ := Fiber.fiberInclusion.map (φ ≫ (hc.pullbackIdComponentIso U y).hom)
  let ψ' := Fiber.fiberInclusion.map ((hc.pullbackIdComponentIso U x).hom ≫
    (hc.pullbackFunctor (𝟙 U)).map φ)
  letI : p.IsHomLift (𝟙 U) ψ := by
    dsimp [ψ]
    exact (φ ≫ (hc.pullbackIdComponentIso U y).hom).2
  letI : p.IsHomLift (𝟙 U) ψ' := by
    dsimp [ψ']
    exact ((hc.pullbackIdComponentIso U x).hom ≫ (hc.pullbackFunctor (𝟙 U)).map φ).2
  -- The helper packages the common factorization into the chosen identity pullback arrow.
  change ψ = ψ'
  have hψ : p.IsHomLift (𝟙 U) ψ := inferInstance
  have hψ' : p.IsHomLift (𝟙 U) ψ' := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 U) (hc.map (𝟙 U) y) inferInstance _ _ (𝟙 U) ψ ψ' hψ hψ'
      (by exact hc.pullbackIdIso_postcompose_eq U φ)

/-- Lemma 4.33.7 (2): the canonical unit isomorphism
`α_U : 𝟭 (Fiber p U) ≅ (𝟙 U)^*`. -/
noncomputable def pullbackIdIso
    (U : C) :
    𝟭 (Fiber p U) ≅ hc.pullbackFunctor (𝟙 U) :=
  NatIso.ofComponents (hc.pullbackIdComponentIso U) (hc.pullbackIdIso_naturality U)

-- Proof sketch: as in the source text, the displayed triangle over `𝟙 U` determines each
-- component uniquely in the fiber over `U`; extensionality for natural isomorphisms then gives the
-- global uniqueness statement.
/-- Helper for Lemma 4.33.7 (2): the unit comparison `α_U : 𝟭 ≅ (𝟙 U)^*` is uniquely
determined by the requirement that its components factor the chosen identity pullback arrows
through identities. -/
theorem pullbackIdIso_unique
    (U : C) (α : 𝟭 (Fiber p U) ≅ hc.pullbackFunctor (𝟙 U))
    (hα : ∀ x : Fiber p U, (α.hom.app x).1 ≫ hc.map (𝟙 U) x = 𝟙 (x.1)) :
    α = hc.pullbackIdIso U := by
  -- The source-text triangle over `𝟙 U` determines the unit comparison component uniquely.
  ext x
  let ψ := Fiber.fiberInclusion.map (α.hom.app x)
  let ψ' := Fiber.fiberInclusion.map ((hc.pullbackIdIso U).hom.app x)
  letI : p.IsHomLift (𝟙 U) ψ := by
    dsimp [ψ]
    exact (α.hom.app x).2
  letI : p.IsHomLift (𝟙 U) ψ' := by
    dsimp [ψ', pullbackIdIso]
    exact (hc.pullbackIdComponentIso U x).hom.2
  change ψ = ψ'
  have hψ : ψ ≫ hc.map (𝟙 U) x = 𝟙 (x.1) := by
    simpa [ψ] using hα x
  have hψ' : ψ' ≫ hc.map (𝟙 U) x = 𝟙 (x.1) := by
    simpa [ψ', pullbackIdIso] using hc.pullbackIdComponentIso_fac U x
  have hψlift : p.IsHomLift (𝟙 U) ψ := inferInstance
  have hψ'lift : p.IsHomLift (𝟙 U) ψ' := inferInstance
  exact
    @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 U) (hc.map (𝟙 U) x) inferInstance _ _ (𝟙 U) ψ ψ' hψlift hψ'lift
      (hψ.trans hψ'.symm)

end PullbackChoice

end CategoryTheory
