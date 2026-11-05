module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import stacks_project.Chap04.Lemma_4_32_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryOver
open scoped CategoricalPullback

namespace CategoryTheory

/-
Domain-style sampling for Example 4.32.4:
- primary domain: comparison between the categorical pullback of functors and the canonical
  `2`-fibre product in `Cat/C`;
- owner abstractions:
  `CategoricalPullback` for the pullback of plain categories,
  `CategoryOver` for categories over a fixed base,
  `BasedCategory.toBase` for the canonical morphism from an object of `Cat/C` to the base object,
  `CategoryOver.explicitTwoFibreProduct` for the canonical pullback object in `Cat/C`;
- primitive data: the unique functor from the one-point category to the one-object two-arrow
  groupoid, and the corresponding object of `Cat/exampleTwoArrowGroupoid`;
- derived API: the concrete discrete-category descriptions of the two pullback constructions,
  together with the resulting inequivalence companion.

Source/core/bridge triage:
- `source-facing`: the concrete descriptions of the two pullback constructions in the example;
- `core/canonical`: `CategoricalPullback` and `explicitTwoFibreProduct`;
- `bridge/view`: the inequivalence comparison theorem deduced from those concrete descriptions. -/

/-- The two-element group used to realize the one-object groupoid with two arrows. -/
abbrev exampleTwoArrowGroup := Multiplicative (ZMod 2)

/-- The groupoid with one object and two arrows from Example 4.32.4. -/
abbrev exampleTwoArrowGroupoid : Type := SingleObj exampleTwoArrowGroup

/-- The unique object of the one-object two-arrow groupoid. -/
abbrev exampleBaseObject : exampleTwoArrowGroupoid :=
  SingleObj.star exampleTwoArrowGroup

/-- The discrete category with one object from Example 4.32.4. -/
abbrev exampleOnePointCategory : Type := Discrete PUnit

/-- The unique functor from the one-point discrete category to the two-arrow groupoid. -/
abbrev exampleOnePointToTwoArrowGroupoid :
    exampleOnePointCategory ⥤ exampleTwoArrowGroupoid :=
  Functor.fromPUnit exampleBaseObject

/-- The categorical pullback of the example cospan, viewed only as a cospan of categories. -/
abbrev exampleCategoricalPullback :=
  exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid

/-- The one-point category viewed as an object of `Cat/exampleTwoArrowGroupoid`. -/
abbrev exampleOnePointOverGroupoid : CategoryOver exampleTwoArrowGroupoid :=
  BasedCategory.ofFunctor exampleOnePointToTwoArrowGroupoid

/-- The underlying category of the canonical `2`-fibre product in
`Cat/exampleTwoArrowGroupoid` for Example 4.32.4. -/
abbrev exampleCategoryOverPullback :=
  (explicitTwoFibreProduct exampleOnePointOverGroupoid.toBase exampleOnePointOverGroupoid.toBase).obj

/-- The unique object of the one-point discrete category. -/
abbrev exampleOnePointObject : exampleOnePointCategory :=
  Discrete.mk PUnit.unit

/-- The unique object of the fibre of the one-point functor over the unique base object. -/
abbrev exampleOnePointLift :
    Functor.Fiber exampleOnePointOverGroupoid.p exampleBaseObject :=
  Functor.Fiber.mk (show exampleOnePointOverGroupoid.p.obj exampleOnePointObject = exampleBaseObject from rfl)

/-- The unique object of the fibre of the identity functor over the unique base object. -/
abbrev exampleIdentityLift :
    Functor.Fiber (𝟭 exampleTwoArrowGroupoid) exampleBaseObject :=
  Functor.Fiber.mk (show (𝟭 exampleTwoArrowGroupoid).obj exampleBaseObject = exampleBaseObject from rfl)

/-- The canonical object of the `2`-fibre product in `Cat/exampleTwoArrowGroupoid`. -/
abbrev exampleCategoryOverPullbackPoint : exampleCategoryOverPullback :=
  { U := exampleBaseObject
    obj :=
      { fst := exampleOnePointLift
        snd := exampleOnePointLift
        iso := Iso.refl exampleIdentityLift } }

/-- The object of the categorical pullback determined by a chosen automorphism of the unique
object of the two-arrow groupoid. -/
noncomputable def exampleCategoricalPullbackFromArrow
    (g : exampleTwoArrowGroup) : exampleCategoricalPullback :=
  { fst := exampleOnePointObject
    snd := exampleOnePointObject
    iso := asIso g }

-- Proof sketch: the structural isomorphism of `exampleCategoricalPullbackFromArrow g` was chosen
-- to have `g` as its underlying morphism.
/-- Reading off the comparison isomorphism of the object built from `g` recovers `g`. -/
theorem exampleCategoricalPullbackFromArrow_hom
    (g : exampleTwoArrowGroup) :
    (exampleCategoricalPullbackFromArrow g).iso.hom = g := by
  -- The object was defined with comparison isomorphism `asIso g`, so its stored morphism is `g`.
  simp [exampleCategoricalPullbackFromArrow, asIso_hom]

-- Proof sketch: an object of the categorical pullback over the constant point functor has only
-- the unique left and right objects available, so it is determined entirely by its comparison
-- isomorphism.
/-- Every object of the categorical pullback is recovered from its comparison automorphism. -/
theorem exampleCategoricalPullback_from_hom
    (P : exampleCategoricalPullback) :
    exampleCategoricalPullbackFromArrow P.iso.hom = P := by
  -- The left and right components are forced to be the unique point object, so rebuilding from
  -- the stored comparison morphism only replaces `P.iso` by `asIso P.iso.hom`.
  cases P with
  | mk fst snd iso =>
      cases fst
      cases snd
      have hiso : asIso iso.hom = iso := by
        ext
        simp [asIso_hom]
      simpa [exampleCategoricalPullbackFromArrow, hiso]

/-- The objects of the categorical pullback are in bijection with the two automorphisms of the
unique object of the two-arrow groupoid. -/
noncomputable def exampleCategoricalPullbackEquivGroup :
    exampleCategoricalPullback ≃ exampleTwoArrowGroup :=
  { toFun := fun P ↦ P.iso.hom
    invFun := exampleCategoricalPullbackFromArrow
    left_inv := exampleCategoricalPullback_from_hom
    right_inv := exampleCategoricalPullbackFromArrow_hom }

-- Proof sketch: the object-reconstruction equivalence identifies the object type of the
-- categorical pullback with the two automorphisms of the unique object of the base groupoid.
/-- The categorical pullback in Example 4.32.4 has finitely many objects. -/
noncomputable instance :
    Fintype exampleCategoricalPullback :=
  Fintype.ofEquiv exampleTwoArrowGroup exampleCategoricalPullbackEquivGroup.symm

-- Proof sketch: an object of the categorical pullback is determined by the unique left and right
-- objects together with an automorphism of the unique object of the base groupoid, and there are
-- exactly two such automorphisms.
/-- The categorical pullback construction in Example 4.32.4 has exactly two objects. -/
theorem exampleCategoricalPullback_card_eq_two :
    Fintype.card exampleCategoricalPullback = 2 := by
  -- The reconstruction equivalence identifies pullback objects with the two elements of `ZMod 2`.
  simpa [exampleTwoArrowGroup] using
    (Fintype.card_congr exampleCategoricalPullbackEquivGroup)

/-- Helper for Example 4.32.4: every morphism in the one-point discrete category is the unique
identity morphism. -/
theorem exampleOnePointCategory_hom_subsingleton
    {X Y : exampleOnePointCategory} (f g : X ⟶ Y) :
    f = g := by
  -- The discrete one-point category has no nontrivial morphism choices.
  exact Subsingleton.elim f g

-- Proof sketch: any morphism in the categorical pullback has identity first and second
-- components, so the compatibility condition forces equality of the comparison isomorphisms;
-- the object-reconstruction theorem then identifies the endpoints.
/-- A morphism in the categorical pullback forces its source and target objects to coincide. -/
theorem exampleCategoricalPullback_eq_of_hom
    {P Q : exampleCategoricalPullback} (f : P ⟶ Q) :
    P = Q := by
  have hf_fst : exampleOnePointToTwoArrowGroupoid.map f.fst = 𝟙 _ :=
    by simp [exampleOnePointToTwoArrowGroupoid]
  have hf_snd : exampleOnePointToTwoArrowGroupoid.map f.snd = 𝟙 _ :=
    by simp [exampleOnePointToTwoArrowGroupoid]
  have hhom :
      P.iso.hom = Q.iso.hom := by
    simpa [hf_fst, hf_snd] using f.w.symm
  calc
    P = exampleCategoricalPullbackFromArrow P.iso.hom := by
      symm
      exact exampleCategoricalPullback_from_hom P
    _ = exampleCategoricalPullbackFromArrow Q.iso.hom := by
      simp [hhom]
    _ = Q := exampleCategoricalPullback_from_hom Q

instance : IsDiscrete exampleCategoricalPullback where
  subsingleton _ _ := by
    -- Morphisms are determined by their two components, and each component lives in a one-point
    -- discrete category.
    refine ⟨fun f g ↦ ?_⟩
    apply CategoricalPullback.hom_ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  eq_of_hom := exampleCategoricalPullback_eq_of_hom

/-- Example 4.32.4 (1): the categorical pullback of the cospan
`exampleOnePointToTwoArrowGroupoid, exampleOnePointToTwoArrowGroupoid` is discrete. -/
instance example_categorical_pullback_isDiscrete :
    IsDiscrete (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) := by
  change IsDiscrete exampleCategoricalPullback
  infer_instance

/-- Example 4.32.4 (2): viewed as an ordinary categorical pullback, the pullback of the one-point
category with itself over the one-object two-arrow groupoid has exactly two objects. -/
theorem example_categorical_pullback_card_eq_two :
    Fintype.card (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) = 2 := by
  simpa using exampleCategoricalPullback_card_eq_two

-- Proof sketch: in the `2`-fibre product over `exampleTwoArrowGroupoid`, the comparison
-- isomorphism lives in the fibre of the identity functor over the unique base object, so it must
-- be the identity; hence the resulting category has a unique object.
/-- Helper for Example 4.32.4: every object of the explicit pullback over the one-object
two-arrow groupoid is the canonical point. -/
theorem exampleCategoryOverPullback_eq_point
    (P : exampleCategoryOverPullback) :
    P = exampleCategoryOverPullbackPoint := by
  -- Collapse the base object and the two fibre objects to the unique choices available in the
  -- one-point categories.
  cases P with
  | mk U obj =>
      cases obj with
      | mk fst snd iso =>
          cases fst with
          | mk x hx =>
              cases snd with
              | mk y hy =>
                  have hxobj : x = exampleOnePointObject := by
                    cases x
                    rfl
                  have hyobj : y = exampleOnePointObject := by
                    cases y
                    rfl
                  cases hxobj
                  cases hyobj
                  cases hx
                  cases hy
                  -- The remaining comparison isomorphism lies in the fibre of the identity functor,
                  -- so its underlying arrow is forced to be the identity.
                  have hhom_val : iso.hom.1 = 𝟙 _ := by
                    let h :=
                      @CategoryTheory.IsHomLift.eq_of_isHomLift
                        _ _ _ _ (𝟭 exampleTwoArrowGroupoid) _ _
                        (𝟙 exampleBaseObject) iso.hom.1 iso.hom.2
                    simpa using
                      h.symm
                  have hhom : iso.hom = 𝟙 _ := by
                    apply Functor.Fiber.hom_ext
                    exact hhom_val
                  have hiso : iso = Iso.refl _ := by
                    ext
                    simpa using congrArg Subtype.val hhom
                  cases hiso
                  rfl

instance : Subsingleton exampleCategoryOverPullback := by
  refine ⟨fun P Q ↦ ?_⟩
  -- Every object identifies with the canonical point, so the whole object type is a subsingleton.
  exact (exampleCategoryOverPullback_eq_point P).trans (exampleCategoryOverPullback_eq_point Q).symm

/-- The `2`-fibre product in `Cat/exampleTwoArrowGroupoid` has a unique object. -/
noncomputable instance : Unique exampleCategoryOverPullback :=
  uniqueOfSubsingleton exampleCategoryOverPullbackPoint

/-- The `2`-fibre product in `Cat/exampleTwoArrowGroupoid` has finitely many objects. -/
noncomputable instance :
    Fintype exampleCategoryOverPullback :=
  inferInstance

/-- Example 4.32.4 (3): in `Cat/exampleTwoArrowGroupoid`, the canonical `2`-fibre product of the
one-point category with itself has a unique object. -/
noncomputable instance example_category_over_pullback_unique :
    Unique
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) := by
  change Unique exampleCategoryOverPullback
  infer_instance

-- Proof sketch: in the pullback over the base groupoid, the comparison isomorphism must lie over
-- the identity of the unique base object, so the only possible comparison arrow is the identity;
-- hence there is only one object.
/-- The pullback construction in `Cat/exampleTwoArrowGroupoid` for Example 4.32.4 has exactly one
object. -/
theorem exampleCategoryOverPullback_card_eq_one :
    Fintype.card exampleCategoryOverPullback = 1 := by
  -- Once the pullback category has a unique object, its object cardinality is immediately `1`.
  simp

/-- Example 4.32.4 (4): viewed as the canonical `2`-fibre product in `Cat/exampleTwoArrowGroupoid`,
the pullback of the one-point category with itself has exactly one object. -/
theorem example_category_over_pullback_card_eq_one :
    Fintype.card
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) = 1 := by
  simpa only [exampleCategoryOverPullback] using exampleCategoryOverPullback_card_eq_one

-- Proof sketch: the point category is discrete and the only admissible base morphism is the
-- identity, so every morphism in the pullback over the base is forced to be the identity.
instance : IsDiscrete exampleCategoryOverPullback where
  subsingleton P Q := by
    -- After collapsing both endpoints to the canonical point, morphisms are determined by their
    -- left and right components in the one-point discrete category.
    refine ⟨fun f g ↦ ?_⟩
    have hP : P = exampleCategoryOverPullbackPoint := exampleCategoryOverPullback_eq_point P
    have hQ : Q = exampleCategoryOverPullbackPoint := exampleCategoryOverPullback_eq_point Q
    subst hP
    subst hQ
    change
      CategoryOver.ExplicitTwoFibreProductHom
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase
        exampleCategoryOverPullbackPoint
        exampleCategoryOverPullbackPoint at f g
    cases f
    cases g
    apply ExplicitTwoFibreProductHom.ext
    · exact exampleOnePointCategory_hom_subsingleton _ _
    · exact exampleOnePointCategory_hom_subsingleton _ _
  eq_of_hom := fun {_ _} _ ↦ Subsingleton.elim _ _

/-- Helper for Example 4.32.4: an equivalence between finite discrete categories preserves the
number of objects. -/
theorem card_eq_of_discrete_equivalence
    {C D : Type*} [Category C] [Category D] [Fintype C] [Fintype D]
    [IsDiscrete C] [IsDiscrete D] (e : C ≌ D) :
    Fintype.card C = Fintype.card D := by
  -- In a discrete category, the unit and counit isomorphisms identify the inverse object maps as
  -- actual inverse functions.
  let h : C ≃ D :=
    { toFun := e.functor.obj
      invFun := e.inverse.obj
      left_inv := fun X ↦ (IsDiscrete.eq_of_hom (e.unitIso.app X).hom).symm
      right_inv := fun Y ↦ IsDiscrete.eq_of_hom (e.counitIso.app Y).hom }
  exact Fintype.card_congr h

/-- Example 4.32.4 (5): in `Cat/exampleTwoArrowGroupoid`, the canonical `2`-fibre product of the
one-point category with itself is discrete. -/
instance example_category_over_pullback_isDiscrete :
    IsDiscrete
      ((explicitTwoFibreProduct
        exampleOnePointOverGroupoid.toBase
        exampleOnePointOverGroupoid.toBase).obj) := by
  change IsDiscrete exampleCategoryOverPullback
  infer_instance

-- Proof sketch: equivalences preserve the cardinality of the object type. The categorical
-- pullback has two objects by `exampleCategoricalPullback_card_eq_two`, while the pullback in
-- `Cat/exampleTwoArrowGroupoid` has one object by `exampleCategoryOverPullback_card_eq_one`.
/-- Example 4.32.4 (6): the `2`-fibre product of the one-point discrete category with itself over the
one-object two-arrow groupoid depends on whether we form it as a pullback of categories or as a
pullback in `Cat/exampleTwoArrowGroupoid`; the two resulting categories are not equivalent. -/
theorem example_two_fibre_product_constructions_not_equivalent :
    ¬ Nonempty
        (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid ≌
          (explicitTwoFibreProduct
            exampleOnePointOverGroupoid.toBase
            exampleOnePointOverGroupoid.toBase).obj) := by
  rintro ⟨e⟩
  -- An equivalence of these discrete categories would force their object types to have the same
  -- finite cardinality, contradicting the computations `2` and `1` above.
  have hcard :
      Fintype.card (exampleOnePointToTwoArrowGroupoid ⊡ exampleOnePointToTwoArrowGroupoid) =
        Fintype.card
          ((explicitTwoFibreProduct
            exampleOnePointOverGroupoid.toBase
            exampleOnePointOverGroupoid.toBase).obj) :=
    card_eq_of_discrete_equivalence e
  rw [example_categorical_pullback_card_eq_two, example_category_over_pullback_card_eq_one] at hcard
  omega

end CategoryTheory
