module

public import stacks_project.Chap04.Definition_4_31_1
public import stacks_project.Chap04.Lemma_4_31_4
public import stacks_project.Chap04.Lemma_4_31_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C₀ : Type u₁} [Category.{v₁} C₀]
variable {D₀ : Type u₂} [Category.{v₂} D₀]

/- Domain-style sampling for Lemma 4.31.13:
- primary domain: bicategorical `2`-fibre products in `Cat`, expressed through categorical
  pullbacks and the canonical diagonal into a self-pullback;
- sampled owner-level declarations:
  `Bicategory.IsFinal`,
  `CatCommSqOver.toBicategoricalSquare`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `CategoricalPullback.toCatCommSqOver`,
  the generic `CatCommSqOver.toFunctorToCategoricalPullback`-equivalence instance from
  `Lemma_4_31_11`,
  `two_fibre_product_map`;
- best owner abstraction: `CatCommSqOver` is the primitive categorical square data, while
  `Bicategory.IsFinal` of the associated `BicategoricalTwoCommutativeSquare` is the universal
  property owner;
- primitive data: the categorical square underlying the public owner
  `two_fibre_product_diagonal_square F G H`;
- derived API: the diagonal functor `Δₚ H`, obtained by applying
  `CatCommSqOver.toFunctorToCategoricalPullback` to the identity square over `H` and `H`; the
  short owner name
  `categorical_pullback_diagonal` is kept only as stable chapter vocabulary for this canonical
  comparison functor, together with the
  finality/equivalence consequences obtained from the owner square through the canonical
  comparison functor.

Source/core/bridge triage:
- `source-facing`: the displayed square with bottom map `Δₚ H`;
- `core/canonical`: `Bicategory.IsFinal (two_fibre_product_diagonal_square F G H)`;
- `bridge/view`: the direct canonical use of `CatCommSqOver.toFunctorToCategoricalPullback`
  applied to the identity square in `CatCommSqOver H H C₀` and to
  `two_fibre_product_diagonal_square_over F G H`. -/

/-- The canonical diagonal functor `Δₚ H : C ⥤ C ×[D] C` attached to a functor `H : C ⥤ D`. -/
abbrev categorical_pullback_diagonal (H : C₀ ⥤ D₀) : C₀ ⥤ H ⊡ H :=
  (toFunctorToCategoricalPullback H H C₀).obj
    { fst := 𝟭 C₀
      snd := 𝟭 C₀
      iso := Iso.refl _ }

@[inherit_doc categorical_pullback_diagonal]
scoped[CategoricalPullback] notation "Δₚ" => CategoryTheory.Limits.categorical_pullback_diagonal

open scoped CategoricalPullback
local notation "Δₚ" => CategoryTheory.Limits.categorical_pullback_diagonal

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable {D : Type (max u v)} [Category.{v} D]

/- The functor from `A ×[C] B` to the base category `C`, obtained from the first projection. -/
abbrev two_fibre_product_to_base (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤ C :=
  π₁ F G ⋙ F

/- Postcomposing the comparison isomorphism with `H` induces a functor
`A ×[C] B ⥤ A ×[D] B`. -/
abbrev two_fibre_product_postcompose (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ (F ⋙ H) ⊡ (G ⋙ H) :=
  two_fibre_product_map
    (Functor.leftUnitor (G ⋙ H))
    (Functor.leftUnitor (F ⋙ H)).symm

@[simp] theorem two_fibre_product_postcompose_obj_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_postcompose F G H).obj X).fst = X.fst := rfl

@[simp] theorem two_fibre_product_postcompose_obj_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_postcompose F G H).obj X).snd = X.snd := rfl

@[simp] theorem two_fibre_product_postcompose_map_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((two_fibre_product_postcompose F G H).map f).fst = f.fst := rfl

@[simp] theorem two_fibre_product_postcompose_map_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : F ⊡ G} (f : X ⟶ Y) :
    ((two_fibre_product_postcompose F G H).map f).snd = f.snd := rfl

/-- Helper for Lemma 4.31.13: postcomposing the inner pullback by `H` carries the structural
isomorphism to `H.map X.iso.hom`. -/
@[simp] theorem twoFibreProductPostcompose_obj_iso_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_postcompose F G H).obj X).iso.hom = H.map X.iso.hom := by
  simpa [two_fibre_product_postcompose, Category.assoc] using
    (two_fibre_product_map_obj_iso_hom
      (Functor.leftUnitor (G ⋙ H))
      (Functor.leftUnitor (F ⋙ H)).symm
      X)

/-- The right vertical functor `A ×[D] B ⥤ C ×[D] C`. -/
abbrev two_fibre_product_right_vertical (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ H) ⊡ (G ⋙ H) ⥤ H ⊡ H :=
  two_fibre_product_map
    (Functor.rightUnitor (G ⋙ H)).symm
    (Functor.rightUnitor (F ⋙ H))

@[simp] theorem two_fibre_product_right_vertical_obj_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((two_fibre_product_right_vertical F G H).obj X).fst = F.obj X.fst := rfl

@[simp] theorem two_fibre_product_right_vertical_obj_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((two_fibre_product_right_vertical F G H).obj X).snd = G.obj X.snd := rfl

@[simp] theorem two_fibre_product_right_vertical_map_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (F ⋙ H) ⊡ (G ⋙ H)} (f : X ⟶ Y) :
    ((two_fibre_product_right_vertical F G H).map f).fst = F.map f.fst := rfl

@[simp] theorem two_fibre_product_right_vertical_map_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (F ⋙ H) ⊡ (G ⋙ H)} (f : X ⟶ Y) :
    ((two_fibre_product_right_vertical F G H).map f).snd = G.map f.snd := rfl

/-- Helper for Lemma 4.31.13: the right vertical functor remembers exactly the `H`-image of the
inner pullback structural isomorphism. -/
@[simp] theorem twoFibreProductRightVertical_obj_iso_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (F ⋙ H) ⊡ (G ⋙ H)) :
    ((two_fibre_product_right_vertical F G H).obj X).iso.hom = X.iso.hom := by
  simpa [two_fibre_product_right_vertical, Category.assoc] using
    (two_fibre_product_map_obj_iso_hom
      (Functor.rightUnitor (G ⋙ H)).symm
      (Functor.rightUnitor (F ⋙ H))
      X)

abbrev two_fibre_product_diagonal_square_top
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ H ⊡ H :=
  two_fibre_product_postcompose F G H ⋙ two_fibre_product_right_vertical F G H

abbrev two_fibre_product_diagonal_square_bottom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ H ⊡ H :=
  two_fibre_product_to_base F G ⋙ Δₚ H

/-- The first projected component of the diagonal square is the identity. -/
abbrev two_fibre_product_diagonal_square_first_iso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    two_fibre_product_diagonal_square_top F G H ⋙ π₁ H H ≅
      two_fibre_product_diagonal_square_bottom F G H ⋙ π₁ H H :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (fun {X Y} f ↦ by
    simp [two_fibre_product_to_base])

/-- The second projected component of the diagonal square is the canonical comparison
isomorphism on `A ×[C] B`. -/
abbrev two_fibre_product_diagonal_square_second_iso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    two_fibre_product_diagonal_square_top F G H ⋙ π₂ H H ≅
      two_fibre_product_diagonal_square_bottom F G H ⋙ π₂ H H :=
  by
    simpa [two_fibre_product_to_base] using
      (CatCommSq.iso (π₁ F G) (π₂ F G) F G).symm

/-- Helper for Lemma 4.31.13: the top composite square carries exactly the `H`-image of the
original pullback isomorphism. -/
@[simp] theorem twoFibreProductDiagonalSquareTopObjIsoHom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_diagonal_square_top F G H).obj X).iso.hom = H.map X.iso.hom := by
  -- First normalize the postcomposition step, then the right-vertical step.
  change
    ((two_fibre_product_right_vertical F G H).obj
        ((two_fibre_product_postcompose F G H).obj X)).iso.hom =
      H.map X.iso.hom
  rw [twoFibreProductRightVertical_obj_iso_hom]
  exact twoFibreProductPostcompose_obj_iso_hom F G H X

/- The displayed square
`A ×[C] B ⥤ A ×[D] B`, `A ×[C] B ⥤ C`, `A ×[D] B ⥤ C ×[D] C`, `C ⥤ C ×[D] C`
is `2`-commutative. -/
abbrev two_fibre_product_diagonal_square_iso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    two_fibre_product_diagonal_square_top F G H ≅
      two_fibre_product_diagonal_square_bottom F G H := by
  -- Route correction: freeze the top-object structural map first, then package the square
  -- objectwise so no later proof has to reopen the composite functor.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · -- Each component identifies the top object with the diagonal object using `X.iso.symm`.
    refine CategoricalPullback.mkIso (.refl _) X.iso.symm ?_
    rw [twoFibreProductDiagonalSquareTopObjIsoHom]
    simp
  · intro X Y f
    -- Naturality is just the original pullback compatibility, projected to the two legs.
    apply CategoricalPullback.hom_ext
    · simp [two_fibre_product_diagonal_square_top, two_fibre_product_diagonal_square_bottom,
        two_fibre_product_to_base]
    · simpa [two_fibre_product_diagonal_square_top, two_fibre_product_diagonal_square_bottom,
        two_fibre_product_to_base] using f.w'

/-- Helper for Lemma 4.31.13: the diagonal-square isomorphism has identity first component. -/
@[simp] theorem twoFibreProductDiagonalSquareIso_app_hom_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (((two_fibre_product_diagonal_square_iso F G H).app X).hom).fst =
      𝟙 (F.obj X.fst) := by
  -- The objectwise square isomorphism was built with identity first component.
  simp [two_fibre_product_diagonal_square_iso]

/-- Helper for Lemma 4.31.13: the diagonal-square isomorphism has second component `X.iso.inv`. -/
@[simp] theorem twoFibreProductDiagonalSquareIso_app_hom_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (((two_fibre_product_diagonal_square_iso F G H).app X).hom).snd =
      X.iso.inv := by
  -- The second component is exactly the inverse of the original pullback comparison.
  simp [two_fibre_product_diagonal_square_iso]

/- The given square regarded as an object of the categorical owner of commutative squares over the
cospan `A ×[D] B ⥤ C ×[D] C ← C`. This is the bridge/view layer; the owner-level finality
statement below is expressed directly on its associated `BicategoricalTwoCommutativeSquare`. -/
abbrev two_fibre_product_diagonal_square_over
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    CatCommSqOver
      (two_fibre_product_right_vertical F G H) (Δₚ H)
      (F ⊡ G) :=
  { fst := two_fibre_product_postcompose F G H
    snd := two_fibre_product_to_base F G
    iso := two_fibre_product_diagonal_square_iso F G H }

/-- Helper for Lemma 4.31.13: the canonical comparison from `A ×[C] B` to the ordinary
categorical pullback of `A ×[D] B ⥤ C ×[D] C ← C`. -/
abbrev two_fibre_product_diagonal_comparison
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ⥤ (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H) :=
  (toFunctorToCategoricalPullback
      (two_fibre_product_right_vertical F G H) (Δₚ H) (F ⊡ G)).obj
    (two_fibre_product_diagonal_square_over F G H)

/-- Helper for Lemma 4.31.13: the comparison functor stores exactly the diagonal-square
isomorphism on each object. -/
@[simp] theorem twoFibreProductDiagonalComparisonObjIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    ((two_fibre_product_diagonal_comparison F G H).obj X).iso =
      (two_fibre_product_diagonal_square_iso F G H).app X :=
  rfl

/-- Helper for Lemma 4.31.13: the comparison object has identity outer-left projection. -/
@[simp] theorem twoFibreProductDiagonalComparisonObjIso_hom_fst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (((two_fibre_product_diagonal_comparison F G H).obj X).iso.hom).fst =
      𝟙 (F.obj X.fst) := by
  -- The comparison object stores the same square isomorphism objectwise.
  rw [twoFibreProductDiagonalComparisonObjIso]
  simpa using twoFibreProductDiagonalSquareIso_app_hom_fst F G H X

/-- Helper for Lemma 4.31.13: the comparison object records the original pullback isomorphism on
its outer-right projection. -/
@[simp] theorem twoFibreProductDiagonalComparisonObjIso_hom_snd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (((two_fibre_product_diagonal_comparison F G H).obj X).iso.hom).snd =
      X.iso.inv := by
  -- The outer-right projection remembers the original pullback comparison.
  rw [twoFibreProductDiagonalComparisonObjIso]
  simpa using twoFibreProductDiagonalSquareIso_app_hom_snd F G H X

/-- Helper for Lemma 4.31.13: the outer pullback comparison identifies the left image
`F.obj X.fst.fst` with the chosen base object. -/
abbrev twoFibreProductDiagonalOuterLeftIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    F.obj X.fst.fst ≅ X.snd :=
  (π₁ H H).mapIso X.iso

/-- Helper for Lemma 4.31.13: the outer pullback comparison identifies the right image
`G.obj X.fst.snd` with the chosen base object. -/
abbrev twoFibreProductDiagonalOuterRightIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    G.obj X.fst.snd ≅ X.snd :=
  (π₂ H H).mapIso X.iso

/-- Helper for Lemma 4.31.13: composing the two outer projection isomorphisms recovers the inner
comparison object of `A ×[C] B`. -/
abbrev twoFibreProductDiagonalRecoveredIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    F.obj X.fst.fst ≅ G.obj X.fst.snd :=
  twoFibreProductDiagonalOuterLeftIso F G H X ≪≫
    (twoFibreProductDiagonalOuterRightIso F G H X).symm

/-- Helper for Lemma 4.31.13: the recovered inner comparison is the composite of the two
projected outer isomorphisms. -/
@[simp] theorem twoFibreProductDiagonalRecoveredIso_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    (twoFibreProductDiagonalRecoveredIso F G H X).hom =
      (twoFibreProductDiagonalOuterLeftIso F G H X).hom ≫
        (twoFibreProductDiagonalOuterRightIso F G H X).inv :=
  rfl

/-- Helper for Lemma 4.31.13: the left projection of a morphism in the outer pullback is exactly
the left naturality relation of the recovered base object. -/
theorem twoFibreProductDiagonalOuterLeftNaturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)}
    (f : X ⟶ Y) :
    F.map f.fst.fst ≫ (twoFibreProductDiagonalOuterLeftIso F G H Y).hom =
      (twoFibreProductDiagonalOuterLeftIso F G H X).hom ≫ f.snd := by
  -- Project the outer pullback relation to the first leg.
  change F.map f.fst.fst ≫ Y.iso.hom.fst = X.iso.hom.fst ≫ f.snd
  exact congrArg CategoricalPullback.Hom.fst f.w

/-- Helper for Lemma 4.31.13: the right projection of a morphism in the outer pullback is exactly
the right naturality relation of the recovered base object. -/
theorem twoFibreProductDiagonalOuterRightNaturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)}
    (f : X ⟶ Y) :
    G.map f.fst.snd ≫ (twoFibreProductDiagonalOuterRightIso F G H Y).hom =
      (twoFibreProductDiagonalOuterRightIso F G H X).hom ≫ f.snd := by
  -- Project the same outer pullback relation to the second leg.
  change G.map f.fst.snd ≫ Y.iso.hom.snd = X.iso.hom.snd ≫ f.snd
  exact congrArg CategoricalPullback.Hom.snd f.w

/-- Helper for Lemma 4.31.13: on comparison objects, the recovered inner isomorphism is the
original pullback isomorphism. -/
@[simp] theorem twoFibreProductDiagonalRecoveredIso_comparison_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (twoFibreProductDiagonalRecoveredIso F G H
        ((two_fibre_product_diagonal_comparison F G H).obj X)).hom =
      X.iso.hom := by
  -- The recovered inner comparison is the identity-left leg followed by the inverse of
  -- `X.iso.inv`, hence it is exactly `X.iso.hom`.
  rw [twoFibreProductDiagonalRecoveredIso_hom]
  change (((two_fibre_product_diagonal_comparison F G H).obj X).iso.hom).fst ≫
      (((two_fibre_product_diagonal_comparison F G H).obj X).iso.inv).snd =
    X.iso.hom
  rw [twoFibreProductDiagonalComparisonObjIso_hom_fst]
  rw [show (((two_fibre_product_diagonal_comparison F G H).obj X).iso.inv).snd = X.iso.hom by
    rw [twoFibreProductDiagonalComparisonObjIso]
    simp [two_fibre_product_diagonal_square_iso]]
  simp

/-- Helper for Lemma 4.31.13: the recovered inner comparison is natural in morphisms of the outer
pullback. -/
theorem twoFibreProductDiagonalRecoveredIso_naturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)}
    (f : X ⟶ Y) :
    F.map f.fst.fst ≫ (twoFibreProductDiagonalRecoveredIso F G H Y).hom =
      (twoFibreProductDiagonalRecoveredIso F G H X).hom ≫ G.map f.fst.snd := by
  have hleft : F.map f.fst.fst ≫ Y.iso.hom.fst = X.iso.hom.fst ≫ f.snd := by
    exact congrArg CategoricalPullback.Hom.fst f.w
  have hright : f.snd ≫ Y.iso.inv.snd = X.iso.inv.snd ≫ G.map f.fst.snd := by
    exact congrArg CategoricalPullback.Hom.snd f.w'
  -- Rewrite both outer projections explicitly and then combine the projected naturality laws.
  change F.map f.fst.fst ≫ (Y.iso.hom.fst ≫ Y.iso.inv.snd) =
      (X.iso.hom.fst ≫ X.iso.inv.snd) ≫ G.map f.fst.snd
  have hleft' :
      F.map f.fst.fst ≫ Y.iso.hom.fst ≫ Y.iso.inv.snd =
        (X.iso.hom.fst ≫ f.snd) ≫ Y.iso.inv.snd := by
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ Y.iso.inv.snd) hleft
  have hright' :
      (X.iso.hom.fst ≫ f.snd) ≫ Y.iso.inv.snd =
        X.iso.hom.fst ≫ (X.iso.inv.snd ≫ G.map f.fst.snd) := by
    simpa [Category.assoc] using congrArg (fun t ↦ X.iso.hom.fst ≫ t) hright
  exact hleft'.trans (hright'.trans (by simp [Category.assoc]))

/-- Helper for Lemma 4.31.13: the inverse square remembers the outer pullback's inner `A`-leg. -/
abbrev twoFibreProductDiagonalInverseFst
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H) ⥤ A :=
  π₁ (two_fibre_product_right_vertical F G H) (Δₚ H) ⋙ π₁ (F ⋙ H) (G ⋙ H)

/-- Helper for Lemma 4.31.13: the inverse square remembers the outer pullback's inner `B`-leg. -/
abbrev twoFibreProductDiagonalInverseSnd
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H) ⥤ B :=
  π₁ (two_fibre_product_right_vertical F G H) (Δₚ H) ⋙ π₂ (F ⋙ H) (G ⋙ H)

/-- Helper for Lemma 4.31.13: the outer pullback determines a commutative square over `F` and
`G` by recovering the inner comparison isomorphism. -/
abbrev twoFibreProductDiagonalInverseIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    twoFibreProductDiagonalInverseFst F G H ⋙ F ≅
      twoFibreProductDiagonalInverseSnd F G H ⋙ G :=
  NatIso.ofComponents
    (twoFibreProductDiagonalRecoveredIso F G H)
    (fun {X Y} f ↦ twoFibreProductDiagonalRecoveredIso_naturality F G H f)

/-- Helper for Lemma 4.31.13: forgetting the redundant base object reconstructs the inner
pullback object determined by the two outer projections. -/
abbrev twoFibreProductDiagonalInverse
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H) ⥤ F ⊡ G :=
  -- Route correction: write the inverse functor directly so Lean does not have to elaborate the
  -- whole owner square back through `toFunctorToCategoricalPullback`.
  { obj X :=
      { fst := X.fst.fst
        snd := X.fst.snd
        iso := twoFibreProductDiagonalRecoveredIso F G H X }
    map f :=
      { fst := f.fst.fst
        snd := f.fst.snd
        w := twoFibreProductDiagonalRecoveredIso_naturality F G H f }
    map_id := by
      intro X
      ext <;> rfl
    map_comp := by
      intro X Y Z f g
      ext <;> rfl }

/-- Helper for Lemma 4.31.13: the counit of the recovered inner comparison only changes the
second projection of the outer pullback object. -/
@[simp] theorem twoFibreProductDiagonalRecoveredIso_inv_comp_outerLeftIso_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    (twoFibreProductDiagonalRecoveredIso F G H X).inv ≫
        (twoFibreProductDiagonalOuterLeftIso F G H X).hom =
      X.iso.hom.snd := by
  -- Route correction: the outer counit is controlled by the second projection, not the first.
  have hfst :
      X.iso.inv.fst ≫ X.iso.hom.fst = 𝟙 (((Δₚ H).obj X.snd).fst) := by
    exact congrArg CategoricalPullback.Hom.fst (Iso.inv_hom_id X.iso)
  simpa [twoFibreProductDiagonalRecoveredIso, twoFibreProductDiagonalOuterLeftIso,
    twoFibreProductDiagonalOuterRightIso, Category.assoc] using
    congrArg (fun t ↦ X.iso.hom.snd ≫ t) hfst

/-- Helper for Lemma 4.31.13: the outer pullback commutativity of `X.iso.hom` already says that
its first component factors through the inner pullback structural map. -/
@[simp] theorem twoFibreProductDiagonalOuterIso_hom_fst_factor
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    H.map X.iso.hom.fst = X.fst.iso.hom ≫ H.map X.iso.hom.snd := by
  -- Read the outer pullback compatibility and normalize the right-vertical structural map once.
  have h := X.iso.hom.w
  change H.map X.iso.hom.fst ≫ ((Δₚ H).obj X.snd).iso.hom =
      ((two_fibre_product_right_vertical F G H).obj X.fst).iso.hom ≫ H.map X.iso.hom.snd at h
  rw [twoFibreProductRightVertical_obj_iso_hom] at h
  simpa [categorical_pullback_diagonal] using h

/-- Helper for Lemma 4.31.13: after forgetting the redundant base object, postcomposing the
recovered inner pullback object by `H` returns the original outer-left pullback object. -/
abbrev twoFibreProductDiagonalPostcomposeRecoveredObjIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    (two_fibre_product_postcompose F G H).obj ((twoFibreProductDiagonalInverse F G H).obj X) ≅
      X.fst := by
  -- Route correction: freeze the recovered inner object as a pullback isomorphism, so the
  -- counit consumes an actual object-level bridge instead of another transport equality.
  refine CategoricalPullback.mkIso (.refl _) (.refl _) ?_
  -- The postcomposed recovered structural map is exactly the original inner structural map.
  rw [twoFibreProductPostcompose_obj_iso_hom, twoFibreProductDiagonalRecoveredIso_hom,
    Functor.map_comp]
  have hsnd₀ : X.iso.hom.snd ≫ X.iso.inv.snd = 𝟙 (G.obj X.fst.snd) := by
    -- The second component of `X.iso` is inverse to itself in the outer pullback.
    exact congrArg CategoricalPullback.Hom.snd X.iso.hom_inv_id
  have hsnd :
      H.map X.iso.hom.snd ≫ H.map X.iso.inv.snd = 𝟙 (H.obj (G.obj X.fst.snd)) := by
    -- Apply `H` to the second-component inverse relation.
    simpa [Functor.map_comp] using
      congrArg H.map hsnd₀
  have hcomp :
      H.map X.iso.hom.fst ≫ H.map X.iso.inv.snd =
        X.fst.iso.hom ≫ (H.map X.iso.hom.snd ≫ H.map X.iso.inv.snd) := by
    rw [twoFibreProductDiagonalOuterIso_hom_fst_factor]
    simp [Category.assoc]
  have hcancel :
      X.fst.iso.hom ≫ H.map X.iso.hom.snd ≫ H.map X.iso.inv.snd = X.fst.iso.hom := by
    simpa [Category.assoc] using congrArg (fun t ↦ X.fst.iso.hom ≫ t) hsnd
  have hmain :
      H.map (twoFibreProductDiagonalOuterLeftIso F G H X).hom ≫
          H.map (twoFibreProductDiagonalOuterRightIso F G H X).inv = X.fst.iso.hom := by
    simpa [twoFibreProductDiagonalOuterLeftIso, twoFibreProductDiagonalOuterRightIso] using
      (hcomp.trans hcancel)
  simpa using hmain.symm

/-- Helper for Lemma 4.31.13: postcomposing the recovered inner comparison by `H` recovers the
structural map of the original inner pullback object. -/
@[simp] theorem twoFibreProductDiagonalRecoveredIso_hom_map
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) :
    H.map (twoFibreProductDiagonalRecoveredIso F G H X).hom = X.fst.iso.hom := by
  -- Reuse the normalization from the recovered-object isomorphism, but keep the proof flat here.
  rw [twoFibreProductDiagonalRecoveredIso_hom, Functor.map_comp]
  have hsnd₀ : X.iso.hom.snd ≫ X.iso.inv.snd = 𝟙 (G.obj X.fst.snd) := by
    exact congrArg CategoricalPullback.Hom.snd X.iso.hom_inv_id
  have hsnd :
      H.map X.iso.hom.snd ≫ H.map X.iso.inv.snd = 𝟙 (H.obj (G.obj X.fst.snd)) := by
    simpa [Functor.map_comp] using congrArg H.map hsnd₀
  have hcomp :
      H.map X.iso.hom.fst ≫ H.map X.iso.inv.snd =
        X.fst.iso.hom ≫ (H.map X.iso.hom.snd ≫ H.map X.iso.inv.snd) := by
    rw [twoFibreProductDiagonalOuterIso_hom_fst_factor]
    simp [Category.assoc]
  have hcancel :
      X.fst.iso.hom ≫ H.map X.iso.hom.snd ≫ H.map X.iso.inv.snd = X.fst.iso.hom := by
    simpa [Category.assoc] using congrArg (fun t ↦ X.fst.iso.hom ≫ t) hsnd
  simpa [twoFibreProductDiagonalOuterLeftIso, twoFibreProductDiagonalOuterRightIso] using
    (hcomp.trans hcancel)

/-- Helper for Lemma 4.31.13: the explicit unit for the diagonal comparison equivalence. -/
abbrev twoFibreProductDiagonalUnitIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    𝟭 (F ⊡ G) ≅
      two_fibre_product_diagonal_comparison F G H ⋙
        twoFibreProductDiagonalInverse F G H := by
  -- The unit keeps both pullback projections fixed and only checks the recovered comparison map.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · -- Objectwise, the comparison-inverse recovers the original inner pullback object.
    refine CategoricalPullback.mkIso (.refl _) (.refl _) ?_
    simpa [twoFibreProductDiagonalInverse] using
      twoFibreProductDiagonalRecoveredIso_comparison_hom F G H X
  · intro X Y f
    -- Naturality is componentwise and both projections are definitionally unchanged.
    apply CategoricalPullback.hom_ext <;> simp [twoFibreProductDiagonalInverse]

/-- Helper for Lemma 4.31.13: the explicit counit for the diagonal comparison equivalence. -/
abbrev twoFibreProductDiagonalCounitIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    twoFibreProductDiagonalInverse F G H ⋙
        two_fibre_product_diagonal_comparison F G H ≅
      𝟭 ((two_fibre_product_right_vertical F G H) ⊡ (Δₚ H)) := by
  -- Route correction: package the counit with the frozen inner recovered-object isomorphism.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · -- The first projection is the recovered inner pullback object, and the second is the chosen
    -- base object identified by the outer-left projection.
    refine CategoricalPullback.mkIso
        (twoFibreProductDiagonalPostcomposeRecoveredObjIso F G H X)
        (twoFibreProductDiagonalOuterLeftIso F G H X) ?_
    -- Check the outer pullback compatibility projectionwise.
    apply CategoricalPullback.hom_ext
    · simp [two_fibre_product_diagonal_comparison, twoFibreProductDiagonalPostcomposeRecoveredObjIso,
        twoFibreProductDiagonalInverse]
    · have hfst :
          X.iso.inv.fst ≫ X.iso.hom.fst = 𝟙 X.snd := by
        exact congrArg CategoricalPullback.Hom.fst X.iso.inv_hom_id
      simpa [two_fibre_product_diagonal_comparison, two_fibre_product_to_base,
        twoFibreProductDiagonalInverse, twoFibreProductDiagonalOuterLeftIso, Category.assoc] using
        (congrArg (fun t ↦ X.iso.hom.snd ≫ t) hfst).symm
  · intro X Y f
    -- Naturality splits into the inner recovered-object naturality and the outer-left naturality.
    apply CategoricalPullback.hom_ext
    · apply CategoricalPullback.hom_ext <;> simp [two_fibre_product_diagonal_comparison,
        twoFibreProductDiagonalPostcomposeRecoveredObjIso, twoFibreProductDiagonalInverse]
    · simpa [two_fibre_product_diagonal_comparison, two_fibre_product_to_base,
        twoFibreProductDiagonalInverse] using
        twoFibreProductDiagonalOuterLeftNaturality F G H f

end CategoryTheory.Limits
