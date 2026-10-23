module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_42_6.SliceRepresentable
public import stacks_project.Chap04.Lemma_4_42_6.Core
public import stacks_project.Chap04.Lemma_4_42_6.Pasting2
public import stacks_project.Chap04.Lemma_4_35_7
public import stacks_project.Chap04.Remark_4_35_8
public import stacks_project.Chap04.Lemma_4_31_12

@[expose] public section

/-!
# Lemma 4.42.6, direction (2) ⟹ (1)

This file proves that if every slice morphism `G : C/U ⟶ X` of a category fibred in groupoids
over `C` is representable, then the diagonal `Δ : X ⟶ X ×_C X` is representable.

## The Stacks argument (direction 2 → 1)

Fix `W ∈ Ob(C)` and a test morphism `H : C/W ⟶ X ×_C X`, with components
`G := H ≫ pr₁` and `G' := H ≫ pr₂`, both `C/W ⟶ X`. We must show the slice base change of
`Δ` along `H`, namely `C/W ×_{X ×_C X} X`, is representable over `C/W`.

By the absolutization bridge of `SliceRepresentable.lean`, this is equivalent to representability
over `C` of the *absolute* diagonal pullback `(C/W) ×_{X ×_C X} X`. The hypothesis applied to `G`
at `G'` gives representability of the product pullback `(C/W) ×_X (C/W)`; the Stacks argument then
identifies, over `C`,
`(C/W) ×_{X ×_C X} X ≅ ((C/W) ×_X (C/W)) ×_{(C/W) × (C/W)} (C/W) ≅ C/W'`,
where `W' = W₀ ×_{(a,a'), W × W} W` is built from a representing object `a : W₀ → W` of
`(C/W) ×_X (C/W)` and the second projection `a'`. (The last equivalence is the bundled form of
Lemma 4.31.12 + Remark 4.35.8.)

## Reusable infrastructure proved here

* `cfg_hom_over_id_isIso`, `based_natTrans_into_cfg_isIso`,
  `fibredCategoryMor_twoCell_into_cfg_isIso`, `fibredInGroupoidsMor_twoCell_isIso`: a `2`-morphism
  of categories fibred in groupoids over `C` whose target is fibred in groupoids is invertible.
* `fibredInGroupoidsOver_isLocallyGroupoid` : the `2`-category `FibredInGroupoidsOver C` is a
  `(2,1)`-category (`IsLocallyGroupoid`).
* `isoOfFinal`, `equivalenceOfFinal` : in a locally groupoidal bicategory, any two final objects
  are bicategorically equivalent (uniqueness of `2`-fibre products).
-/

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Functor IsHomLift IsStronglyCartesian Bicategory
open scoped CategoricalPullback

variable {C : Type (max u v)} [Category.{v} C]

/-! ### Generic two-cell and finality helpers

These now live in `Core.lean`, so `Pasting2.lean` and both directions can use them without an
public import cycle. -/

/-! ### Lemma 4.42.6, direction (2) ⟹ (1) -/

/-- Apply the hypothesis to two already chosen slice morphisms and pass to the absolute
two-fibre-product form. -/
opaque diagonal_component_product_isRepresentable
    [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G)
    {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X) :
    (FibredInGroupoidsOver.twoFibreProduct R L).IsRepresentable := by
  have hprod : (FibredInGroupoidsMor.sliceTwoFibreProduct L R).IsRepresentable := hAll L R
  have hprodAbs :
      (absolutize (FibredInGroupoidsMor.sliceTwoFibreProduct L R)).IsRepresentable :=
    (isRepresentable_iff_absolutize_isRepresentable _).1 hprod
  simpa [absolutize_sliceTwoFibreProduct_eq] using hprodAbs

/-- Canonical diagonal base-change for already chosen components and terminal product map. -/
opaque diagonal_canonical_basechange_isRepresentable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (hprodLR : (FibredInGroupoidsOver.twoFibreProduct R L).IsRepresentable) :
    (FibredInGroupoidsOver.twoFibreProduct
      (FibredInGroupoidsOver.overMap
          (Limits.prod.lift (𝟙 W) (𝟙 W) : W ⟶ Limits.prod W W) ≫ uH.hom)
      uDg.hom).IsRepresentable :=
  canonical_diagonal_basechange_representable_of_product X L R uH uDg hprodLR

/-- The canonical target square for the diagonal argument is final. -/
opaque diagonal_target_square_isFinal
    (X : FibredInGroupoidsOver C) :
    Bicategory.IsFinal
      (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :=
  FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct X.baseProjection X.baseProjection

/-- First component of a test map into the canonical self two-fibre product. -/
noncomputable abbrev diagonal_left_component
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    ofFunctor (Over.forget W) ⟶ X :=
  H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p

/-- Second component of a test map into the canonical self two-fibre product. -/
noncomputable abbrev diagonal_right_component
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    ofFunctor (Over.forget W) ⟶ X :=
  H ≫ (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q

/-- Terminal map from the identity diagonal source square to a final target square.
Kept as a (semireducible) `def`, not an `abbrev`: its `⊤_` terminal-lift body is whnf-heavy, so a
reducible abbrev would be eagerly unfolded during `isDefEq` and overflow heartbeats downstream. -/
noncomputable def diagonal_source_terminal_map
    (X : FibredInGroupoidsOver C)
    (T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    [Bicategory.IsFinal T] :
    diagonalSourceSquare X ⟶ T := by
  haveI : Limits.HasTerminal (diagonalSourceSquare X ⟶ T) :=
    Bicategory.IsFinal.hasTerminal (x := T) (diagonalSourceSquare X)
  exact ⊤_ (diagonalSourceSquare X ⟶ T)

/-- Terminal map from the product-slice source square to a final target square.
Kept as a (semireducible) `def` for the same reason as `diagonal_source_terminal_map`. -/
noncomputable def diagonal_product_terminal_map
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    [Bicategory.IsFinal T] :
    productSliceSourceSquare X L R ⟶ T := by
  haveI : Limits.HasTerminal (productSliceSourceSquare X L R ⟶ T) :=
    Bicategory.IsFinal.hasTerminal (x := T) (productSliceSourceSquare X L R)
  exact ⊤_ (productSliceSourceSquare X L R ⟶ T)

/-- The diagonal map of the base object `W`. -/
noncomputable abbrev diagonal_base_delta [Limits.HasBinaryProducts C] {W : C} :
    W ⟶ Limits.prod W W :=
  Limits.prod.lift (𝟙 W) (𝟙 W)

/-- The product-slice map after base change along the diagonal of `W`. -/
noncomputable abbrev diagonal_basechanged_product_map
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection :=
  FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom

/-- The left product-slice projection after pulling back along the diagonal base map. -/
noncomputable opaque diagonal_left_base_iso
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X) :
    (FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
      (productSliceSourceSquare X L R).p) ≅ L := by
  dsimp [diagonal_base_delta, productSliceSourceSquare]
  exact diagonalOverMapFstIso X L

/-- The right product-slice projection after pulling back along the diagonal base map. -/
noncomputable opaque diagonal_right_base_iso
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (L R : ofFunctor (Over.forget W) ⟶ X) :
    (FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
      (productSliceSourceSquare X L R).q) ≅ R := by
  dsimp [diagonal_base_delta, productSliceSourceSquare]
  exact diagonalOverMapSndIso X R

/-- Left projection cell for the comparison map from the diagonal pullback. -/
opaque diagonal_left_projection_cell
    {X : FibredInGroupoidsOver C} {A : FibredInGroupoidsOver C}
    (T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    (PP : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    (H : A ⟶ T.obj) (K : A ⟶ PP.obj) (uH : PP ⟶ T)
    (eL : K ≫ PP.p ≅ H ≫ T.p) :
    (K ≫ uH.hom) ≫ T.p ⟶ H ≫ T.p :=
  (Bicategory.associator K uH.hom T.p).hom ≫
    Bicategory.whiskerLeft K uH.left ≫ eL.hom

/-- Right projection cell for the comparison map from the diagonal pullback. -/
opaque diagonal_right_projection_cell
    {X : FibredInGroupoidsOver C} {A : FibredInGroupoidsOver C}
    (T : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    (PP : BicategoricalTwoCommutativeSquare X.baseProjection X.baseProjection)
    (H : A ⟶ T.obj) (K : A ⟶ PP.obj) (uH : PP ⟶ T)
    (eR : K ≫ PP.q ≅ H ≫ T.q) :
    (K ≫ uH.hom) ≫ T.q ⟶ H ≫ T.q :=
  (Bicategory.associator K uH.hom T.q).hom ≫
    Bicategory.whiskerLeft K uH.right ≫ eR.hom

/-- Canonical left projection cell after base change along the diagonal of `W`. -/
noncomputable opaque diagonal_canonical_left_projection_cell
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (eL : FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
        (productSliceSourceSquare X L R).p ≅
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).p) :
    (FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
          uH.hom) ≫
        (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).p ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).p :=
  diagonal_left_projection_cell
    (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (productSliceSourceSquare X L R) H
    (FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W)) uH eL

/-- Canonical right projection cell after base change along the diagonal of `W`. -/
noncomputable opaque diagonal_canonical_right_projection_cell
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (eR : FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
        (productSliceSourceSquare X L R).q ≅
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).q) :
    (FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
          uH.hom) ≫
        (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection).q ⟶
      H ≫ (FibredInGroupoidsOver.twoFibreProductSquare
        X.baseProjection X.baseProjection).q :=
  diagonal_right_projection_cell
    (FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (productSliceSourceSquare X L R) H
    (FibredInGroupoidsOver.overMap (diagonal_base_delta : W ⟶ Limits.prod W W)) uH eR


end CategoryTheory
