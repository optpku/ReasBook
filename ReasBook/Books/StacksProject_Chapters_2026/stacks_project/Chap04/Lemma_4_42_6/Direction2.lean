module

public import stacks_project.Chap04.Lemma_4_42_6.Direction2AbsFamily
public import stacks_project.Chap04.Lemma_4_42_6.Direction2Left
public import stacks_project.Chap04.Lemma_4_42_6.Direction2Right

@[expose] public section

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Bicategory

variable {C : Type (max u v)} [Category.{v} C]

/-! ### Lemma 4.42.6, direction (2) ⟹ (1)

The fixed-test assembly below triggers a very heavy `isDefEq` on the bundled
`FibredInGroupoidsOver` representation; the two opaques carrying it use a raised `maxHeartbeats`
(per explicit authorization) since the surrounding development forbids it globally. -/

set_option maxHeartbeats 4000000 in
/-- Fixed-test absolute form of Lemma 4.42.6, direction `(2) -> (1)`: for a test map `H` into the
canonical self two-fibre product, the base change of the diagonal along `H` is representable. -/
private opaque diagonal_twoFibreProduct_isRepresentable_of_all_slice_morphisms_representable_aux
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G)
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection) :
    absoluteTfpRep H
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) := by
  let T := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  haveI hT : Bicategory.IsFinal T := diagonal_target_square_isFinal X
  let PDg := diagonalSourceSquare X
  haveI : Limits.HasTerminal (PDg ⟶ T) := Bicategory.IsFinal.hasTerminal (x := T) PDg
  let uDg : PDg ⟶ T := ⊤_ (PDg ⟶ T)
  let L := H ≫ T.p
  let R := H ≫ T.q
  have hprodLR : (FibredInGroupoidsOver.twoFibreProduct R L).IsRepresentable :=
    diagonal_component_product_isRepresentable X hAll L R
  let PP := productSliceSourceSquare X L R
  haveI : Limits.HasTerminal (PP ⟶ T) := Bicategory.IsFinal.hasTerminal (x := T) PP
  let uH : PP ⟶ T := ⊤_ (PP ⟶ T)
  have hcanonDiag :
      (FibredInGroupoidsOver.twoFibreProduct
        (FibredInGroupoidsOver.overMap
            (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
        uDg.hom).IsRepresentable :=
    diagonal_canonical_basechange_isRepresentable X L R uDg uH hprodLR
  let eL : (FibredInGroupoidsOver.overMap
        (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
      (productSliceSourceSquare X L R).p) ≅ L :=
    diagonal_left_base_iso X L R
  let eR : (FibredInGroupoidsOver.overMap
        (diagonal_base_delta : W ⟶ Limits.prod W W) ≫
      (productSliceSourceSquare X L R).q) ≅ R :=
    diagonal_right_base_iso X L R
  let leftK :=
    diagonal_canonical_left_projection_cell X H L R uH eL
  let rightK :=
    diagonal_canonical_right_projection_cell X H L R uH eR
  have hLocal : (FibredInGroupoidsOver.twoFibreProduct H uDg.hom).IsRepresentable :=
    diagonal_final_left_transport_with_alpha X H L R uDg uH
      (actualTwoFibreProductMapsComparisonIsoOfTwoCells X
        (FibredInGroupoidsOver.overMap
          (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
        H leftK rightK)
      hcanonDiag
  exact absoluteTfpRep_of_isRepresentable H
    (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)
    (diagonal_transport_right_to_formal X H uDg hLocal)

set_option maxHeartbeats 4000000 in
/-- Diagonal-specialized family form of Lemma 4.42.6, direction `(2) -> (1)`.  Phrased through the
sealed `diagonalTfpFamily` (diagonal owner hard-coded) and built via `diagonalTfpFamily_of_forall`,
so consumers never `unfold diagonalTfpFamily` on a goal. -/
private opaque diagonal_diagonalTfpFamily_of_all_slice_morphisms_representable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G) :
    diagonalTfpFamily X :=
  diagonalTfpFamily_of_forall X fun _ H =>
    diagonal_twoFibreProduct_isRepresentable_of_all_slice_morphisms_representable_aux X hAll H

/-- Lemma 4.42.6, direction (2) ⟹ (1): if every slice morphism `G : C/U ⟶ X` is representable,
then the diagonal `Δ : X ⟶ X ×_C X` is representable. -/
opaque representable_diagonal_of_all_slice_morphisms_representable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hAll :
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G) :
    FibredInGroupoidsMor.IsRepresentable
      (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) :=
  diagonalTfpFamily_to_isRepresentable X
    (diagonal_diagonalTfpFamily_of_all_slice_morphisms_representable X hAll)

end CategoryTheory
