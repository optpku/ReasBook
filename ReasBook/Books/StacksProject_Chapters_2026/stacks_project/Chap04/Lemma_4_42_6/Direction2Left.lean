module

public import stacks_project.Chap04.Lemma_4_42_6.Direction2Aux

@[expose] public section

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Bicategory

variable {C : Type (max u v)} [Category.{v} C]

/-- Helper for Lemma 4.42.6: transport the left leg in the diagonal argument once the
postcomposed comparison isomorphism is supplied explicitly. -/
opaque diagonal_final_left_transport_with_alpha
    [Limits.HasBinaryProducts C]
    (X : FibredInGroupoidsOver C) {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (L R : ofFunctor (Over.forget W) ⟶ X)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (uH : productSliceSourceSquare X L R ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection)
    (alpha :
      FibredInGroupoidsMor.G
            (FibredInGroupoidsOver.overMap
                (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom) ⋙
          (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
        FibredInGroupoidsMor.G H ⋙
          (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor)
    (hcanonDiag :
      (FibredInGroupoidsOver.twoFibreProduct
        (FibredInGroupoidsOver.overMap
            (diagonal_base_delta : W ⟶ Limits.prod W W) ≫ uH.hom)
        uDg.hom).IsRepresentable) :
    (FibredInGroupoidsOver.twoFibreProduct H uDg.hom).IsRepresentable :=
  twoFibreProduct_representable_transport_postcompose_left
    (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection) alpha hcanonDiag

end CategoryTheory
