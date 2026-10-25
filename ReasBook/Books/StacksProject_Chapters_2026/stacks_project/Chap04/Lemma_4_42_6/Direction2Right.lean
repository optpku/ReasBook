module

public import stacks_project.Chap04.Lemma_4_42_6.Pasting2

@[expose] public section

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open Functor IsHomLift IsStronglyCartesian Bicategory
open scoped CategoricalPullback

variable {C : Type (max u v)} [Category.{v} C]

-- `FibredInGroupoidsOver.twoFibreProduct` is transparent globally (so `Pasting2` can project through
-- it).  This wrapper only *delegates* to the postcompose-transport lemma; matching the bundled
-- two-fibre-product goals against that lemma would otherwise unfold the explicit-pullback tower and
-- overflow whnf.  Sealing it here keeps the matching syntactic.
attribute [local irreducible] FibredInGroupoidsOver.twoFibreProduct

/-- Transport the right leg from a local terminal diagonal map to the canonical diagonal morphism.
This file is intentionally small so downstream direction `(2) -> (1)` does not import the larger
transport scratchpad. -/
opaque diagonal_transport_right_to_formal
    (X : FibredInGroupoidsOver C)
    {W : C}
    (H : ofFunctor (Over.forget W) ⟶
      FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (uDg : diagonalSourceSquare X ⟶
      FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection) :
    (FibredInGroupoidsOver.twoFibreProduct H uDg.hom).IsRepresentable →
      (FibredInGroupoidsOver.twoFibreProduct H
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)).IsRepresentable := by
  intro hH
  let β : FibredInGroupoidsMor.G uDg.hom ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor ≅
      FibredInGroupoidsMor.G
          (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ⋙
        (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection).functor :=
    diagonalSourceSquareComparisonIso X uDg ≪≫ (diagonalMorComparisonIso X).symm
  exact twoFibreProduct_representable_transport_postcompose_functor_iso
    (A := ofFunctor (Over.forget W)) (B := X)
    (T := FibredInGroupoidsOver.twoFibreProduct X.baseProjection X.baseProjection)
    (F := H) (F' := H) (G := uDg.hom)
    (G' := FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection)
    (twoFibreProductEquivCatPullback X.baseProjection X.baseProjection)
    (Iso.refl _) β hH

end CategoryTheory
