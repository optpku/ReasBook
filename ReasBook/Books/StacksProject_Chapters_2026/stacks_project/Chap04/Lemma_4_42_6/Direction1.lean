module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_42_6.SliceRepresentable
public import stacks_project.Chap04.Lemma_4_42_6.Core
public import stacks_project.Chap04.Lemma_4_42_6.Pasting2

@[expose] public section

/-!
# Lemma 4.42.6 (tag 02YA), direction (1) → (2)

If the diagonal `Δ : X → X ×_C X` of a category fibred in groupoids `X` over `C` is
representable, then every `1`-morphism `G : C/U → X` from a slice category is representable.

The Stacks proof: to test representability of `G`, fix `V` and `G' : C/V → X` and pull back the
diagonal along `(G, G') : C/U × C/V → X × X`. Using binary products in `C`, the result is
identified with the slice `2`-fibre product `C/U ×_X C/V`. The cross-base scaffolding lives in
`Core.lean` / `SliceRepresentable.lean`; this file supplies the remaining "math equivalence"
`C/V ×_X C/U ≅_C C/(U⨯V) ×_{X×_C X} X`.

## Architecture

The concrete diagonal and product-slice comparison are kept as local `let`s in the main proof.  The
long total-category equivalence and its compatibility with the projection to `C` are packaged in
`Pasting2.lean`, close to the Remark 4.35.8 projection-formula APIs it uses.
-/

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

variable {C : Type (max u v)} [Category.{v} C]

-- The diagonal owner `twoFibreProductDiagonalMor X.baseProjection` is definitionally the terminal
-- map `uDg.hom` out of `diagonalSourceSquare X`; it is kept `@[irreducible]` globally to avoid
-- whnf-overflows when its terminal-factorization body is exposed, so we locally restore default
-- unfolding here where that definitional identification is exactly what is needed.
attribute [local semireducible] FibredInGroupoidsMor.twoFibreProductDiagonalMor

/-! ### Product-slice/diagonal base-change comparison

The comparison `C/V ×_X C/U ≃ C/(U×V) ×_{X×_C X} X`, together with its compatibility over `C`,
is provided by `productSliceDiagonalBasechange_representabilityTransport` in `Pasting2.lean`. -/

/-- Fixed-test form of direction `(1) -> (2)`: the absolute product-slice pullback is
representable. -/
private theorem sliceProduct_twoFibreProduct_isRepresentable_of_representable_diagonal
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hDiagonal :
      FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection))
    {U V : C} (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    (FibredInGroupoidsOver.twoFibreProduct G' G).IsRepresentable := by
  let DTsq := FibredInGroupoidsOver.twoFibreProductSquare X.baseProjection X.baseProjection
  haveI hDTsq : Bicategory.IsFinal DTsq :=
    FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct X.baseProjection X.baseProjection
  let PDg := diagonalSourceSquare X
  haveI : Limits.HasTerminal (PDg ⟶ DTsq) :=
    Bicategory.IsFinal.hasTerminal (x := DTsq) PDg
  let uDg : PDg ⟶ DTsq := ⊤_ (PDg ⟶ DTsq)
  let Dg : X ⟶ DTsq.obj := uDg.hom
  haveI : Limits.HasTerminal ((productSliceSourceSquare X G G') ⟶ DTsq) :=
    Bicategory.IsFinal.hasTerminal (x := DTsq) (productSliceSourceSquare X G G')
  let uH : (productSliceSourceSquare X G G') ⟶ DTsq :=
    ⊤_ ((productSliceSourceSquare X G G') ⟶ DTsq)
  have hRep := diagonal_twoFibreProduct_isRepresentable_of_representable X hDiagonal uH.hom
  exact productSliceDiagonalBasechange_representabilityTransport X G G' uH uDg hRep

/-- Fixed-test form of direction `(1) -> (2)` after passing from the slice base to `C`. -/
private theorem absolutized_sliceProduct_isRepresentable_of_representable_diagonal
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hDiagonal :
      FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection))
    {U V : C} (G : ofFunctor (Over.forget U) ⟶ X)
    (G' : ofFunctor (Over.forget V) ⟶ X) :
    (absolutize (FibredInGroupoidsMor.sliceTwoFibreProduct G G')).IsRepresentable :=
  absolutize_sliceTwoFibreProduct_isRepresentable_of_twoFibreProduct G G'
    (sliceProduct_twoFibreProduct_isRepresentable_of_representable_diagonal X hDiagonal G G')

/-- Lemma 4.42.6, direction (1) → (2): if the diagonal of `X` is representable, then every slice
morphism `G : C/U → X` is representable. -/
theorem all_slice_morphisms_representable_of_representable_diagonal
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    (X : FibredInGroupoidsOver C)
    (hDiagonal :
      FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection))
    {U : C} (G : ofFunctor (Over.forget U) ⟶ X) :
    FibredInGroupoidsMor.IsRepresentable G := by
  rw [FibredInGroupoidsMor.isRepresentable_iff_forall_sliceTwoFibreProduct_isRepresentable]
  intro V G'
  exact (isRepresentable_iff_absolutize_isRepresentable
    (FibredInGroupoidsMor.sliceTwoFibreProduct G G')).mpr
      (absolutized_sliceProduct_isRepresentable_of_representable_diagonal X hDiagonal G G')

end CategoryTheory
