module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Lemma_4_42_6.Core
public import stacks_project.Chap04.Lemma_4_42_6.Direction2
public import stacks_project.Chap04.Lemma_4_42_6.Direction1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]

/- The owner-level scaffolding for Lemma 4.42.6 — the canonical diagonal owner
`FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection`, the equivalence-transport of
representability, and the product-slice / diagonal base-change comparison — lives in
`Lemma_4_42_6/Core.lean`. The two directions of the equivalence are proved in
`Lemma_4_42_6/Direction1.lean` (`(1) → (2)`) and `Lemma_4_42_6/Direction2.lean` (`(2) → (1)`),
both built on the absolutization bridge `Lemma_4_42_6/SliceRepresentable.lean`. -/

-- Proof sketch: for `(1) → (2)`, fix `U` and `G : C/U ⥤ S`. To test representability of `G`,
-- pull back the diagonal along `(G, G') : C/U × C/V ⥤ S × S` for arbitrary `V` and `G'`,
-- using binary products in `C` and Lemma `4.31.11` together with Remark `4.35.8` to identify the
-- resulting representable pullback with `C/U ×_S C/V`. For `(2) → (1)`, start from a pair
-- `(G, G') : C/V ⥤ S × S`, apply representability to the first projection of
-- `C/V ×_{G, S, G'} C/V`, and then use Lemma `4.31.12` and Remark `4.35.8` to recover the
-- pullback of the diagonal.

/-- Lemma 4.42.6: for a category fibred in groupoids `X` over `C`, representability of its
canonical diagonal morphism is equivalent to representability of every morphism
`G : C/U ⟶ X` from a slice category. The left-hand side uses the canonical owner
`FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection` directly, rather than the wrapper alias
`FibredInGroupoidsOver.baseProjectionDiagonalMor X`. -/
theorem representable_diagonal_iff_all_slice_morphisms_representable
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C] (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.twoFibreProductDiagonalMor X.baseProjection) ↔
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G := by
  exact ⟨
    fun hDiagonal U G =>
      all_slice_morphisms_representable_of_representable_diagonal X hDiagonal G,
    fun hAll =>
      representable_diagonal_of_all_slice_morphisms_representable X hAll⟩

end CategoryTheory
