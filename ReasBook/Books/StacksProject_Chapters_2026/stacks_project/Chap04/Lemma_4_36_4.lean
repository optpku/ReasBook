module

public import stacks_project.Chap04.Lemma_4_36_4.Strictification
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

/-- Lemma 4.36.4: every fibred category `p : S ⥤ C` admits a split strictification over
`C` and a based equivalence over `C` from `p` to that strictification. The strictification target
uses the larger object universe needed to store a base arrow in each strictified object. -/
lemma exists_split_fibred_category_over_base
    (p : S ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{u₁, v₁, max (max u₁ v₁) u₂, max v₁ v₂} C)
      (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p),
      F.IsEquivalenceOverBase ∧ Functor.IsSplitFibredCategory Y.p := by
  exact exists_split_fibred_category_over_base_aux p

section SaturatedOwner

variable {Sₛ : Type (max u₁ (max v₁ u₂))} [Category.{max v₁ v₂} Sₛ]

/-- Helper for Lemma 4.36.4: when the source total category already lives in the universe
needed by the strictification construction, the based strictification comparison promotes to an
owner equivalence of fibred categories. -/
lemma exists_split_fibred_category_over_base_owner_equivalence
    (p : Sₛ ⥤ C) [p.IsFibered] :
    ∃ (Y : FibredCategoryOver.{u₁, v₁, max u₁ (max v₁ u₂), max v₁ v₂} C)
      (_ : FibredCategoryOver.ofFunctor p ≌ Y),
      Functor.IsSplitFibredCategory Y.p := by
  -- Use strictification in the saturated universe, then repackage the based equivalence as an
  -- equivalence in the fibred-category owner.
  obtain ⟨Y, F, hF, hY⟩ :=
    exists_split_fibred_category_over_base.{v₁, v₂, u₁, max v₁ u₂} p
  let F' : FibredCategoryOver.ofFunctor p ⟶ Y :=
    FibredCategoryMor.ofBasedFunctor F
      (BasedFunctor.preservesStronglyCartesian_of_isEquivalenceOverBase hF)
  obtain ⟨e, _he⟩ := FibredCategoryMor.exists_equivalence F' hF
  exact ⟨Y, e, hY⟩

end SaturatedOwner

end CategoryTheory
