module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import stacks_project.Chap04.Lemma_4_19_6
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling for Lemma 7.5.1:
- primary domain: filtered/cofiltered criteria for structured-arrow categories
- owner declarations reused here:
  `HasSpanCocones`,
  `HasEqualizers`,
  `RepresentablyFlat` as the stronger owner from later Chapter 7 results
- target layer: `source-facing` bridge. The lemma does not supply the stronger owner
  `RepresentablyFlat u`; it only proves that `(StructuredArrow V u)ᵒᵖ` satisfies the two explicit
  hypotheses used in Chapter 4, Lemma 4.19.8.

Primitive data are the pullback/equalizer hypotheses on `C` and the corresponding preservation
hypotheses on `u`. Both the `HasSpanCocones` half and the postcomposition-equalizer half are
derived owner API, so the textbook conjunction below is kept only as a thin source-facing bridge.
-/

/-- Helper for Lemma 7.5.1: in the opposite of a category with equalizers, every parallel pair
becomes equal after postcomposition with the opposite of an equalizer map. -/
private theorem op_postcomposition_equalizers_of_hasEqualizers
    (I : Type u₁) [Category.{v₁} I] [HasEqualizers I] :
    ∀ ⦃X Y : Iᵒᵖ⦄ (f g : X ⟶ Y), ∃ (Z : Iᵒᵖ) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  -- Take the opposite of the equalizer in `I`; this is the required postcomposition equalizer.
  intro X Y f g
  refine ⟨Opposite.op (equalizer f.unop g.unop), (equalizer.ι f.unop g.unop).op, ?_⟩
  -- The equalizer identity in `I` turns into the desired equality after applying `op`.
  simpa using congrArg Quiver.Hom.op (equalizer.condition f.unop g.unop)

/-- Lemma 7.5.1: if `C` has fibre products and equalizers and `u` commutes with them, then the
opposite structured-arrow category `(StructuredArrow V u)ᵒᵖ`, which is the category
`(𝓘_V^u)ᵒᵖ` from the text, satisfies the two hypotheses of Categories, Lemma 4.19.8. -/
theorem structuredArrow_op_has_span_cocones_and_postcomposition_equalizers
    (u : C ⥤ D) (V : D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    HasSpanCocones (StructuredArrow V u)ᵒᵖ ∧
      (∀ ⦃X Y : (StructuredArrow V u)ᵒᵖ⦄ (f g : X ⟶ Y),
        ∃ (Z : (StructuredArrow V u)ᵒᵖ) (h : Y ⟶ Z), f ≫ h = g ≫ h) := by
  -- The equalizer half of the textbook argument is supplied by the induced equalizers in the
  -- structured-arrow category.
  let _ : HasEqualizers (StructuredArrow V u) := inferInstance
  -- The pullback half gives span cocones on the opposite category, and the helper above packages
  -- the dual equalizer argument exactly as in the source proof.
  exact ⟨inferInstance, op_postcomposition_equalizers_of_hasEqualizers (StructuredArrow V u)⟩

end CategoryTheory
