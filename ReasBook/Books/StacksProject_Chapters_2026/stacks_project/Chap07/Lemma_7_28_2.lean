module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.GuitartExact.Over
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

noncomputable section

namespace CategoryTheory.TwoSquare.overPost

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : D ⥤ C)
variable [HasBinaryProducts C] [HasBinaryProducts D]

/- Domain-style sampling for Lemma 7.28.2:
- primary domain: localized slice functors in `CategoryTheory.Over`, with the square determined by
  product with a fixed object and postcomposition along a functor;
- sampled owner API:
  `TwoSquare.overPost`,
  `Over.star`,
  `Over.post`,
  `prodComparisonNatIso`;
- source-facing layer: the localized square attached to `u` and `V`;
- core/canonical owner: `TwoSquare.overPost u V`, whose comparison on right adjoints is supplied by
  `prodComparisonNatIso u V`;
- bridge/view: the induced natural isomorphism between the right adjoints of the vertical functors,
  recorded below as `TwoSquare.overPost.rightAdjointIso`.

Primitive data are only the functor `u`, the binary-product structures, and the family of
preservation hypotheses `∀ Y, PreservesLimit (pair V Y) u`. The localized square itself is
derived API from the owner square `TwoSquare.overPost u V`, so the correct public shape is the
induced natural isomorphism rather than a parallel local wrapper.
-/

/-- Lemma 7.28.2: if `u : \mathcal D ⥤ \mathcal C` preserves the binary products `V ⨯ Y`, then
the owner square `CategoryTheory.TwoSquare.overPost u V` induces the canonical comparison
isomorphism between the right adjoints of its vertical functors:
`Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V)`. -/
noncomputable def rightAdjointIso (V : D)
    [∀ Y, PreservesLimit (pair V Y) u] :
    Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V) :=
  NatIso.ofComponents
    (fun Y ↦
      Over.isoMk ((prodComparisonNatIso u V).app Y) <|
        by
          change prodComparison u V Y ≫ ((Over.star (u.obj V)).obj (u.obj Y)).hom =
            u.map (((Over.star V).obj Y).hom)
          rw [Over.star_obj_hom, Over.star_obj_hom]
          simpa only [prod.lift_fst] using prodComparison_fst u V Y)
    (by
      intro Y Y' f
      ext
      simpa [Over.star_map_left] using (prodComparisonNatIso u V).hom.naturality f)

-- Proof sketch: `rightAdjointIso u V` is already a natural isomorphism, so each component of its
-- `hom` is an isomorphism in the slice category.
/-- Each component of the canonical comparison `rightAdjointIso u V` is an isomorphism in the
relevant slice category. -/
theorem rightAdjointIso_hom_app_isIso (V Y : D)
    [∀ Z, PreservesLimit (pair V Z) u] :
    IsIso ((rightAdjointIso u V).hom.app Y) := by
  -- The comparison itself is a natural isomorphism, so its `hom` is an isomorphism of
  -- functors.
  have h : IsIso (rightAdjointIso u V).hom := by
    infer_instance
  -- The standard componentwise criterion now gives the desired slice isomorphism at `Y`.
  exact (NatTrans.isIso_iff_isIso_app (rightAdjointIso u V).hom).1 h Y

end

end CategoryTheory.TwoSquare.overPost
