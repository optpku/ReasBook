module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_4
public import stacks_project.Chap07.Lemma_7_30_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (U : C)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]
variable (F : Sheaf J (Type (max u v)))

/- Domain-style sampling for Lemma 7.25.7:
- primary domain: localization of sheaves on a slice site and the corresponding slice-category
  description over the sheafified representable `h_U^#`;
- sampled owner API:
  `GrothendieckTopology.representableLocalizationComparison`,
  `Functor.toOver_comp_forget`,
  `GrothendieckTopology.representableLocalizationComparison_inverseImage_obj`,
  `Sheaf.over`,
  `Over.star`,
  `Over.star_obj_hom`;
- source-facing layer: the canonical comparison
  `j_{U!} j_U^{-1} F ⟶ F × h[U]^#[J]`;
- core/canonical owner: the slice object `(J.representableLocalizationComparison U).obj (F.over U)`
  over `h[U]^#[J]`, canonically identified with `((Over.star h[U]^#[J]).obj F)`
  representing product with `h[U]^#[J]`;
- bridge/view: the binary-product braiding turning the canonical `h_U^# × F` slice object into the
  textbook-ordered `F × h[U]^#[J]` projection.

Primitive data are the ambient site `(C, J)`, the object `U`, and the sheaf `F`. The map to the
product is derived from the owner-level over-category comparison and the canonical identification
of inverse-image objects with `Over.star`. The localized restriction should be exposed through the
canonical owner `F.over U`, not the lower-level spelling `(J.overPullback _ U).obj F`.
-/

/-- Lemma 7.25.7: for a sheaf `F` on `(C, J)` and an object `U : C`, the localization extension by
the empty set `j_{U!} j_U^{-1} F` is isomorphic to the product `F × h[U]^#[J]`. -/
noncomputable def localization_lowerShriek_overPullback_prodIso
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        (F.over U) ≅
      (F ⨯ h[U]^#[J]) := by
  let starProdIso :
      (Over.star h[U]^#[J]).obj F ≅
        Over.mk (prod.snd : F ⨯ h[U]^#[J] ⟶ h[U]^#[J]) :=
    Over.isoMk (prod.braiding h[U]^#[J] F) (by
      rw [Over.star_obj_hom]
      calc
        prod.lift prod.snd prod.fst ≫ prod.snd = prod.fst := by
          rw [prod.lift_snd]
        _ = prod.lift prod.fst (𝟙 (h[U]^#[J] ⨯ F)) ≫ prod.fst := by
          symm
          rw [prod.lift_fst])
  simpa [GrothendieckTopology.representableLocalizationComparison] using
    Functor.mapIso
      (Over.forget h[U]^#[J])
      (J.representableLocalizationComparison_inverseImage_obj U F ≪≫ starProdIso)

/-- The forward morphism of `localization_lowerShriek_overPullback_prodIso` is an isomorphism. -/
-- Proof sketch: this morphism is the `hom` of the canonical isomorphism
-- `localization_lowerShriek_overPullback_prodIso`.
theorem localization_lowerShriek_overPullback_prodIso_hom_isIso :
    IsIso (localization_lowerShriek_overPullback_prodIso U F).hom := by
  -- The target map is literally the forward arrow of an isomorphism already constructed above.
  infer_instance

end
