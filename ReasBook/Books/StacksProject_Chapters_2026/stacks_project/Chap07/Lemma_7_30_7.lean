module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.30.7:
- primary domain: comparison between the localized inverse-image on the slice site `(C / U, J.over
  U)` and the canonical slice inverse-image functor on `Sh(C, J) / h[U]^#[J]`;
- sampled owner declarations:
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `Functor.sheafAdjunctionContinuous`,
  `Over.forgetAdjStar`,
  `Adjunction.rightAdjointUniq`;
- source/core/bridge triage:
  `source-facing`: the textbook identification of `j_U⁻¹` with the inverse-image functor of the
    localization at `h[U]^#[J]`;
  `core/canonical`: the adjunctions
    `(Over.forget U).sheafPullback ⊣ J.overPullback ... U` and
    `Over.forget h[U]^#[J] ⊣ Over.star h[U]^#[J]`;
  `bridge/view`: the transported comparison along
    `J.representableLocalizationComparison U`.

Primitive data are only the localized object `U` and the two owner adjunctions above. The object
formula is derived API; the canonical owner statement is the natural isomorphism of right adjoints
to the same forgetful functor, obtained via `Adjunction.rightAdjointUniq`. The public surface
should therefore live first at the functor level and only then specialize to objects through the
canonical restriction owner `ℱ.over U`.
-/

section

variable (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/-- Lemma 7.30.7, owner form: under the equivalence
`J.representableLocalizationComparison U : Sh(C/U, J.over U) ≌ Sh(C, J) / h[U]^#[J]`, the
localized
inverse-image functor `j_U⁻¹` is the canonical slice inverse-image functor
`Over.star h[U]^#[J]`. -/
noncomputable def representableLocalizationComparison_inverseImageIso :
    J.overPullback (Type (max u v)) U ⋙ J.representableLocalizationComparison U ≅
      Over.star h[U]^#[J] := by
  let comparison := J.representableLocalizationComparison U
  let hU := h[U]^#[J]
  haveI : comparison.IsEquivalence := J.representableLocalizationComparison_isEquivalence U
  let comparisonAdj := comparison.asEquivalence.toAdjunction
  let comparisonCounitIso := comparison.asEquivalence.counitIso
  let sliceAdj : comparison ⋙ Over.forget hU ⊣ Over.star hU ⋙ comparison.inv :=
    comparisonAdj.comp (Over.forgetAdjStar hU)
  let localizationAdj : comparison ⋙ Over.forget hU ⊣ J.overPullback (Type (max u v)) U :=
    ((Over.forget U).sheafAdjunctionContinuous (Type (max u v)) (J.over U) J).ofNatIsoLeft
      (eqToIso (J.representableLocalizationComparison_forget U).symm)
  let rightIso : Over.star hU ⋙ comparison.inv ≅ J.overPullback (Type (max u v)) U :=
    Adjunction.rightAdjointUniq sliceAdj localizationAdj
  let e' : Over.star hU ≅ J.overPullback (Type (max u v)) U ⋙ comparison :=
    (Functor.rightUnitor (Over.star hU)).symm ≪≫
      Functor.isoWhiskerLeft (Over.star hU) comparisonCounitIso.symm ≪≫
      (Functor.associator (Over.star hU) comparison.inv comparison).symm ≪≫
      Functor.isoWhiskerRight rightIso comparison
  exact e'.symm

/-- Objectwise form of Lemma 7.30.7, stated on the canonical restriction owner `ℱ.over U`. -/
noncomputable def representableLocalizationComparison_inverseImage_obj
    (ℱ : Sheaf J (Type (max u v))) :
    (J.representableLocalizationComparison U).obj (ℱ.over U) ≅
      (Over.star h[U]^#[J]).obj ℱ := by
  simpa [Sheaf.over] using
    (J.representableLocalizationComparison_inverseImageIso U).app ℱ

end

end CategoryTheory.GrothendieckTopology
