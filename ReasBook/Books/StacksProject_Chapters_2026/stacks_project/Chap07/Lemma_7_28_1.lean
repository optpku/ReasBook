module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Lemma_7_25_9
public import stacks_project.Chap07.Lemma_7_25_8
public import stacks_project.Chap07.Remark_7_25_10
public import stacks_project.Chap07.Lemma_7_28_1.Index

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite
open scoped SheafifiedRepresentable

universe w u₁ u₂ v₁ v₂ v₃

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Helper for Lemma 7.28.1: cover preservation of the ambient functor transports to cover
preservation of the induced functor on localized slice sites. -/
private theorem overPost_coverPreserving_of_coverPreserving
    (u : D ⥤ C) (hcov : CoverPreserving JD JC u) (V : D) :
    CoverPreserving (JD.over V) (JC.over (u.obj V)) (Over.post u) where
  cover_preserve {U S} hS := by
    -- Move both localized covering conditions to the corresponding base sieves.
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    -- The slice pushforward is the ambient pushforward after applying `Sieve.overEquiv`.
    rw [overEquiv_functorPushforward_post]
    exact hcov.cover_preserve hS

/-- Helper for Lemma 7.28.1: section fibres stay sheaves after precomposition with the induced
slice functor `Over.post u`. -/
private theorem overPost_sectionFiberPresheaf_isSheaf
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    {E B : Sheaf JC (Type w)} (π : E ⟶ B)
    (b : B.obj.obj (op (u.obj V))) :
    Presieve.IsSheaf (JD.over V) ((Over.post u).op ⋙ sectionFiberPresheaf π b) := by
  -- First prove sheafness for the section fibre of the pushed-forward morphism.
  have hfiber :
      Presieve.IsSheaf (JD.over V)
        (sectionFiberPresheaf
          ((u.sheafPushforwardContinuous (Type w) JD JC).map π) b) :=
    sectionFiberPresheaf_isSheaf
      ((u.sheafPushforwardContinuous (Type w) JD JC).map π) b
  -- Then transport across the explicit identification with precomposition by `Over.post u`.
  exact Presieve.isSheaf_iso (JD.over V)
    (sectionFiberPresheaf_sheafPushforwardContinuous_iso (u := u) (V := V) π b)
    hfiber

/-- Lemma 7.28.1: type-valued sheaves on the localized target site remain sheaves after
precomposition with the induced slice functor. -/
private theorem overPost_op_comp_isSheaf_of_types
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V) ((Over.post u).op ⋙ ℋ.obj) := by
  -- Route correction: the direct sieve-pushforward step is now isolated above under the stronger
  -- `CoverPreserving` hypothesis; the present target only assumes `Functor.IsContinuous`, so the
  -- remaining bridge must identify the fibre of the transported lower-shriek sheaf with
  -- `(Over.post u).op ⋙ ℋ.obj`.
  let π :=
    GrothendieckTopology.uliftRepresentableLocalizationHom.{u₁, v₁, max u₂ v₂}
      JC (u.obj V) ℋ
  let b :=
    GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, max u₂ v₂}
      JC (u.obj V)
  -- First prove sheafness for the identity-section fibre of the enlarged localization morphism.
  have hfiber :
      Presieve.IsSheaf (JD.over V)
        ((Over.post u).op ⋙ sectionFiberPresheaf π b) :=
    overPost_sectionFiberPresheaf_isSheaf (JC := JC) (JD := JD) (u := u) (V := V) π b
  -- Then transport that sheaf condition across the named fibre-identification bridge.
  exact Presieve.isSheaf_iso (JD.over V)
    (overPost_uliftRepresentableLocalization_sectionFiberIso
      (JC := JC) (JD := JD) (u := u) (V := V) ℋ)
    hfiber

-- Proof sketch: once the localized sheafness statement above is proved, continuity is exactly the
-- owner constructor `Functor.IsContinuous.mk`.
/-- The induced slice functor of a continuous site functor is again continuous. -/
instance overPost_isContinuous
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D) :
    (Over.post u).IsContinuous (JD.over V) (JC.over (u.obj V)) := by
  constructor
  intro ℋ
  -- The source-faithful localization proof is isolated in the previous helper.
  exact overPost_op_comp_isSheaf_of_types (u := u) (V := V) ℋ

-- Proof sketch: representable flatness descends to the slice by identifying the relevant
-- structured-arrow category with an over-category in the ambient structured-arrow category.
/-- If `u` is representably flat, then the induced slice functor `Over.post u` is representably
flat. -/
instance overPost_representablyFlat
    (u : D ⥤ C) [RepresentablyFlat u] (V : D) :
    RepresentablyFlat (show Over V ⥤ Over (u.obj V) from Over.post u) := by
  constructor
  intro Y
  -- The ambient structured-arrow category is cofiltered by flatness of `u`.
  haveI : IsCofiltered (StructuredArrow Y.left u) :=
    RepresentablyFlat.cofiltered (F := u) Y.left
  -- Passing to an over-category preserves cofilteredness.
  haveI : IsCofiltered (Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)) :=
    CategoryTheory.IsCofiltered.over _
  -- Transport cofilteredness back across the explicit slice equivalence.
  exact IsCofiltered.of_equivalence
    (structuredArrow_overPost_equiv_over_structuredArrow u V Y).symm

-- Proof sketch: the chapter owner `IsMorphismOfSites` is by definition continuity together with
-- representable flatness, both already provided above for `Over.post u`.
/-- The slice functor induced by a morphism of sites is again a morphism of sites on the localized
sites. -/
instance overPost_isMorphismOfSites
    (u : D ⥤ C) [IsMorphismOfSites JD JC u] (V : D) :
    IsMorphismOfSites (JD.over V) (JC.over (u.obj V))
      (show Over V ⥤ Over (u.obj V) from Over.post u) :=
  inferInstance

-- Proof sketch: once `Over.post u` is continuous, the commutative square of direct images is the
-- canonical owner comparison for the strict equality
-- `Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u`.
/-- Helper for Lemma 7.28.1: the localized direct-image square is the owner-level comparison
`f'_* j_U^{-1} ≅ j_V^{-1} f_*`. -/
noncomputable def slice_pushforward_comp_iso
    (u : D ⥤ C) [u.IsContinuous JD JC]
    (V : D) (A : Type w) [Category.{v₃} A] :
    JC.overPullback A (u.obj V) ⋙
        (Over.post u).sheafPushforwardContinuous A (JD.over V) (JC.over (u.obj V)) ≅
      u.sheafPushforwardContinuous A JD JC ⋙ JD.overPullback A V := by
  letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
    Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
  -- Apply the owner comparison to the strict commutative triangle on slice forgetful functors.
  exact
    Functor.sheafPushforwardContinuousComp'
      (eqToIso (overPost_comp_forget_eq u V) :
        Over.post u ⋙ Over.forget (u.obj V) ≅ Over.forget V ⋙ u)
      A (JD.over V) (JC.over (u.obj V)) JC

end

end CategoryTheory
