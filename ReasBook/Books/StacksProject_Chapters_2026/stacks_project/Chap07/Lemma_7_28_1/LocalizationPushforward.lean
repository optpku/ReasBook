module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Lemma_7_25_9
public import stacks_project.Chap07.Lemma_7_25_8
public import stacks_project.Chap07.Remark_7_25_10
public import stacks_project.Chap07.Lemma_7_28_1.LowerShriekTransport

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite

universe w u₁ u₂ v₁ v₂ v₃

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Helper for Lemma 7.28.1: composing type-valued sheaves with the ambient `ULift` functor
preserves the sheaf condition on any site appearing in this proof. -/
instance uliftFunctor_hasSheafCompose_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor :
        Type (max u₁ u₂ v₁ v₂) ⥤ Type (max w (max u₁ u₂ v₁ v₂))) where
  isSheaf P hP := by
    -- Reduce to the concrete type-valued sheaf condition where `ULift` is stable.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- Helper for Lemma 7.28.1: the slice sheafness goal is unchanged after whiskering by the ambient
`ULift` functor. -/
theorem overPost_op_comp_isSheaf_iff_ulift
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V)
        (((Over.post u).op ⋙ ℋ.obj) ⋙
          (CategoryTheory.uliftFunctor :
            Type (max u₁ u₂ v₁ v₂) ⥤ Type (max w (max u₁ u₂ v₁ v₂)))) ↔
      Presieve.IsSheaf (JD.over V) ((Over.post u).op ⋙ ℋ.obj) := by
  -- This is exactly the standard `ULift`-invariance of the type-valued sheaf condition.
  exact
    (Presieve.isSheaf_comp_uliftFunctor_iff
      (J := JD.over V) (P := (Over.post u).op ⋙ ℋ.obj))


/-- Helper for Lemma 7.28.1: the source identity
`j_{u(V)!} ∘ u'^* ≅ u^* ∘ j_{V!}` is the canonical pullback-composition comparison for the strict
equality `Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u`. -/
noncomputable def overPost_composite_sheafPullback_iso
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    [Functor.IsContinuous (Over.post u) (JD.over V) (JC.over (u.obj V))]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.post u).op.HasLeftKanExtension P]
    [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
      (Over.forget (u.obj V)).op.HasLeftKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JD (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JC (Type (max u₁ u₂ v₁ v₂))] :
    (Over.post u).sheafPullback (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V)) ⋙
        (Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
          (JC.over (u.obj V)) JC ≅
      (Over.forget V).sheafPullback (Type (max u₁ u₂ v₁ v₂)) (JD.over V) JD ⋙
        u.sheafPullback (Type (max u₁ u₂ v₁ v₂)) JD JC := by
  let A := Type (max u₁ u₂ v₁ v₂)
  letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
    Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
  let leftIso :
      (Over.post u).sheafPullback A (JD.over V) (JC.over (u.obj V)) ⋙
          (Over.forget (u.obj V)).sheafPullback A (JC.over (u.obj V)) JC ≅
        (Over.forget V ⋙ u).sheafPullback A (JD.over V) JC :=
    -- First collapse the slice lower-shriek with the ambient localization functor.
    Functor.sheafPullbackComp'
      (JD.over V) (JC.over (u.obj V)) JC (Over.post u) (Over.forget (u.obj V))
      (eqToIso (overPost_comp_forget_eq u V))
  let rightIso :
      (Over.forget V).sheafPullback A (JD.over V) JD ⋙ u.sheafPullback A JD JC ≅
        (Over.forget V ⋙ u).sheafPullback A (JD.over V) JC :=
    -- Then identify the ambient composite with `u^* ∘ j_{V!}`.
    Functor.sheafPullbackComp'
      (JD.over V) JD JC (Over.forget V) u (Iso.refl _)
  exact leftIso ≪≫ rightIso.symm

/-- Helper for Lemma 7.28.1: objectwise form of
`overPost_composite_sheafPullback_iso`, evaluated at a sheaf on `(C/u(V), JC.over u(V))`. -/
noncomputable def overPost_composite_sheafPullback_iso_app
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    [Functor.IsContinuous (Over.post u) (JD.over V) (JC.over (u.obj V))]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.post u).op.HasLeftKanExtension P]
    [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
      (Over.forget (u.obj V)).op.HasLeftKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JD (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JC (Type (max u₁ u₂ v₁ v₂))]
    (ℋ : Sheaf (JD.over V) (Type (max u₁ u₂ v₁ v₂))) :
    (((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
          (JC.over (u.obj V)) JC).obj
        (((Over.post u).sheafPullback (Type (max u₁ u₂ v₁ v₂))
            (JD.over V) (JC.over (u.obj V))).obj ℋ)) ≅
      ((u.sheafPullback (Type (max u₁ u₂ v₁ v₂)) JD JC).obj
        (((Over.forget V).sheafPullback (Type (max u₁ u₂ v₁ v₂))
            (JD.over V) JD).obj ℋ)) := by
  -- Evaluate the functor-level comparison at `ℋ`.
  simpa using (overPost_composite_sheafPullback_iso (u := u) (V := V)).app ℋ

end

end CategoryTheory
