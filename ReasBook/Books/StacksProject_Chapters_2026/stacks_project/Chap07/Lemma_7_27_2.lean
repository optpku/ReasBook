module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_25_1
public import stacks_project.Chap07.Lemma_7_22_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasBinaryProducts C]

/- Domain-style sampling for Lemma 7.27.2:
- primary domain: localization of a site and the direct image on sheaves;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `Over.forgetAdjStar`,
  `GrothendieckTopology.over`;
- source/core/bridge triage:
  `source-facing`: the textbook formula computing `j_{U*}` on sections by evaluation on the
  slice object `U ⨯ X ⟶ U`;
  `core/canonical`: the localization direct image owner
  `((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*`;
  `bridge/view`: the right adjoint `Over.star U`, supplied by `Over.forgetAdjStar U`, identifies
  the section over `X` with evaluation on the slice object above `U`.

Primitive data are just the site `J` and the object `U`. The localization morphism of topoi and
its pushforward are already owned upstream, while `Over.star U` is derived from the standard
adjunction `Over.forget U ⊣ Over.star U`. The public refinement should therefore keep the main
statement on the canonical owner `j_{U*}` and use the existing right-adjoint comparison with
`Over.star U` only as a bridge to the objectwise slice formula.
-/

variable (U : C)

/- Lemma 7.27.2, owner recall: the localization direct image `j_{U*}` is the pushforward of the
canonical localization morphism attached to `Over.forget U`. -/
#check
  ((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*) :
    Sheaf (J.over U) (Type (max u v)) ⥤ Sheaf J (Type (max u v)))

/- Companion recall: localization at `U` is governed by the standard adjunction
`Over.forget U ⊣ Over.star U`, and `Over.star U` sends `X` to the slice object `U ⨯ X ⟶ U`. -/
#check Over.forgetAdjStar U

/-- Lemma 7.27.2 (1): the localization functor `j_U = Over.forget U` has the continuous right
adjoint `v = Over.star U`. -/
theorem localization_rightAdjoint_isContinuous :
    (Over.star U).IsContinuous J (J.over U) := by
  infer_instance

variable [HasSheafify J (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasPointwiseRightKanExtension P]

/-- Lemma 7.27.2 (2), pushforward form: the direct image obtained from the continuous right
adjoint `v = Over.star U` agrees with the direct image of the canonical localization morphism
`j_U`. -/
noncomputable def localization_rightAdjoint_pushforwardIso :
    (Over.star U).sheafPushforwardContinuous (Type (max u v)) J (J.over U) ≅
      ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J).pushforward :=
  continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (Over.forget U) (Over.star U) (Type (max u v)) (Over.forgetAdjStar U)

/-- Bridge from the source-facing product `X × U / U` to the canonical `Over.star U` object
`U × X / U`. -/
noncomputable def localization_productOverIsoStar (X : C) :
    Over.mk (prod.snd : X ⨯ U ⟶ U) ≅ (Over.star U).obj X :=
  Over.isoMk (prod.braiding X U) (by
    rw [Over.star_obj_hom, prod.lift_fst]
    change prod.lift prod.snd prod.fst ≫ prod.fst = prod.snd
    rw [prod.lift_fst])

/-- Bridge formula: the localization direct image `j_{U*}` is computed on `X` by evaluating `ℱ`
on the canonical right-adjoint object `(Over.star U).obj X`. -/
noncomputable def localization_directImage_objIso_sections_over_star
    (ℱ : Sheaf (J.over U) (Type (max u v))) (X : C) :
    (((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj ℱ).obj.obj
        (op X)) ≅
      ℱ.obj.obj (op ((Over.star U).obj X)) :=
  let pushforwardIso :
      ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J).pushforward ≅
        (Over.star U).sheafPushforwardContinuous (Type (max u v)) J (J.over U) :=
    (eqToIso
      (Functor.morphismOfTopoiInOfCocontinuous_pushforward
        (Over.forget U) (J.over U) J)) ≪≫
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.forget U) (Over.star U) (Type (max u v)) (Over.forgetAdjStar U)).symm
  let e :
      (((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J).pushforward.obj ℱ).obj)) ≅
        (Over.star U).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight
          pushforwardIso
          (sheafToPresheaf J (Type (max u v)))).app ℱ) ≪≫
      ((Over.star U).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (max u v)) J (J.over U)).app ℱ
  e.app (op X)

/-- Lemma 7.27.2 (3): source-facing section formula
`j_{U*} ℱ (X) = ℱ(X × U / U)`. -/
noncomputable def localization_directImage_objIso_sections_product_over
    (ℱ : Sheaf (J.over U) (Type (max u v))) (X : C) :
    (((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj ℱ).obj.obj
        (op X)) ≅
      ℱ.obj.obj (op (Over.mk (prod.snd : X ⨯ U ⟶ U))) :=
  localization_directImage_objIso_sections_over_star U ℱ X ≪≫
    ℱ.obj.mapIso (localization_productOverIsoStar U X).op

end
