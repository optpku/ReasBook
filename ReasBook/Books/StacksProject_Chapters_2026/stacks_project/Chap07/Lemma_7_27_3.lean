module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_25_1
public import stacks_project.Chap07.Lemma_7_22_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {U V : C} (f : U ⟶ V)
variable [HasPullbacksAlong f]

/-
Domain-style sampling for Lemma 7.27.3:
- primary domain: relocalization between slice sites and the induced direct image on sheaves;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `Over.mapPullbackAdj`,
  `Adjunction.isContinuous_of_isCocontinuous`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardContinuous`;
- source-facing layer: the textbook direct image `j_*` for relocalization along `f : U ⟶ V`;
- core/canonical owner: the relocalization morphism of topoi
  `(Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)` and its direct image
  `j_*`;
- bridge/view: the right adjoint `Over.pullback f` and the continuous-versus-cocontinuous
  pushforward comparison, used only internally to compute sections of `j_*`.

Primitive data are the morphism `f` and pullbacks along `f`. Continuity of `Over.pullback f` is
derived from the owner adjunction and cocontinuity of `Over.map f`. The canonical relocalization
morphism of topoi already owns the public direct image `j_*`, while the section formula is a
derived computation obtained by comparing that owner with the continuous pushforward of
`Over.pullback f` and then evaluating the standard continuous-pushforward section formula.
-/

/-- Lemma 7.27.3 (1): the relocalization functor `Over.map f` has the continuous right adjoint
`v = Over.pullback f`. -/
theorem relocalization_rightAdjoint_isContinuous :
    (Over.pullback f).IsContinuous (J.over V) (J.over U) :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous (J.over U) (J.over V)

variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.map f).op.HasPointwiseRightKanExtension P]

/- Lemma 7.27.3, owner recall: the relocalization direct image `j_*` along `f` is the pushforward
of the canonical relocalization morphism of topoi attached to `Over.map f`. -/
#check
  ((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)) _*) :
    Sheaf (J.over U) (Type (max u v)) ⥤ Sheaf (J.over V) (Type (max u v)))

/-- Lemma 7.27.3 (2), pushforward form: the direct image obtained from the continuous right
adjoint `v = Over.pullback f` agrees with the direct image of the canonical relocalization
morphism `j`. -/
noncomputable def relocalization_rightAdjoint_pushforwardIso :
    by
      letI : Functor.IsContinuous (Over.pullback f) (J.over V) (J.over U) :=
        relocalization_rightAdjoint_isContinuous f
      exact
        (Over.pullback f).sheafPushforwardContinuous (Type (max u v)) (J.over V) (J.over U) ≅
          ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)).pushforward := by
  letI : Functor.IsContinuous (Over.pullback f) (J.over V) (J.over U) :=
    relocalization_rightAdjoint_isContinuous f
  exact
    continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      (Over.map f) (Over.pullback f) (Type (max u v)) (Over.mapPullbackAdj f)

variable (ℱ : Sheaf (J.over U) (Type (max u v))) (X : Over V)

-- Proof sketch: whisker the functor comparison above by `sheafToPresheaf` to compare the
-- underlying presheaves, then compose with the canonical owner computation
-- `Functor.sheafPushforwardContinuousCompSheafToPresheafIso` for `Over.pullback f`. Evaluating at
-- `X/V` yields the section formula.
/-- The direct image `j_*` along relocalization is computed on `X/V` by evaluating the sheaf on
the slice pullback object `(Over.pullback f).obj X`, i.e. the textbook object
`(X ×_V U)/U`. -/
noncomputable def relocalization_directImage_objIso_sections_over_pullback :
    (((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)) _*).obj ℱ).obj.obj
        (op X)) ≅
      ℱ.obj.obj (op ((Over.pullback f).obj X)) :=
  letI : Functor.IsContinuous (Over.pullback f) (J.over V) (J.over U) :=
    (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous (J.over U) (J.over V)
  let pushforwardIso :
      ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)).pushforward ≅
        (Over.pullback f).sheafPushforwardContinuous (Type (max u v)) (J.over V) (J.over U) :=
    (eqToIso
      (Functor.morphismOfTopoiInOfCocontinuous_pushforward
        (Over.map f) (J.over U) (J.over V))) ≪≫
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        (Over.map f) (Over.pullback f) (Type (max u v)) (Over.mapPullbackAdj f)).symm
  let e :
    (((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over U) (J.over V)).pushforward.obj ℱ).obj)) ≅
        (Over.pullback f).op ⋙ ℱ.obj :=
    ((Functor.isoWhiskerRight
          pushforwardIso
          (sheafToPresheaf (J.over V) (Type (max u v)))).app ℱ) ≪≫
      ((Over.pullback f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (max u v)) (J.over V) (J.over U)).app ℱ
  e.app (op X)

end

end CategoryTheory
