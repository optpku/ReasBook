module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_25_8
public import stacks_project.Chap07.Lemma_7_27_5
public import stacks_project.Chap07.Lemma_7_28_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w u₁ u₂ v₁ v₂

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

variable (u : D ⥤ C) [u.IsContinuous JD JC]

variable [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]

/- Domain-style sampling for Lemma 7.28.3:
- primary domain: localized comparison functors for morphisms of sites and relocalization on slice
  sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPullbackComp'`,
  `GrothendieckTopology.overPullback`,
  `GrothendieckTopology.overMapPullback`,
  `relocalization_inverse_image_square_iso`;
- source-facing layer: the localized factorization and naturality statements attached to
  `c : U ⟶ u.obj V`;
- core/canonical owner: the sheaf functors `u.sheafPushforwardContinuous`,
  `(Over.post u).sheafPushforwardContinuous`, `JC.overPullback`, and `JC.overMapPullback`;
- bridge/view layer: the specialized comparison isomorphisms between those owner functors. This
  file should stay at that bridge layer and should not introduce a second family of comparison
  owners.

Primitive data are only the site functor `u`, the localization morphism `c`, and in part `(2)` the
commutative square `c' ≫ u.map b = a ≫ c`. The localized comparison functors themselves are
already derived from the chapter/mathlib owners above, so the refined file should recall and
specialize those owners directly rather than keep four broken chapter-local wrapper declarations.
-/

recall Functor.sheafPushforwardContinuousComp'
recall Functor.sheafPullbackComp'
recall relocalization_inverse_image_square_iso

section

variable {V : D} {U : C}
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type w, (Over.forget (u.obj V)).op.HasLeftKanExtension P]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify JC (Type w)]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [HasWeakSheafify (JC.over U) (Type w)]
variable [HasWeakSheafify (JD.over V) (Type w)]
variable [IsMorphismOfSites JD JC u]

/- Lemma 7.28.3 (1): the source comparison
`j_U⁻¹ ⋙ f⁻¹ ≅ (f_c)⁻¹ ⋙ j_V⁻¹`
is obtained by composing the localized square of Lemma `7.28.1` with the relocalization triangle
of Lemma `7.25.8`. The file should therefore recall those owner comparisons directly rather than
keep a parallel chapter-local wrapper around their composite. -/
#check
  (fun
    (u : D ⥤ C)
    [u.IsContinuous JD JC]
    (V : D) ↦
      by
        letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
          Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
        exact
          (Functor.sheafPushforwardContinuousComp'
            (eqToIso (by rfl) : Over.post u ⋙ Over.forget (u.obj V) ≅ Over.forget V ⋙ u)
            (Type w) (JD.over V) (JC.over (u.obj V)) JC :
            JC.overPullback (Type w) (u.obj V) ⋙
                (Over.post u).sheafPushforwardContinuous (Type w)
                  (JD.over V) (JC.over (u.obj V)) ≅
              u.sheafPushforwardContinuous (Type w) JD JC ⋙
                JD.overPullback (Type w) V))

#check
  (fun (c : U ⟶ u.obj V) ↦
    (Functor.sheafPushforwardContinuousComp'
      (Over.mapForget c) (Type w) (JC.over U) (JC.over (u.obj V)) JC :
        JC.overPullback (Type w) (u.obj V) ⋙
            JC.overMapPullback (Type w) c ≅
          JC.overPullback (Type w) U))

end

section

variable {V V' : D} {U U' : C}
variable [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [∀ P : (Over V')ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
variable [HasWeakSheafify (JC.over (u.obj V')) (Type w)]
variable (c : U ⟶ u.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
variable (c' : U' ⟶ u.obj V') (hcomm : c' ≫ u.map b = a ≫ c)

/- Lemma 7.28.3 (2): naturality in `c` is exactly the relocalization square owner specialized to
the commutative square `c' ≫ u.map b = a ≫ c`; no separate chapter-local comparison is needed. -/
#check
  (relocalization_inverse_image_square_iso
    JC a c' c (u.map b) hcomm.symm :
      JC.overMapPullback (Type w) c ⋙
          JC.overMapPullback (Type w) a ≅
        JC.overMapPullback (Type w) (u.map b) ⋙
          JC.overMapPullback (Type w) c')

end

end

end CategoryTheory
