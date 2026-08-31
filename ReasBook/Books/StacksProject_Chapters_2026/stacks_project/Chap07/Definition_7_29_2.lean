module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_29_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

/- Domain-style sampling for Definition 7.29.2:
- primary domain: dense-subsite comparison for sheaf topoi and cocontinuous direct images;
- sampled owner API:
  `CategoryTheory.Functor.IsDenseSubsite`,
  `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`,
  `CategoryTheory.sourceLocal_isDenseSubsite`,
  `CategoryTheory.Functor.sheafPushforwardCocontinuous`,
  `CategoryTheory.Adjunction.isEquivalence_right_of_isEquivalence_left`;
- source/core/bridge triage:
  `source-facing`: the Stacks notion of a special cocontinuous functor;
  `core/canonical`: the dense-subsite owner `Functor.IsDenseSubsite`;
  `bridge/view`: the pointwise right Kan extension data needed to realize the cocontinuous direct
  image on sheaves of sets, and the resulting equivalence instance.

Primitive data are only the dense-subsite owner data expressing the comparison-lemma hypotheses.
The set-valued pointwise right Kan extension hypotheses are bridge data needed to realize the
cocontinuous direct image on sheaves of sets, and the resulting equivalence is derived API from
that owner plus those extra hypotheses.
-/

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Definition 7.29.2: the Stacks notion of a special cocontinuous functor is owned canonically by
`G.IsDenseSubsite J K`; this file keeps only the cocontinuous direct-image bridge under the extra
pointwise right Kan extension hypotheses. -/
recall Functor.IsDenseSubsite

namespace IsDenseSubsite

/-- A dense-subsite functor has cocontinuous direct image on `Type w`-valued sheaves an
equivalence whenever the corresponding pointwise right Kan extensions exist. -/
theorem sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
    (G : C ⥤ D) [G.IsDenseSubsite J K]
    [∀ P : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := by
  letI : IsSourceLocallyFaithful G J := ⟨fun a b h ↦ equalizer_mem J K G a b h⟩
  letI : IsSourceLocallyFull G J := ⟨fun c ↦ imageSieve_mem J K G c⟩
  letI : G.IsCoverDense K := isCoverDense J K G
  exact comparison_directImage_isEquivalence G

/-- A dense-subsite functor has cocontinuous direct image on sheaves of sets an
equivalence whenever the corresponding pointwise right Kan extensions exist. -/
instance sheafPushforwardCocontinuous_isEquivalence
    (G : C ⥤ D) [G.IsDenseSubsite J K]
    [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).IsEquivalence :=
  sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension G

end IsDenseSubsite

end Functor
end CategoryTheory
