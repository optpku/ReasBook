module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_21_2

@[expose] public section

open CategoryTheory

universe w uC' uC uD' uD vC' vC vD' vD

noncomputable section

section

variable {C' : Type uC'} [Category.{vC'} C']
variable {C : Type uC} [Category.{vC} C]
variable {D' : Type uD'} [Category.{vD'} D']
variable {D : Type uD} [Category.{vD} D]

variable {J' : GrothendieckTopology C'} {J : GrothendieckTopology C}
variable {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}

variable {u' : D' ⥤ C'} {u : D ⥤ C} {v' : C' ⥤ C} {v : D' ⥤ D}

variable [Functor.IsContinuous u K J]
variable [Functor.IsContinuous u' K' J']
variable [Functor.IsContinuous v K' K]
variable [Functor.IsContinuous v' J' J]

/- Domain-style sampling for Lemma 7.28.7:
- primary domain: Beck-Chevalley comparison for inverse-image functors on sheaf categories
  attached to a strictly commutative square of continuous functors of sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPushforwardContinuousComp`,
  `Functor.sheafPullbackComp'`;
- source/core/bridge triage:
  `source-facing`: the source's comparison between the two composites
  `f'_* ∘ (g')⁻¹` and `g⁻¹ ∘ f_*`, together with the induced comparison between the corresponding
  lower-shriek composites;
  `core/canonical`: the owner composition isomorphisms for `sheafPushforwardContinuous` and
  `sheafPullback`;
  `bridge/view`: the square-specialized comparisons below, obtained by composing the owner-level
  composition isomorphisms with the equality `v ⋙ u = u' ⋙ v'`.

Primitive data are only the commutative square of site functors and the continuity/Kan-extension
hypotheses needed to form the owner functors. Both clauses are therefore derived bridge API, so
this file should specialize the canonical composition owners directly rather than maintain
square-specific comparison declarations under new names.
-/

recall Functor.sheafPushforwardContinuousComp'
recall Functor.sheafPushforwardContinuousComp
recall Functor.sheafPullbackComp'
/- Lemma 7.28.7 (1): for a strictly commutative square `v ⋙ u = u' ⋙ v'`, the comparison
`f'_* ∘ (g')⁻¹ ≅ g⁻¹ ∘ f_*` is the square specialization of the canonical owner
`Functor.sheafPushforwardContinuousComp'`, obtained by comparing the two direct owner
specializations for `u' ⋙ v'` and `v ⋙ u`; no chapter-local wrapper is needed. -/
#check
  (fun (hcomm : v ⋙ u = u' ⋙ v') ↦
    by
      letI : Functor.IsContinuous (u' ⋙ v') K' J :=
        Functor.isContinuous_comp u' v' K' J' J
      letI : Functor.IsContinuous (v ⋙ u) K' J :=
        Functor.isContinuous_comp v u K' K J
      exact
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso hcomm.symm) (Type w) K' J' J) ≪≫
          (Functor.sheafPushforwardContinuousComp
            v u (Type w) K' K J).symm :
      (hcomm : v ⋙ u = u' ⋙ v') →
            v'.sheafPushforwardContinuous (Type w) J' J ⋙
                u'.sheafPushforwardContinuous (Type w) K' J' ≅
              u.sheafPushforwardContinuous (Type w) K J ⋙
                v.sheafPushforwardContinuous (Type w) K' K)

variable [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, u'.op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension P]
variable [∀ P : C'ᵒᵖ ⥤ Type w, v'.op.HasLeftKanExtension P]
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J' (Type w)]
variable [HasWeakSheafify K (Type w)]

/- Lemma 7.28.7 (2): the corresponding comparison between the lower-shriek composites is the
left-adjoint mate of the pushforward comparison from part (1). Under the stronger composite
left-Kan-extension hypothesis, this agrees with the square specialization of the canonical
pullback-composition owner `Functor.sheafPullbackComp'`, but the source-facing statement here
keeps only the weaker factorwise hypotheses. -/
#check
  (fun (hcomm : v ⋙ u = u' ⋙ v') ↦
    by
      letI : Functor.IsContinuous (u' ⋙ v') K' J :=
        Functor.isContinuous_comp u' v' K' J' J
      letI : Functor.IsContinuous (v ⋙ u) K' J :=
        Functor.isContinuous_comp v u K' K J
      let e :
          v'.sheafPushforwardContinuous (Type w) J' J ⋙
              u'.sheafPushforwardContinuous (Type w) K' J' ≅
            u.sheafPushforwardContinuous (Type w) K J ⋙
              v.sheafPushforwardContinuous (Type w) K' K :=
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso hcomm.symm) (Type w) K' J' J) ≪≫
          (Functor.sheafPushforwardContinuousComp
            v u (Type w) K' K J).symm
      exact
        Adjunction.leftAdjointUniq
          ((Adjunction.comp
              (u'.sheafAdjunctionContinuous (Type w) K' J')
              (v'.sheafAdjunctionContinuous (Type w) J' J)).ofNatIsoRight e)
          (Adjunction.comp
            (v.sheafAdjunctionContinuous (Type w) K' K)
            (u.sheafAdjunctionContinuous (Type w) K J)) :
      (hcomm : v ⋙ u = u' ⋙ v') →
            u'.sheafPullback (Type w) K' J' ⋙
                v'.sheafPullback (Type w) J' J ≅
              v.sheafPullback (Type w) K' K ⋙
                u.sheafPullback (Type w) K J)

end
