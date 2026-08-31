module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_42_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/- Domain-style sampling for Lemma 7.42.6:
- primary domain: direct-image functors on sheaves of sets for continuous, almost cocontinuous
  functors of sites, specialized to pushouts and coequalizers;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous`,
  `sheafPushforwardContinuous_preservesPushouts_of_isAlmostCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks consequence that the direct image `f_*` commutes with pushouts and
  coequalizers;
  `core/canonical`: the owner property
  `PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K)`;
  `bridge/view`: the `WalkingSpan` and `WalkingParallelPair` specializations already exported in
  Lemma `7.42.5`.

Primitive data are only the site functor `u`, the two topologies, weak sheafification, and the
continuity/almost-cocontinuity hypotheses. The pushout and coequalizer statements are derived API
from the finite-connected-colimit owner of Lemma `7.42.5`, so this file should expose only those
source-facing specializations and not duplicate the stronger owner theorem on its public surface.
-/
/- Lemma 7.42.6: if `f : \mathcal D \to \mathcal C` is the morphism of sites associated to the
continuous functor `u : \mathcal C \to \mathcal D` and `u` is almost cocontinuous, then the
direct image functor `f_*`, identified here with `u.sheafPushforwardContinuous`, commutes with
pushouts and coequalizers. These are the `WalkingSpan` and `WalkingParallelPair` specializations
of the finite-connected-colimit theorem proved in Lemma `7.42.5`. -/
recall sheafPushforwardContinuous_preservesPushouts_of_isAlmostCocontinuous
recall sheafPushforwardContinuous_preservesCoequalizers_of_isAlmostCocontinuous

end

end CategoryTheory.Functor
