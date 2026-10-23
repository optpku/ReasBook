module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Example_7_21_4
public import stacks_project.Chap07.Lemma_7_22_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open TopCat

noncomputable section

universe u

/- Domain-style sampling for Example 7.21.3:
- primary domain: sheaf functors attached to the inclusion of an open subspace;
- sampled owner API:
  `Topology.IsOpenEmbedding.functor_isContinuous`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`,
  `IsOpenMap.cocontinuousPushforwardIsoSheafPushforward`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- source/core/bridge triage:
  `source-facing`: compare the sheaf functors induced by the open-subspace site functor with the
  usual restriction `j⁻¹` and direct image `j_*` for `j : U ↪ X`;
  `core/canonical`: `Topology.IsOpenEmbedding.sheafPullbackIso` for the inverse-image side and the
  Chapter 7 owner
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward` for the
  direct-image side;
  `bridge/view`: the specialization from the inclusion `Opens.inclusion' U` to those owners, in
  particular the owner-scoped open-map comparison
  `IsOpenMap.cocontinuousPushforwardIsoSheafPushforward`.

Primitive data are only the open `U` and the opens adjunction
`(Opens.isOpenEmbedding U).functor ⊣ Opens.map (Opens.inclusion' U)`. The inverse-image and
direct-image comparisons are derived owner specializations, so this file should reuse those owners
and the existing owner-scoped open-map specialization directly rather than keep parallel local comparison
isomorphisms.
-/

section

variable {X : TopCat.{u}} (U : Opens X)

/- Companion recall: the continuity of the open-subspace functor is already the canonical owner
`Topology.IsOpenEmbedding.functor_isContinuous`. -/
recall Topology.IsOpenEmbedding.functor_isContinuous

/- Companion recall: the inverse-image comparison for an open embedding is already the canonical
owner `Topology.IsOpenEmbedding.sheafPullbackIso`. -/
recall Topology.IsOpenEmbedding.sheafPullbackIso

/- Example 7.21.3, inverse-image side: for the inclusion `j : U ↪ X`, the inverse-image functor
coming from the open-subspace site functor is the inverse of the canonical open-embedding
pullback isomorphism. -/
#check
  ((Opens.isOpenEmbedding U).sheafPullbackIso (Type u)).symm

/- Companion recall: the direct-image comparison for a continuous right adjoint is owned by the
Chapter 7 theorem
`continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`. -/
recall continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward

/- Companion recall: the owner-scoped open-map specialization already packages the direct-image
comparison in the source-facing form used here. -/
recall IsOpenMap.cocontinuousPushforwardIsoSheafPushforward

/- Example 7.21.3, direct-image side: the cocontinuous pushforward attached to the open-subspace
functor agrees with the usual direct image `j_*`. -/
#check
  (Opens.isOpenEmbedding U).isOpenMap.cocontinuousPushforwardIsoSheafPushforward

end
