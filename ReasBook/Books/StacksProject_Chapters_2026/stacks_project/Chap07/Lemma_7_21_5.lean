module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe t u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/- Domain-style sampling for Lemma 7.21.5:
- primary domain: the continuous sheaf functor on set-valued sheaves induced by precomposition
  with `u.op`, together with its left adjoint from sheafified left Kan extension and, in the
  cocontinuous case, its right adjoint given by cocontinuous sheaf pushforward;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks functor on sheaves obtained from precomposition with `u.op`, its
  left adjoint `g_!`, and the fact that this functor commutes with arbitrary limits and colimits
  once both adjunctions are available;
  `core/canonical`: the owner central to this file is
  `u.sheafPushforwardContinuous (Type t) J K`; separately, Lemma 7.21.1 packages a cocontinuous
  morphism of topoi whose inverse-image owner is
  `u.sheafPullbackCocontinuous (Type t) J K`, so these two owner packages must not be conflated;
  `bridge/view`: `u.sheafPushforwardContinuousCompSheafToPresheafIso` identifies the underlying
  presheaf of the continuous sheaf functor, `u.sheafPullbackConstruction.sheafAdjunctionContinuous
  (Type t) J K` gives its left adjoint, and `u.sheafAdjunctionCocontinuous (Type t) J K` gives
  the same functor as a left adjoint to the cocontinuous direct image.

Primitive data are the site functor `u`, continuity for the continuous owner, and the
cocontinuity/Kan-extension hypotheses only where the direct-image side is needed. The comparison
isomorphism and the limit/colimit-preservation facts are derived API. In particular, clause `(3)`
should be phrased on the continuous owner `u.sheafPushforwardContinuous (Type t) J K` through its
`IsRightAdjoint` and `IsLeftAdjoint` structures, rather than by identifying it with the
inverse-image field of `u.morphismOfTopoiInOfCocontinuous J K` or introducing a parallel local
wrapper. -/

/- Lemma 7.21.5 (1): the continuous sheaf functor attached to a functor of sites `u`, realized in
Lean by `u.sheafPushforwardContinuous (Type t) J K`, is already given on underlying presheaves by
precomposition with `u.op`, so no further sheafification is needed. The recalled owner itself only
uses the continuous half of the hypotheses. -/
recall Functor.sheafPushforwardContinuousCompSheafToPresheafIso

/- Lemma 7.21.5 (2): the source-facing left adjoint `g_!` to this continuous sheaf functor is
realized by the sheafified left Kan extension along `u.op`. The recalled owner is the adjunction
between that construction and `u.sheafPushforwardContinuous (Type t) J K`. -/
recall Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

/- Lemma 7.21.5 (3): in the cocontinuous case, the canonical adjunction
`u.sheafAdjunctionCocontinuous (Type t) J K` exhibits the same continuous owner
`u.sheafPushforwardContinuous (Type t) J K` as left adjoint to the cocontinuous direct-image
functor `u.sheafPushforwardCocontinuous (Type t) J K`. This is the second adjunction carried by
the continuous owner; it should not be identified with the inverse-image field of
`u.morphismOfTopoiInOfCocontinuous J K`, whose owner is instead
`u.sheafPullbackCocontinuous (Type t) J K`. The main entry here therefore recalls the adjunction
owner itself rather than repackaging its `IsLeftAdjoint` view as a parallel local declaration. -/
recall Functor.sheafAdjunctionCocontinuous

section RightAdjoint

variable [u.IsContinuous J K]
variable [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]

/- Lemma 7.21.5 (3), limit part: once the source-facing left adjoint `g_!` from clause `(2)` is
constructed, the continuous owner `u.sheafPushforwardContinuous (Type t) J K` commutes with
arbitrary limits because it is a right adjoint. This is the generic owner-level instance induced
by `Adjunction.rightAdjoint_preservesLimits`, so no parallel local theorem is kept here. -/
#synth PreservesLimits (u.sheafPushforwardContinuous (Type t) J K)

end RightAdjoint

section LeftAdjoint

variable [u.IsContinuous J K]
variable [(u.sheafPushforwardContinuous (Type t) J K).IsLeftAdjoint]

/- Lemma 7.21.5 (3), colimit part: when the same continuous owner
`u.sheafPushforwardContinuous (Type t) J K` carries the left-adjoint structure supplied in the
cocontinuous case by `u.sheafAdjunctionCocontinuous (Type t) J K`, it commutes with arbitrary
colimits as well. This is the generic owner-level instance induced by
`Adjunction.leftAdjoint_preservesColimits`, so no parallel local theorem is kept here. -/
#synth PreservesColimits (u.sheafPushforwardContinuous (Type t) J K)

end LeftAdjoint

end
