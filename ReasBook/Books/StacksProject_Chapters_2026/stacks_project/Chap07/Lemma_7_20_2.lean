module

public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 7.20.2:
- primary domain: sheaf pushforward along cocontinuous functors of sites via right Kan extension;
- sampled owner API:
  `CategoryTheory.Functor.IsCocontinuous`,
  `CategoryTheory.ran_isSheaf_of_isCocontinuous`,
  `CategoryTheory.Functor.sheafPushforwardCocontinuous`,
  `CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`;
- source/core/bridge triage:
  `source-facing`: the statement that the presheaf pushforward of a sheaf along a cocontinuous
  functor is again a sheaf;
  `core/canonical`: the cocontinuity owner `Functor.IsCocontinuous` together with the canonical
  theorem `ran_isSheaf_of_isCocontinuous`;
  `bridge/view`: `Functor.sheafPushforwardCocontinuous`, which packages the recalled sheaf
  condition into the direct-image functor on sheaves.

Primitive data are the functor of sites, cocontinuity, pointwise right Kan extensions, and the
input sheaf. The sheaf condition on `u.op.ran.obj ℱ.obj` is derived API from the canonical theorem
`ran_isSheaf_of_isCocontinuous`, so this file should recall that theorem directly rather than
introducing a parallel local wrapper for the same construction.
-/

/- Lemma 7.20.2: if `u : \mathcal C \to \mathcal D` is cocontinuous and `ℱ` is a sheaf of sets
on `( \mathcal C, J )`, then the presheaf pushforward `${}_p u ℱ`, realized canonically in Lean
as the right Kan extension `u.op.ran.obj ℱ.obj`, is a sheaf on `( \mathcal D, K )`; equivalently,
this is the sheaf condition used to define the cocontinuous direct image on sheaves. This is the
set-valued specialization of `CategoryTheory.ran_isSheaf_of_isCocontinuous`. -/
recall CategoryTheory.ran_isSheaf_of_isCocontinuous
