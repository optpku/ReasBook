module

public import Mathlib.CategoryTheory.Sites.Point.Comap

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe w v u₁ u₂ u₃ v₁ v₂

namespace CategoryTheory.GrothendieckTopology

/- Domain-style sampling for Lemma 7.34.2:
- primary domain: points of Grothendieck sites and inverse image along a morphism of sites;
- sampled owner declarations:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.comap`,
  `GrothendieckTopology.Point.sheafFiberComapIso`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, with the pullback
  point and its stalk comparison as derived API;
- source/core/bridge triage:
  `source-facing`: pulling back a site point along a morphism of sites and identifying the stalk
    of a pulled-back sheaf at the original point;
  `core/canonical`: the mathlib owners `Point.comap` and `Point.sheafFiberComapIso`;
  `bridge/view`: this file is recall-only, restating the textbook content directly on that
    canonical owner surface.

Primitive data are only the point `q`, the functor `u`, and the cover-preserving hypothesis `h`.
The induced point on `(C, J)` and the stalk comparison are derived API from the owner
`GrothendieckTopology.Point`, so this file should keep direct recall/use of the canonical mathlib
declarations rather than reintroducing any local wrapper.
-/

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {K : GrothendieckTopology D}
variable (q : K.Point) (u : C ⥤ D) [RepresentablyFlat u]
variable {J : GrothendieckTopology C} (h : CoverPreserving J K u)
variable [InitiallySmall (u ⋙ q.fiber).Elements]

/-
Lemma 7.34.2: a morphism of sites `(D, K) → (C, J)` given by `u : C ⥤ D` pulls a point `q` of
`(D, K)` back to a point of `(C, J)`. Mathlib states the canonical construction slightly more
generally, for a representably flat cover-preserving functor `u`, as `q.comap u h`.
-/
#check (q.comap u h : J.Point)

variable (A : Type u₃) [Category.{v} A] [HasProducts A] [u.IsContinuous J K]
variable [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
variable [HasColimitsOfSize.{w, w} A]

/-
Lemma 7.34.2: for the same data, the stalk of the pullback of a sheaf along `u` at `q` is
canonically identified with the stalk at the pulled-back point `q.comap u h`. Mathlib states
this as the canonical isomorphism `q.sheafFiberComapIso u h A`; specializing to set-valued
sheaves takes `A` to a suitable universe of types.
-/
#check
  (q.sheafFiberComapIso u h A :
    (q.comap u h).sheafFiber ≅ u.sheafPullback A J K ⋙ q.sheafFiber)

end

end CategoryTheory.GrothendieckTopology
