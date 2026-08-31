module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

/-
Domain-style sampling for Definition 6.31.2:
- primary domain: restriction / inverse image of presheaves, sheaves, and ringed-space objects
  along the inclusion of an open subset;
- sampled owner declarations:
  `TopCat.Presheaf.pullback`,
  `TopCat.Sheaf.pullback`,
  `PresheafOfModules.pullback`,
  `SheafedSpace.restrict`;
- best owner abstraction: restriction is the canonical pullback/restriction along the open
  inclusion `U.inclusion'`; source-facing open-subset notation should be the only thin bridge,
  while the module-valued restriction functor should be exposed through the canonical owner
  `PresheafOfModules.pullback` rather than a parallel wrapper object;
- primitive data: the open inclusion `U.inclusion'`;
- derived API: restriction notation for sheaves and morphisms, and the module-valued pullback
  induced by the adjunction unit.

Source/core/bridge triage:
- `source-facing`: the open-subset restriction surface `𝒢 ↾ U` and `φ ↾ₘ U`;
- `core/canonical`: `TopCat.Presheaf.pullback`, `TopCat.Sheaf.pullback`,
  `PresheafOfModules.pullback`, and the inherited restriction construction
  `X.restrict U.isOpenEmbedding`;
- `bridge/view`: the open-subset specializations obtained by evaluating those owners at
  `U.inclusion'`.
-/

/-
Definition 6.31.2 (presheaf restriction): the restriction of a presheaf to an open subset is the
canonical pullback along the open inclusion. The owner declaration is `TopCat.Presheaf.pullback`.
-/
recall TopCat.Presheaf.pullback

/-
Definition 6.31.2 (sheaf restriction): the restriction of a sheaf to an open subset is the
canonical pullback along the open inclusion. The owner declaration is `TopCat.Sheaf.pullback`.
-/
recall TopCat.Sheaf.pullback

end

-- Sheaf restriction notation, specialized directly from the canonical pullback owner.
namespace TopCat

set_option quotPrecheck false in
scoped notation:80 𝒢:80 " ↾ " U:80 =>
  (TopCat.Sheaf.pullback _ (Opens.inclusion' U)).obj 𝒢

-- Restriction notation for sheaf morphisms, specialized directly from the same owner.
set_option quotPrecheck false in
scoped notation:80 φ:80 " ↾ₘ " U:80 =>
  (TopCat.Sheaf.pullback _ (Opens.inclusion' U)).map φ

end TopCat

noncomputable section

variable {X : TopCat.{u}}
variable (U : Opens X) (𝒪 : X.Presheaf RingCat.{u})

/- Definition 6.31.2 (presheaf-module restriction): for an open inclusion `j : U ↪ X`,
restriction of `𝒪`-modules is the canonical owner `PresheafOfModules.pullback`. -/
recall PresheafOfModules.pullback

/- Companion specialization to the open-subset inclusion `U.inclusion'`. -/
#check
  (PresheafOfModules.pullback
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪) :
    PresheafOfModules 𝒪 ⥤
      PresheafOfModules ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪))

/- Definition 6.31.2 (ringed-space restriction): the core owner is the inherited restriction
construction `SheafedSpace.restrict`; for ringed spaces this specializes to `X.restrict
U.isOpenEmbedding`. -/
recall SheafedSpace.restrict

/- Companion ringed-space specialization. -/
#check fun (X : RingedSpace.{u}) (U : Opens X.carrier) ↦ X.restrict U.isOpenEmbedding

end
