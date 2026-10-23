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
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Presheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : Y.Presheaf RingCat.{u})

/- Domain-style sampling for Lemma 6.24.2:
- primary domain: inverse image for presheaves of modules along a continuous map, obtained by
  change of rings along the unit of the presheaf pullback-pushforward adjunction;
- sampled owner API:
  `TopCat.Presheaf.pullback`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pullbackPushforwardAdjunction`;
- source/core/bridge triage:
  `source-facing`: the inverse-image functor on presheaves of modules for a continuous map
  `f : X ⟶ Y`;
  `core/canonical`: `PresheafOfModules.pullback` applied to the unit
  `((pullbackPushforwardAdjunction RingCat f).unit.app 𝒪)`;
  `bridge/view`: the identification of the target ring presheaf with
  `((pullback RingCat f).obj 𝒪)`.

Primitive data are only the continuous map `f` and the ring presheaf `𝒪`. The module pullback
functor itself is already the canonical owner `PresheafOfModules.pullback`; the adjunction unit
and the pulled-back ring presheaf are derived from the presheaf pullback owner, so this file
should recall that owner directly rather than keep a parallel local abbreviation.
-/

/- Lemma 6.24.2 (Tag 008T): for a continuous map `f : X ⟶ Y` and a presheaf of rings `𝒪` on
`Y`, inverse image on opens induces the canonical functor on presheaves of modules
`f_p : \operatorname{PMod}(\mathcal O) \to \operatorname{PMod}(f^{-1}\mathcal O)`.
In mathlib this is exactly `PresheafOfModules.pullback`, specialized to the unit of
`pullbackPushforwardAdjunction RingCat f`. -/
recall PresheafOfModules.pullback

#check
  (PresheafOfModules.pullback ((pullbackPushforwardAdjunction RingCat f).unit.app 𝒪) :
    PresheafOfModules 𝒪 ⥤ PresheafOfModules ((pullback RingCat f).obj 𝒪))

end
