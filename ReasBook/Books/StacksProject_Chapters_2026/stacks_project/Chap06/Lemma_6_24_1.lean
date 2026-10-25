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


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Presheaf PresheafOfModules TopologicalSpace

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf RingCat.{u})

/- Domain-style sampling for Lemma 6.24.1:
- primary domain: direct image for presheaves of modules along a continuous map, obtained by
  reindexing along the induced map of opens;
- sampled owner API:
  `TopCat.Presheaf.pushforward`,
  `Opens.map`,
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.pushforward`;
- source/core/bridge triage:
  `source-facing`: the direct-image functor
  `f_* : \operatorname{PMod}(\mathcal O) \to \operatorname{PMod}(f_* \mathcal O)`;
  `core/canonical`: `pushforward₀ (Opens.map f) 𝒪`;
  `bridge/view`: the identification of the target ring presheaf with
  `((pushforward RingCat f).obj 𝒪)`.

Primitive data are only the continuous map `f` and the ring presheaf `𝒪` on `X`. The direct-image
functor itself is already the canonical owner `pushforward₀`, so this item should recall that
owner directly rather than keep any parallel local alias.
-/

/- Lemma 6.24.1 (Tag 008S): for a continuous map `f : X ⟶ Y` and a presheaf of rings `𝒪` on
`X`, direct image on opens induces the canonical functor
`f_* : \operatorname{PMod}(\mathcal O) \to \operatorname{PMod}(f_* \mathcal O)`.
In mathlib this is exactly `pushforward₀`, specialized to the map of opens `Opens.map f`. -/
#check (pushforward₀ (Opens.map f) 𝒪 :
  PresheafOfModules 𝒪 ⥤ PresheafOfModules ((pushforward RingCat f).obj 𝒪))

end
