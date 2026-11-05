module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_10_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : TopCat.Sheaf RingCat.{u} Y)

/- Domain-style sampling for Lemma 6.24.6:
- primary domain: pullback and pushforward of sheaves of modules along a continuous map of
  topological spaces;
- sampled owner declarations:
  `Mod(𝒪)`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Definition_18_13_1`'s direct recall of `SheafOfModules.pullback`;
- best owner abstraction: the inverse-image functor
  `SheafOfModules.pullback ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)`;
- primitive data: the continuous map `f` and the sheaf of rings `𝒪`;
- derived API: the specialized functor
  `Mod(𝒪) ⥤ Mod((pullback RingCat.{u} f).obj 𝒪)`.

Source/core/bridge triage:
- `source-facing`: the inverse-image functor `f^{-1} : Mod(𝒪) ⥤ Mod(f^{-1}𝒪)` attached to a
  continuous map;
- `core/canonical`: `SheafOfModules.pullback`;
- `bridge/view`: the specialization along the unit of
  `pullbackPushforwardAdjunction RingCat.{u} f`, together with the chapter notation `Mod(𝒪)` from
  Definition `6.10.1`.
-/

/- Lemma 6.24.6: for a continuous map `f : X ⟶ Y` and a sheaf of rings `𝒪` on `Y`, inverse image
defines the canonical functor on sheaves of modules
`f^{-1} : \operatorname{Mod}(\mathcal O) \to \operatorname{Mod}(f^{-1}\mathcal O)`. In mathlib
this is exactly `SheafOfModules.pullback`, specialized to the unit
`𝒪 ⟶ f_* f^{-1} 𝒪` of `f^{-1} ⊣ f_*`. -/
recall SheafOfModules.pullback

#check
  (SheafOfModules.pullback
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪) :
    Mod(𝒪) ⥤ Mod((pullback RingCat.{u} f).obj 𝒪))

end
