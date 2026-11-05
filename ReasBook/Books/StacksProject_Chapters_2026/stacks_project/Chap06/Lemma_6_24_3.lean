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
public import stacks_project.Chap06.Definition_6_6_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Presheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : Y.Presheaf RingCat.{u})
variable (𝒢 : PMod(𝒪))
variable (ℱ : PMod((pullback RingCat f).obj 𝒪))

private abbrev continuousMapUnit :
    𝒪 ⟶ (pushforward RingCat f).obj ((pullback RingCat f).obj 𝒪) :=
  (pullbackPushforwardAdjunction RingCat f).unit.app 𝒪

/- Domain-style sampling for Lemma 6.24.3:
- primary domain: the pullback-pushforward adjunction for presheaves of modules along a morphism of
  presheaves of rings arising from a continuous map;
- sampled owner API:
  `PMod`,
  `TopCat.Presheaf.pullbackPushforwardAdjunction`,
  `PresheafOfModules.pullback`,
  `PresheafOfModules.pushforward`,
  `PresheafOfModules.pullbackPushforwardAdjunction`;
- source/core/bridge triage:
  `source-facing`: the canonical bijection
  `Mor_{PMod(f⁻¹𝒪)}(f⁻¹𝒢, ℱ) ≃ Mor_{PMod(𝒪)}(𝒢, f_* ℱ)`;
  `core/canonical`: the hom-equivalence of
  `PresheafOfModules.pullbackPushforwardAdjunction` specialized to the unit
  `continuousMapUnit f 𝒪`;
  `bridge/view`: the existing chapter notation `PMod(𝒪)` from Definition `6.6.1`, together with
  the identification of the target ring presheaf with `((pullback RingCat f).obj 𝒪)`.

Primitive data are only `f`, `𝒪`, `𝒢`, and `ℱ`. The bijection itself is derived API from the
canonical owner adjunction, so this item should use that owner directly rather than keep a
parallel local abbreviation. On the source-facing theorem surface, the module categories should be
written through the existing `PMod` notation rather than repeated raw owner names.
-/

/- Lemma 6.24.3: for a continuous map `f : X ⟶ Y`, a presheaf of rings `𝒪` on `Y`, a presheaf
of `𝒪`-modules `𝒢`, and a presheaf of `f_p 𝒪`-modules `ℱ`, the required canonical bijection is
exactly the hom-equivalence of `PresheafOfModules.pullbackPushforwardAdjunction`, specialized to
the unit of `TopCat.Presheaf.pullbackPushforwardAdjunction RingCat f`. -/
recall PresheafOfModules.pullbackPushforwardAdjunction

#check
  ((PresheafOfModules.pullbackPushforwardAdjunction
      (continuousMapUnit f 𝒪)).homEquiv 𝒢 ℱ :
    ((PresheafOfModules.pullback (continuousMapUnit f 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (PresheafOfModules.pushforward (continuousMapUnit f 𝒪)).obj ℱ))

end
