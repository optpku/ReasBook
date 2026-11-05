module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_26_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 6.26.2:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.toRingCatSheafHom`,
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.Hom.toRingCatSheafHom f)`;
- primitive data: the morphism of ringed spaces `f : X ⟶ Y`, an `\mathcal O_Y`-module sheaf
  `𝒢`, and an `\mathcal O_X`-module sheaf `ℱ`;
- derived API: the specialized Hom-equivalence `.homEquiv 𝒢 ℱ` and its canonical bijectivity
  theorem `.bijective`.

Source/core/bridge triage:
- `source-facing`: the Stacks bijection
  `Hom_{\mathcal O_X}(f^* 𝒢, ℱ) ≃ Hom_{\mathcal O_Y}(𝒢, f_* ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
    (RingedSpace.Hom.toRingCatSheafHom f)`;
- `bridge/view`: the ringed-space specializations `f^*`, `f _*`, and the resulting specialized
  Hom-equivalence.

The previous file duplicated the ringed-space module pullback/pushforward owners already
introduced in Definition 6.26.1. This refinement deletes those parallel private definitions and
states the lemma through the existing chapter owner plus the canonical sheaf-of-modules adjunction.
-/

/- Lemma 6.26.2, owner form: for a morphism of ringed spaces `f`, the inverse-image functor on
module sheaves is left adjoint to the direct-image functor. In canonical form this is the
specialization of `SheafOfModules.pullbackPushforwardAdjunction` to
`RingedSpace.Hom.toRingCatSheafHom f`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf Y)))
variable (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))

/- Lemma 6.26.2: for a morphism of ringed spaces `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`,
an `\mathcal O_Y`-module sheaf `𝒢`, and an `\mathcal O_X`-module sheaf `ℱ`, there is a canonical
bijection
`Hom_{\mathcal O_X}(f^* 𝒢, ℱ) ≃ Hom_{\mathcal O_Y}(𝒢, f_* ℱ)`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom f)).homEquiv 𝒢 ℱ) :
    (((f^*).obj 𝒢) ⟶ ℱ) ≃
      (𝒢 ⟶ (f _*).obj ℱ))

/- Lemma 6.26.2 companion: the source bijection statement is the canonical bijectivity theorem
for the specialized adjunction equivalence above. -/
#check
  ((((SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom f)).homEquiv 𝒢 ℱ).bijective) :
    Function.Bijective
      ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom f)).homEquiv 𝒢 ℱ))

end

end AlgebraicGeometry
