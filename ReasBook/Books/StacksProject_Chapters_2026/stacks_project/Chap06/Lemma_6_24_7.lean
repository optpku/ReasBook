module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_24_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf RingCat.{u} Y)
variable (𝒢 : SheafOfModules 𝒪)
variable (ℱ : SheafOfModules ((pullback RingCat.{u} f).obj 𝒪))

/- Domain-style sampling for Lemma 6.24.7:
- primary domain: the pullback-pushforward adjunction for sheaves of modules along a continuous
  map;
- sampled owner declarations:
  `TopCat.Sheaf.pullbackPushforwardAdjunction`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  the recall/check surface in `Lemma_18_12_3` and `Lemma_18_13_2` for the same owner abstraction;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)`;
- primitive data: the continuous map `f`, the sheaf of rings `𝒪`, and the module sheaves `𝒢`,
  `ℱ`;
- derived API: the specialized Hom-equivalence `.homEquiv 𝒢 ℱ` and its canonical bijectivity
  theorem `.bijective`.

Source/core/bridge triage:
- `source-facing`: the canonical bijection
  `Mor_{Mod(f^{-1}𝒪)}(f^{-1}𝒢, ℱ) ≃ Mor_{Mod(𝒪)}(𝒢, f_*ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
    ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)`;
- `bridge/view`: the specialization of `.homEquiv` to `𝒢` and `ℱ`.

This file should therefore recall the owner adjunction directly and reuse its derived API via
`.homEquiv` and `.bijective`, with no parallel local abbreviation for the unit map and no exact-
interface wrapper theorem for bijectivity.
-/

/- Lemma 6.24.7, owner form: for the unit map `𝒪 ⟶ f_* f^{-1} 𝒪` induced by `f`, the
inverse-image functor on sheaves of `𝒪`-modules is left adjoint to the direct-image functor on
sheaves of `f^{-1}𝒪`-modules. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.24.7: for a continuous map `f : X ⟶ Y`, a sheaf of rings `𝒪` on `Y`, a sheaf of
`𝒪`-modules `𝒢`, and a sheaf of `f^{-1} 𝒪`-modules `ℱ`, morphisms
`f^{-1} 𝒢 ⟶ ℱ` of `f^{-1} 𝒪`-modules are canonically equivalent to morphisms
`𝒢 ⟶ f_* ℱ` of `𝒪`-modules, where `f_* ℱ` is viewed as an `𝒪`-module via
`𝒪 ⟶ f_* f^{-1} 𝒪`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).obj ℱ))

/- Lemma 6.24.7 companion: the source bijection statement is exactly the canonical bijectivity
theorem for the specialized adjunction equivalence. -/
#check
  ((((SheafOfModules.pullbackPushforwardAdjunction
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).homEquiv 𝒢 ℱ).bijective) :
    Function.Bijective
      ((SheafOfModules.pullbackPushforwardAdjunction
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒪)).homEquiv 𝒢 ℱ))

end
