module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf RingCat.{u} X}
variable (p : 𝒪₁ ⟶ 𝒪₂) (𝒢 : SheafOfModules 𝒪₁) (ℱ : SheafOfModules 𝒪₂)

local notation "J" => Opens.grothendieckTopology X

private abbrev ringSheafHomOverId :
    𝒪₁ ⟶ ((𝟭 (Opens X)).sheafPushforwardContinuous RingCat.{u} J J).obj 𝒪₂ :=
  p

/- Domain-style sampling for Lemma 6.20.2:
- primary domain: change of rings for sheaves of modules on one topological space;
- sampled owner declarations:
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  the presheaf analogue `PresheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.pullback`;
- best owner abstraction: the canonical adjunction owner
  `SheafOfModules.pullbackPushforwardAdjunction`;
- primitive data: the ring-sheaf morphism `p : 𝒪₁ ⟶ 𝒪₂` and the module sheaves `𝒢`, `ℱ`;
- derived API: the induced same-site Hom-set equivalence specialized from `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project Hom-bijection for change of rings on one space;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the identity-on-opens recasting `ringSheafHomOverId p`, kept private so no
  parallel public owner is introduced. -/

/- Lemma 6.20.2, owner form: for sheaves of modules on a topological space `X`, extension of
scalars along `p : 𝒪₁ ⟶ 𝒪₂` is left adjoint to the same-site pushforward functor, i.e. to
restriction of scalars along `p`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 6.20.2 companion: the Stacks-project Hom-set bijection is the specialized same-site
adjunction equivalence coming from
`SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId p)`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction (ringSheafHomOverId p)).homEquiv 𝒢 ℱ).symm :
    (𝒢 ⟶ (SheafOfModules.restrictScalars p).obj ℱ) ≃
      ((SheafOfModules.pullback (ringSheafHomOverId p)).obj 𝒢 ⟶ ℱ))
