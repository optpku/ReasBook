module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_14_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

section

variable {C₃ : Type u₁} [Category.{v₁} C₃]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {C₁ : Type u₃} [Category.{v₃} C₁]
variable (v : C₃ ⥤ C₂) (u : C₂ ⥤ C₁)
variable (J₃ : GrothendieckTopology C₃)
variable (J₂ : GrothendieckTopology C₂)
variable (J₁ : GrothendieckTopology C₁)
variable [IsMorphismOfSites J₃ J₂ v] [IsMorphismOfSites J₂ J₁ u]

/- Domain-style sampling for Definition 7.14.5:
- primary domain: Grothendieck topologies and morphisms of sites;
- sampled owner API:
  `IsMorphismOfSites`,
  `Functor.isContinuous_comp`,
  `RepresentablyFlat.comp`,
  `isMorphismOfSites_comp`;
- source/core/bridge triage:
  `source-facing`: composition of morphisms of sites;
  `core/canonical`: the owner class `IsMorphismOfSites`;
  `bridge/view`: the theorem `isMorphismOfSites_comp`.

No new primitive data are introduced here. Continuity and representable flatness
already live in the owner abstraction, and Lemma 7.14.4 has already packaged
their canonical composition into the theorem `isMorphismOfSites_comp`.
So this numbered definition should stay a direct recall of that theorem
rather than a parallel wrapper declaration. -/
/- Definition 7.14.5: if `v : (C₃, J₃) ⥤ (C₂, J₂)` and
`u : (C₂, J₂) ⥤ (C₁, J₁)` are morphisms of sites, then the composite functor
`v ⋙ u` again defines a morphism of sites. This file stays at the
`bridge/view` layer by recalling the chapter theorem `isMorphismOfSites_comp`,
rather than introducing a second public wrapper around the owner
`IsMorphismOfSites`. -/
recall isMorphismOfSites_comp

end
