module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Lemma_4_23_2
public import stacks_project.Chap07.Definition_7_14_1
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.14.8:
- primary domain: continuous site functors and finite-limit preservation;
- sampled owner API:
  `leftExactFunctor_iff_preserves_terminal_and_pullbacks`,
  `leftExactFunctor_iff`,
  `preservesFiniteLimits_iff_flat`,
  `flat_of_preservesFiniteLimits`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the textbook reformulation of finite-limit preservation in terms of terminal
  objects and pullbacks, together with the continuous finite-limit-preserving hypothesis;
  `core/canonical`: `PreservesFiniteLimits u`, `RepresentablyFlat u`, and
  `IsMorphismOfSites J K u`;
  `bridge/view`: the Chapter 4 equivalence and the site-morphism consequence below.

Primitive data here are only the functor together with the canonical terminal/pullback
preservation hypotheses, or continuity together with finite-limit preservation. The terminal and
pullback criterion is already owned upstream by Chapter 4 through
`leftExactFunctor_iff_preserves_terminal_and_pullbacks`, and `leftExactFunctor C D u` is
definitionally `PreservesFiniteLimits u`. Representable flatness and the morphism-of-sites
structure are derived from the existing owner API, so this file should stay a thin bridge. -/

/- Remark 7.14.8: preserving terminal objects and pullbacks is exactly preserving finite limits.
This is already the Chapter 4 owner theorem
`leftExactFunctor_iff_preserves_terminal_and_pullbacks`, since `leftExactFunctor C D u` is
definitionally `PreservesFiniteLimits u`. -/
recall leftExactFunctor_iff_preserves_terminal_and_pullbacks

/- Remark 7.14.8 also uses the canonical mathlib flatness owner: over a finitely complete source
category, a finite-limit-preserving functor is representably flat. -/
recall flat_of_preservesFiniteLimits

/-- Remark 7.14.8: a continuous functor that preserves finite limits is representably flat, hence
defines a morphism of sites. -/
theorem isMorphismOfSites_of_preservesFiniteLimits
    (u : C ⥤ D) [u.IsContinuous J K] [HasFiniteLimits C] [PreservesFiniteLimits u] :
    IsMorphismOfSites J K u := by
  let _ : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  infer_instance

end
