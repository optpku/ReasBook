module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import stacks_project.Chap07.Definition_7_14_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Example 7.14.2:
- primary domain: morphisms of sites attached to continuous maps of topological spaces;
- sampled owner API:
  `IsMorphismOfSites`,
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `(Opens.map f).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)`;
- source/core/bridge triage:
  `source-facing`: the Stacks example asserting that a continuous map gives a morphism of sites on
  the small Zariski sites of opens;
  `core/canonical`: the owner class `IsMorphismOfSites`, whose primitive data are continuity and
  representable flatness;
  `bridge/view`: the specialization to the functor `Opens.map f`.

This file should therefore be a direct recall of the canonical instance for `Opens.map f`, not a
parallel local wrapper theorem.
-/

/- Example 7.14.2: a continuous map `f : X ⟶ Y` induces a morphism of sites
`X_{Zar} ⟶ Y_{Zar}` via inverse image of opens, i.e. via the functor
`Opens.map f : Opens Y ⥤ Opens X`. -/
#check
  (inferInstance :
    IsMorphismOfSites (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
      (Opens.map f))
