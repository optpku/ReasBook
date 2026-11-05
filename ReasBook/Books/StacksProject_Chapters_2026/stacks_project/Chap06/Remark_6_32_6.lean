module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_43_7

@[expose] public section

/- Domain-style sampling for Remark 6.32.6:
- primary domain: closed immersions of ringed spaces and their relation to the underlying closed
  embedding of topological spaces;
- sampled owner API:
  `Topology.IsClosedEmbedding`,
  `CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion`;
- best owner abstraction: the ringed-space notion (`AlgebraicGeometry.RingedSpace.IsClosedImmersion`)
  is deferred to the planned Chapter 17 owner (`Chap17.Definition_17_13_1`), which does not exist
  yet; until it lands, the only canonical closed-immersion owner available in the project is the
  topos-level one from Definition 7.43.7;
- primitive data: a morphism of ringed spaces, the closed-embedding condition on its underlying
  map, local surjectivity of `𝒪_X ⟶ i_* 𝒪_Z`, and local generators for the kernel ideal sheaf.

Source/core/bridge triage:
- `source-facing`: the deferred `AlgebraicGeometry.RingedSpace.IsClosedImmersion`
  (future Chapter 17 owner);
- `core/canonical`: `Topology.IsClosedEmbedding` for the underlying topological map;
- `bridge/view`: `CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion` for the topos-level
  analogue, recalled below.

This item should therefore not introduce a Chapter 6 wrapper. TODO: once
`Chap17.Definition_17_13_1` provides the ringed-space owner, re-point this recall at
`AlgebraicGeometry.RingedSpace.IsClosedImmersion`. -/

/- Remark 6.32.6: the relationship between closed immersions and ringed spaces is deferred in this
chapter. The ringed-space owner is planned for Chapter 17 and has not been formalized yet; the
canonical closed-immersion owner currently available in the project is the topos-level notion of
Definition 7.43.7, which this file recalls together with the underlying topological notion. -/
recall CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion
