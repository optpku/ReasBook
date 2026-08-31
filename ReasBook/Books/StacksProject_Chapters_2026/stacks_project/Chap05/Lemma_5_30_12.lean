module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R] [TopologicalSpace R]

/- Domain-style sampling for topological modules:
- primary domain: categorical colimits in `TopModuleCat R` and preservation by its canonical
  forgetful functor to `ModuleCat R`
- sampled mathlib owner declarations:
  `TopModuleCat`,
  the instance `HasColimits (TopModuleCat R)`,
  `TopModuleCat.indiscreteAdj`,
  the instance `(forget₂ (TopModuleCat R) (ModuleCat R)).IsLeftAdjoint`
- sampled neighboring project declarations:
  `Definition_5_30_10` fixes `TopModuleCat` as the chapter owner for topological modules;
  `Lemma_5_30_11.topModuleCat_hasLimits_and_forget_preservesLimits` packages the analogous limit
  consequences directly from canonical instances.

- best owner abstraction: `TopModuleCat R`

Layer triage:
- `source-facing`: this lemma packages the source consequence that `TopModuleCat R` has colimits
  and that the forgetful functor to `ModuleCat R` preserves them
- `core/canonical`: the owner `TopModuleCat R`, its canonical `HasColimits` instance, and the
  left-adjoint structure on `forget₂ (TopModuleCat R) (ModuleCat R)`
- `bridge/view`: none; the item is already a thin consequence of the owner-level API

Primitive data lives in the owner `TopModuleCat R`: topology, additive continuity, and scalar
continuity on each module. Colimit existence and preservation by the forgetful functor are derived
categorical API, so this file should only package the canonical instances rather than duplicate
them behind a local wrapper.

As in the neighboring limit lemma, the stronger `IsTopologicalRing R` hypothesis is redundant for
this statement: the sampled owner-level colimit and adjunction API only requires `[Ring R]` and
`[TopologicalSpace R]`.
-/

/-- Lemma 5.30.12: for a ring `R` with a topology, the category `TopModuleCat R` of topological
modules over `R` has arbitrary colimits, and the forgetful functor to `ModuleCat R` preserves
these colimits. -/
theorem topModuleCat_hasColimits_and_forgetToModuleCat_preservesColimits :
    HasColimits (TopModuleCat R) ∧
      PreservesColimits (forget₂ (TopModuleCat R) (ModuleCat R)) :=
  ⟨inferInstance, inferInstance⟩
