module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [Ring R] [TopologicalSpace R]

/- Domain-style sampling for topological modules:
- primary domain: categorical limits in `TopModuleCat R` and preservation by its canonical
  forgetful functors
- sampled mathlib owner declarations:
  `TopModuleCat`,
  the instance `HasLimits (TopModuleCat R)`,
  the instance `PreservesLimits (forget₂ (TopModuleCat R) TopCat)`,
  the instance `(forget₂ (TopModuleCat R) (ModuleCat R)).IsRightAdjoint`
- sampled neighboring project declarations:
  `Definition_5_30_10` fixes `TopModuleCat` as the chapter owner for topological modules;
  `Lemma_5_30_8.topologicalRingCat_hasLimits_and_forget_preservesLimits` gives the analogous
  split source-facing declarations for topological rings;
  `Lemma_5_30_12.topModuleCat_hasColimits_and_forgetToModuleCat_preservesColimits` gives the
  analogous source-facing colimit statement.

- best owner abstraction: `TopModuleCat R`, with its object data bundled in the owner and its
  limit and preservation statements supplied by canonical instances and adjunctions

Layer triage:
- `source-facing`: the textbook lemma split into atomic limit and preservation declarations
- `core/canonical`: the owner `TopModuleCat R` and the canonical `HasLimits`/`PreservesLimits`
  instances attached to it
- `bridge/view`: none; this item is already a direct owner-level reuse

Primitive data lives in the owner `TopModuleCat R` itself: the topology, the topological additive
group structure, and scalar continuity on each object. The limit-existence and
forgetful-preservation statements are derived categorical API, so this file should stay a thin
reuse of the canonical instances rather than introduce any parallel local wrapper.

The source phrases the result for a topological ring. The sampled owner-level API, together with
the chapter's own `Definition_5_30_10`, shows that this lemma only uses the ring structure and the
ambient topology on `R`; the stronger `IsTopologicalRing R` hypothesis is therefore redundant here
and is removed from the public statement. The declaration does not generalize below `[Ring R]`
because the canonical owner `TopModuleCat R` in mathlib is itself ring-based.
-/

/-- Lemma 5.30.11 (1): the category `TopModuleCat R` of topological `R`-modules has all small
limits. -/
instance topModuleCat_hasLimits : HasLimits (TopModuleCat R) :=
  inferInstance

/-- Lemma 5.30.11 (2): the forgetful functor from `TopModuleCat R` to `TopCat` preserves all
small limits. -/
instance topModuleCat_forgetToTopCat_preservesLimits :
    PreservesLimits (forget₂ (TopModuleCat R) TopCat) :=
  inferInstance

/-- Lemma 5.30.11 (3): the forgetful functor from `TopModuleCat R` to `ModuleCat R` preserves all
small limits. -/
instance topModuleCat_forgetToModuleCat_preservesLimits :
    PreservesLimits (forget₂ (TopModuleCat R) (ModuleCat R)) :=
  inferInstance
