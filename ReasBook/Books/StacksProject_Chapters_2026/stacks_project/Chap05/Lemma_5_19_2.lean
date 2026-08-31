module

import Mathlib.Topology.Inseparable
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.19.2:
- primary domain: specialization/generalization stability of subsets in a topological space
- inspected declarations:
  `StableUnderSpecialization`,
  `StableUnderGeneralization`,
  `IsClosed.stableUnderSpecialization`,
  `IsOpen.stableUnderGeneralization`,
  `stableUnderGeneralization_compl_iff`
- best owner abstraction: the canonical subset-stability predicates
  `StableUnderSpecialization` and `StableUnderGeneralization`
- primitive data: only a subset together with one of those owner predicates
- derived API: the closed/open consequences and the complement equivalence
  `stableUnderGeneralization_compl_iff`

Layer triage:
- `source-facing`: the three textbook facts relating closed sets, open sets, and complements to
  specialization/generalization stability
- `core/canonical`: `StableUnderSpecialization` and `StableUnderGeneralization`
- `bridge/view`: the canonical complement equivalence between those two owner predicates

The chapter owner entry-point is `Definition_5_19_1`, which already recalls the two predicates.
This file should therefore stay on that owner layer and recall only the derived canonical lemmas,
instead of rebuilding parallel local predicates or wrapper theorems.
-/

/- Lemma 5.19.2 (1) is recalled canonically by `IsClosed.stableUnderSpecialization`: any closed
subset of a topological space is stable under specialization. -/
recall IsClosed.stableUnderSpecialization

/- Lemma 5.19.2 (2) is recalled canonically by `IsOpen.stableUnderGeneralization`: any open
subset of a topological space is stable under generalization. -/
recall IsOpen.stableUnderGeneralization

/- Lemma 5.19.2 (3): a subset is stable under specialization if and only if its complement is
stable under generalization. This is recalled exactly by the canonical complement theorem
`stableUnderGeneralization_compl_iff`. -/
recall stableUnderGeneralization_compl_iff
