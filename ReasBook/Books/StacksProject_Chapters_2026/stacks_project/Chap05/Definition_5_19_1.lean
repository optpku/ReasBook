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

/- Domain-style sampling for Definition 5.19.1:
- primary domain: specialization/generalization in a topological space
- owner declarations: `Specializes`, `specializes_iff_mem_closure`,
  `StableUnderSpecialization`, `StableUnderGeneralization`
- same-domain derived API: `IsClosed.stableUnderSpecialization`,
  `IsOpen.stableUnderGeneralization`, `stableUnderGeneralization_compl_iff`

Layer triage:
- `source-facing`: the Stacks terminology of specialization, generalization, and subsets stable
  under them
- `core/canonical`: the mathlib owner declarations above in `Topology.Inseparable`
- `bridge/view`: the closure characterization `specializes_iff_mem_closure`

There is no additional primitive data to define in this file. The numbered item is only recalling
existing canonical topology notions, so the correct public surface is direct `recall` of the owner
declarations rather than local aliases or wrapper definitions.
-/

/- Definition 5.19.1 (1): for points `x, x'` of a topological space, `x` is a specialization of
`x'` and `x'` is a generalization of `x` if and only if `x' ⤳ x` in the canonical specialization
relation `Specializes`. -/
recall Specializes

/- Definition 5.19.1 (1), closure characterization: the canonical equivalence
`specializes_iff_mem_closure` states that `x' ⤳ x` if and only if `x ∈ closure ({x'} : Set X)`. -/
recall specializes_iff_mem_closure

/- Definition 5.19.1 (2): a subset stable under specialization is the canonical predicate
`StableUnderSpecialization`. -/
recall StableUnderSpecialization

/- Definition 5.19.1 (3): a subset stable under generalization is the canonical predicate
`StableUnderGeneralization`. -/
recall StableUnderGeneralization
