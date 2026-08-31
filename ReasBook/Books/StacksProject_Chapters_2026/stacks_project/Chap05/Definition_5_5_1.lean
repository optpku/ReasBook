module

import Mathlib.Topology.Bases
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for topological bases:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.isTopologicalBasis_opens`,
  `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `isTopologicalBasis_generateFrom`

Layer triage:
- `source-facing`: the textbook notion that a family of subsets is a basis for the topology
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: nearby chapter lemmas such as `isTopologicalBasis_generateFrom` and
  `eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`

Primitive data is exactly the owner structure fields
`exists_subset_inter`, `sUnion_eq`, and `eq_generateFrom`. The openness and local-refinement
formulations are derived API, so this file should recall the canonical owner directly rather than
introducing a parallel local predicate or a large specification theorem.
-/

/- Definition 5.5.1: a collection of subsets of a topological space is a basis for the topology
if every basis element is open and every open set is locally refined by a basis element; this is
the canonical mathlib predicate `TopologicalSpace.IsTopologicalBasis`. -/
recall TopologicalSpace.IsTopologicalBasis
