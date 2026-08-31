module

import Mathlib.Topology.Order
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

/- Domain-style sampling for induced topologies:
- primitive owner object: `TopologicalSpace.induced`
- owner predicate on a map: `IsInducing`
- same-domain declarations inspected:
  `continuous_iff_le_induced`, `Topology.IsInducing.isOpen_iff`,
  `Topology.IsInducing.isClosed_iff`

Layer triage:
- `source-facing`: the induced topology on the domain of a map into a topological space
- `core/canonical`: `TopologicalSpace.induced` together with the owner predicate `IsInducing`
- `bridge/view`: the open/closed/continuity characterization theorems

Primitive data is just the induced topology `TopologicalSpace.induced f`; continuity, openness,
and closedness are derived API from that owner abstraction. The injectivity mentioned in the
Stacks prose is redundant for the topology owner and its basic characterization theorems, so this
file should recall the canonical owner object first and then its companion API, rather than
introducing a parallel local wrapper specialized to injective maps.
-/

/- The primitive owner object for the topology induced by a map `f` is the canonical topology
`TopologicalSpace.induced`. -/
recall TopologicalSpace.induced

/- Companion recall: the canonical map-side predicate for carrying the induced topology is
`IsInducing`. -/
recall IsInducing

/- Lemma 5.6.1 (1): for an injective map `f : Y → X`, the source statement that the induced
topology on `Y` is the weakest topology making `f` continuous is exactly the canonical theorem
`continuous_iff_le_induced`. -/
recall continuous_iff_le_induced

/- Lemma 5.6.1 (2): the open subsets of the induced topology are exactly the preimages of open
subsets of `X`, canonically expressed by `isOpen_induced_iff`. -/
recall isOpen_induced_iff

/- Lemma 5.6.1 (3): the closed subsets of the induced topology are exactly the preimages of closed
subsets of `X`, canonically expressed by `isClosed_induced_iff`. -/
recall isClosed_induced_iff
