module

import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for total disconnectedness in topological spaces:
- owner abstraction: `TotallyDisconnectedSpace`
- canonical source-facing bridge:
  `totallyDisconnectedSpace_iff_connectedComponent_singleton`
- same-domain declarations inspected:
  `TotallyDisconnectedSpace`,
  `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`,
  `totallyDisconnectedSpace_iff_connectedComponent_singleton`,
  `connectedComponent_eq_singleton`

Layer triage:
- `source-facing`: the textbook criterion that connected components are singletons
- `core/canonical`: the mathlib owner class `TotallyDisconnectedSpace`
- `bridge/view`: the equivalence between the textbook criterion and the owner class

Primitive data belongs to the owner class `TotallyDisconnectedSpace`. The connected-component
singleton criterion is derived API, so this file should recall the owner first and keep the
criterion as a companion bridge. -/

/- Canonical recall for the mathlib class `TotallyDisconnectedSpace`, which is the owner
abstraction for this definition. -/
recall TotallyDisconnectedSpace

/- Definition 5.7.8: a topological space is totally disconnected if all of its connected
components are singletons. This is the canonical bridge between the textbook criterion and the
owner class `TotallyDisconnectedSpace`. -/
recall totallyDisconnectedSpace_iff_connectedComponent_singleton
