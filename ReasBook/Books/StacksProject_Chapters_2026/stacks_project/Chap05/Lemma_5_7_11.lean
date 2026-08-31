module

import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

variable {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X]

/- Domain-style sampling for locally connected topological spaces:
- owner abstraction: `LocallyConnectedSpace`
- same-domain declarations inspected:
  `LocallyConnectedSpace.open_connected_basis`,
  `IsOpen.locallyConnectedSpace`,
  `isOpen_connectedComponent`,
  `IsOpen.connectedComponentIn`

Layer triage:
- `source-facing`: Lemma 5.7.11 records the standard permanence/open-neighborhood consequences of
  local connectedness
- `core/canonical`: the mathlib owner class `LocallyConnectedSpace`
- `bridge/view`: no extra bridge is needed here, since clause `(4)` is already exactly the owner
  theorem `LocallyConnectedSpace.open_connected_basis`

Primitive data belongs to `LocallyConnectedSpace.open_connected_basis`, whose basis is indexed by
sets. The `OpenNhdsOf x` formulation is derived API, so this file should stop at direct canonical
recall of the owner theorem rather than introduce a parallel local bridge. -/

/- Lemma 5.7.11 (1): open subsets of a locally connected space are locally connected.
This is exactly the canonical theorem `IsOpen.locallyConnectedSpace`. -/
recall IsOpen.locallyConnectedSpace

/- Lemma 5.7.11 (2): in a locally connected space, connected components are open.
This is exactly the canonical theorem `isOpen_connectedComponent`. -/
recall isOpen_connectedComponent

/- Lemma 5.7.11 (3): for an open subset `U`, `connectedComponentIn U x` is open.
This is exactly the canonical theorem `IsOpen.connectedComponentIn`. -/
recall IsOpen.connectedComponentIn

/- Lemma 5.7.11 (4): every point of a locally connected space has a neighbourhood basis of open
connected sets. This is exactly the canonical theorem
`LocallyConnectedSpace.open_connected_basis`. -/
recall LocallyConnectedSpace.open_connected_basis
