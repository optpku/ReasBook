module

import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for connected components and totally disconnected targets:
- owner abstractions:
  `ConnectedComponents`,
  `TotallyDisconnectedSpace`
- same-domain declarations inspected:
  `ConnectedComponents.totallyDisconnectedSpace`,
  `Continuous.connectedComponentsLift`,
  `Continuous.connectedComponentsLift_comp_coe`,
  `Continuous.connectedComponentsLift_unique`

Layer triage:
- `source-facing`: the quotient of a space by connected components and the universal factorization
  of a continuous map into a totally disconnected space
- `core/canonical`: the quotient owner `ConnectedComponents` together with the owner class
  `TotallyDisconnectedSpace`
- `bridge/view`: the canonical lift `Continuous.connectedComponentsLift` and its factorization and
  uniqueness theorems

Primitive data are only the quotient owner `ConnectedComponents X`, the target owner class
`TotallyDisconnectedSpace Y`, and a continuous map `f : X → Y`. Total disconnectedness of the
quotient and the universal factorization statements are derived API already owned by mathlib, so
this file should remain a pure recall of those canonical declarations rather than introduce any
parallel local wrapper.
-/
/- Lemma 5.7.9 (first assertion): the quotient of `X` by its connected components is totally
disconnected. This is the canonical mathlib instance
`ConnectedComponents.totallyDisconnectedSpace`. -/
recall ConnectedComponents.totallyDisconnectedSpace

variable {Y : Type v} [TopologicalSpace Y] [TotallyDisconnectedSpace Y]

/- Lemma 5.7.9 (second assertion): for a continuous map `f : X → Y` into a totally disconnected
space, the canonical factorization through `X → ConnectedComponents X` is
`Continuous.connectedComponentsLift`; its continuity, factorization identity, and uniqueness are
the recalled facts below. -/
recall Continuous.connectedComponentsLift
recall Continuous.connectedComponentsLift_continuous
recall Continuous.connectedComponentsLift_comp_coe
recall Continuous.connectedComponentsLift_unique
