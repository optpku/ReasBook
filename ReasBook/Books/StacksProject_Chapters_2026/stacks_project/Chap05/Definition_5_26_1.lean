module

import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for extremal disconnectedness:
- primary domain: extremally disconnected spaces in general topology
- owner declarations sampled: `ExtremallyDisconnected`,
  `ExtremallyDisconnected.open_closure`,
  `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`,
  `CompactT2.projective_iff_extremallyDisconnected`
- canonical owner abstraction: `ExtremallyDisconnected`
- primitive data: the class field `open_closure`
- derived API: consequences such as
  `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen` and
  `CompactT2.projective_iff_extremallyDisconnected`

Layer triage:
- `source-facing`: the Stacks definition that the closure of every open subset is open
- `core/canonical`: the mathlib predicate `ExtremallyDisconnected`
- `bridge/view`: field projection `ExtremallyDisconnected.open_closure`

This item is a direct recall of the canonical owner. Keeping a separate theorem of the form
`ExtremallyDisconnected X ↔ ∀ U, IsOpen U → IsOpen (closure U)` would only restate the class field
and create an unnecessary parallel API surface.
-/

/- Definition 5.26.1: a topological space is extremally disconnected if the closure of every open
subset is open; this is the canonical mathlib predicate `ExtremallyDisconnected`. -/
recall ExtremallyDisconnected
