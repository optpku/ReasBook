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
- derived API: the disjoint-closure lemma recalled below

Layer triage:
- `source-facing`: the Stacks lemma that disjoint open subsets have disjoint closures
- `core/canonical`: the mathlib owner predicate `ExtremallyDisconnected`
- `bridge/view`: the owner field `ExtremallyDisconnected.open_closure`

This item should remain a direct recall of the canonical derived theorem rather than a parallel
local lemma reproving the same statement from `open_closure`.
-/

/- Lemma 5.26.3: let `X` be an extremally disconnected space. If `U, V ⊆ X` are disjoint open
subsets, then `closure U` and `closure V` are disjoint too. This is exactly the canonical mathlib
theorem `ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen`. -/
recall ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen
