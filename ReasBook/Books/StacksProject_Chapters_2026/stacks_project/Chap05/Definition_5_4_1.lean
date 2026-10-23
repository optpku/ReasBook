module

import Mathlib.Topology.SeparatedMap
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for separated maps:
- owner abstraction: `IsSeparatedMap`
- same-domain declarations inspected:
  `IsSeparatedMap`,
  `isSeparatedMap_iff_isClosed_diagonal`,
  `T2Space.isSeparatedMap`,
  `IsSeparatedMap.pullback`

Layer triage:
- `source-facing`: the textbook notion that a map is separated
- `core/canonical`: `IsSeparatedMap`
- `bridge/view`: the closed-diagonal criterion and pullback stability theorems

Primitive data is exactly the owner predicate: points in one fiber can be separated by disjoint
open neighborhoods. The closed-diagonal criterion, Hausdorff-source specialization, and pullback
stability are derived API around that owner. The source's continuity hypothesis is redundant for
the core predicate, so this file should recall the canonical owner directly rather than
introducing a parallel local predicate or a large `_iff` wrapper as the main entry.
-/

/-
Definition 5.4.1: the textbook separatedness condition for a continuous map of topological spaces
is the canonical mathlib predicate `IsSeparatedMap`.
-/
recall IsSeparatedMap
