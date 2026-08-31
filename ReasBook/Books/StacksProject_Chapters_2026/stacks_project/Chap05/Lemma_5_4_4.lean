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
- relevant declarations inspected:
  project: `Definition_5_4_1` recalling `IsSeparatedMap`
  mathlib: `IsSeparatedMap`, `isSeparatedMap_iff_isClosed_diagonal`,
    `T2Space.isSeparatedMap`, `IsSeparatedMap.pullback`

Layer triage:
- `source-facing`: separatedness is preserved by base change
- `core/canonical`: the owner predicate `IsSeparatedMap`
- `bridge/view`: the base-change stability theorem `IsSeparatedMap.pullback`

Primitive data is only the owner predicate `IsSeparatedMap`. Closed-diagonal characterizations,
Hausdorff-source specializations, and pullback stability are derived API around that owner. Since
`Definition_5_4_1` already recalls the core owner, this lemma should remain a pure `bridge/view`
entry and reuse the exact owner theorem `IsSeparatedMap.pullback`: it already states separatedness
of the canonical second projection from the pullback and so matches the source's base-change
statement without any parallel local wrapper or extra continuity packaging.
-/

/- Lemma 5.4.4: separated maps are stable under pullback. This is exactly the canonical mathlib
bridge theorem `IsSeparatedMap.pullback`. -/
recall IsSeparatedMap.pullback
