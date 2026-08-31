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
  mathlib: `IsSeparatedMap`, `T2Space.isSeparatedMap`,
    `isSeparatedMap_iff_isClosed_diagonal`, `IsSeparatedMap.pullback`

Layer triage:
- `source-facing`: a map from a Hausdorff source is separated
- `core/canonical`: the owner predicate `IsSeparatedMap`
- `bridge/view`: `T2Space.isSeparatedMap`, which produces the owner predicate from the Hausdorff
  source hypothesis

Primitive data is only the owner predicate `IsSeparatedMap`; Hausdorffness of the source is a
canonical sufficient hypothesis, not extra primitive data. Since `Definition_5_4_1` already
recalls the owner, this lemma should stay at the `bridge/view` layer and reuse the exact
owner-attached theorem `T2Space.isSeparatedMap` rather than introduce a parallel local theorem
with the redundant continuity hypothesis from the source prose.
-/

/- Lemma 5.4.3: a continuous map from a Hausdorff topological space is a separated map. The
canonical bridge theorem is `T2Space.isSeparatedMap`, whose statement already drops the redundant
continuity hypothesis. -/
recall T2Space.isSeparatedMap
