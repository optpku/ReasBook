module

import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: local finiteness of families of subsets in a topological space
- owner abstraction: `LocallyFinite`
- same-domain declarations inspected: `LocallyFinite`, `locallyFinite_iff_smallSets`,
  `LocallyFinite.exists_mem_basis`, `nhds_basis_opens'`

Layer triage:
- `source-facing`: the textbook notion of a locally finite family of subsets
- `core/canonical`: the mathlib owner `LocallyFinite`
- `bridge/view`: source-facing open-neighborhood consequences obtained downstream from
  `LocallyFinite.exists_mem_basis`

Primitive data are only the family of subsets. The textbook open-neighborhood wording is derived
from the owner abstraction via the neighborhood-basis API, so this file should expose the owner
directly and leave the open-set reformulation to downstream bridge lemmas when needed. -/

/- Definition 5.28.4: a family of subsets of a topological space is locally finite if every point
has a neighborhood meeting only finitely many members; this is the canonical mathlib notion
`LocallyFinite`. -/
recall LocallyFinite

/- Source-facing bridge: the neighborhood-basis formulation of local finiteness is already the
canonical theorem `LocallyFinite.exists_mem_basis`, so this file recalls it directly rather than
adding a local open-neighborhood wrapper. -/
recall LocallyFinite.exists_mem_basis
