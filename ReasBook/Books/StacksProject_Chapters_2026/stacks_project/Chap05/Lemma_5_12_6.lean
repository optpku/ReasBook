module

import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for finite-intersection compactness in topological spaces:
- primary domain: compactness of spaces and closed-set families
- same-domain declarations inspected:
  `CompactSpace`,
  `isCompact_univ`,
  `IsCompact.inter_iInter_nonempty`,
  `CompactSpace.iInter_nonempty`
- best owner abstraction: `CompactSpace`

Layer triage:
- `source-facing`: a family of closed subsets with the finite intersection property
- `core/canonical`: compactness of the ambient space
- `bridge/view`: the specialization from `isCompact_univ` to the whole-space theorem

Primitive data here is only the closed family together with its finite-intersection nonemptiness.
No local wrapper or parallel theorem should be kept, because the owner theorem already has the
exact source-facing interface.
-/

/- Lemma 5.12.6: in a quasi-compact topological space, a family of closed subsets with the finite
intersection property has nonempty total intersection. Via Definition 5.12.1, quasi-compact spaces
are `CompactSpace`, and this is exactly the canonical theorem `CompactSpace.iInter_nonempty`. -/
recall CompactSpace.iInter_nonempty
