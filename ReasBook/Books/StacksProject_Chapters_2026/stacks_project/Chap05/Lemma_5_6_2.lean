module

import Mathlib.Topology.Order
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Topology

/- Domain-style sampling for quotient topologies:
- primitive owner object: `TopologicalSpace.coinduced`
- owner predicates on a map: `IsCoinducing`, `IsQuotientMap`
- same-domain declarations inspected:
  `continuous_iff_coinduced_le`, `isOpen_coinduced`, `isClosed_coinduced`,
  `isQuotientMap_iff`

Layer triage:
- `source-facing`: the quotient topology on the codomain of a surjective map
- `core/canonical`: `TopologicalSpace.coinduced` together with the owner predicates
  `IsCoinducing` and `IsQuotientMap`
- `bridge/view`: the iff theorems translating the Stacks wording into those owner declarations

Primitive data is just the coinduced topology `TopologicalSpace.coinduced`; the “strongest
topology making `f` continuous”, open-set, and closed-set clauses are derived API. Surjectivity
does not belong to the topology itself, only to the quotient-map package, so this file should
recall the canonical owner declarations and their companion theorems rather than introducing a
parallel local quotient-topology wrapper.
-/

/- The primitive owner object for the quotient topology associated to a map `f` is the canonical
coinduced topology `TopologicalSpace.coinduced`. -/
recall TopologicalSpace.coinduced

/- Companion recall: the quotient-topology condition itself is the canonical predicate
`IsCoinducing`. -/
recall IsCoinducing

/- Companion recall: once surjectivity is added, the canonical owner predicate is
`IsQuotientMap`. -/
recall IsQuotientMap

/- Lemma 5.6.2 (1): for a surjective map `f`, the source statement that the quotient topology on
`Y` is the strongest topology making `f` continuous is exactly the canonical theorem
`continuous_iff_coinduced_le`. -/
recall continuous_iff_coinduced_le

/- Companion recall: a surjective coinducing map is exactly a quotient map. -/
recall isQuotientMap_iff

/- Lemma 5.6.2 (2): for a surjective map `f`, the source open-set characterization of the
quotient topology is exactly the canonical theorem `isOpen_coinduced`. -/
recall isOpen_coinduced

/- Lemma 5.6.2 (3): for a surjective map `f`, the source closed-set characterization of the
quotient topology is exactly the canonical theorem `isClosed_coinduced`. -/
recall isClosed_coinduced
