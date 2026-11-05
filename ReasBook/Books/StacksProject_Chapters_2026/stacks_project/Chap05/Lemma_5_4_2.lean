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
    `isSeparatedMap_iff_isClosedEmbedding`

Layer triage:
- `source-facing`: the textbook diagonal criterion for a separated map
- `core/canonical`: the owner predicate `IsSeparatedMap`
- `bridge/view`: the diagonal-closedness and closed-embedding criteria attached to that owner

Primitive data is only the owner predicate `IsSeparatedMap`. The closedness of the pullback
diagonal is derived API expressing the same notion canonically. Since `Definition_5_4_1` already
exposes the core owner, this file should stay at the `bridge/view` layer and recall the exact
owner-attached bridge theorem directly, rather than introducing a second local theorem shell or a
duplicated diagonal-closedness wrapper.
-/

/- Lemma 5.4.2: for a continuous map of topological spaces, being separated is equivalent to the
closedness of the diagonal subset `Δ(X) ⊆ X ×_Y X`. This is the exact canonical bridge theorem
`isSeparatedMap_iff_isClosed_diagonal`, used here as the `bridge/view` companion to
`Definition_5_4_1`; its statement already drops the redundant continuity and target-topology
hypotheses. -/
recall isSeparatedMap_iff_isClosed_diagonal
