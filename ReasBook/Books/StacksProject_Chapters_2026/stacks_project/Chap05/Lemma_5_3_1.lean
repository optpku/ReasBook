module

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Hausdorff diagonal criteria:
- owner abstraction: the separation owner `T2Space`, with canonical diagonal criterion
  `t2_iff_isClosed_diagonal`
- same-domain declarations inspected:
  `t2_iff_isClosed_diagonal`,
  `isClosed_diagonal`,
  `isClosed_eq`,
  `t2Space_iff_of_isOpenQuotientMap`

Layer triage:
- `source-facing`: the textbook criterion that `X` is Hausdorff exactly when the diagonal
  `diagonal X ⊆ X × X` is closed
- `core/canonical`: the owner theorem `t2_iff_isClosed_diagonal` for the separation class
  `T2Space`
- `bridge/view`: derived diagonal and equalizer consequences such as `isClosed_diagonal` and
  `isClosed_eq`

Primitive data is only the ambient topological space together with its diagonal subset
`diagonal X`. The closed-diagonal criterion is already the canonical owner statement, while
closedness of the diagonal under `[T2Space X]` and equalizer-closedness are derived API. This file
should therefore recall the owner theorem directly instead of introducing a parallel local
Hausdorff predicate or a duplicate diagonal-closedness wrapper.
-/

/- Lemma 5.3.1: a topological space is Hausdorff if and only if its diagonal in `X × X` is
closed. This is the canonical mathlib theorem `t2_iff_isClosed_diagonal`. -/
recall t2_iff_isClosed_diagonal
