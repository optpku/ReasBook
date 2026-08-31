module

import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for quasi-compactness of closed subsets:
- whole-space owner: `CompactSpace`
- subset-level canonical predicate: `IsCompact`
- canonical theorem for the present lemma: `IsClosed.isCompact`
- companion reverse direction in the Hausdorff case: `IsCompact.isClosed`

Layer triage:
- `source-facing`: a closed subset of a quasi-compact space is quasi-compact
- `core/canonical`: whole-space quasi-compactness as `CompactSpace`
- `bridge/view`: subset quasi-compactness as `IsCompact`, derived from the owner theorem

Primitive data here are only the ambient `CompactSpace X` instance and the hypothesis
`IsClosed E`; the subset compactness conclusion is derived API, so this file should remain a
direct recall of `IsClosed.isCompact` rather than introducing any parallel local wrapper.
-/

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/- Lemma 5.12.3: via Definition 5.12.1, quasi-compactness of spaces is the canonical owner
`CompactSpace`, and the closed-subset consequence is exactly the canonical theorem
`IsClosed.isCompact`. -/
recall IsClosed.isCompact

end
