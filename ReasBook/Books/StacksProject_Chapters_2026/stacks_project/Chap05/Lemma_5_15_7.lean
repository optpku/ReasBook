module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

namespace Topology

/- Domain-style sampling for constructible pullbacks along subspace inclusions:
- owner declaration: `Topology.IsConstructible.preimage_of_isClosedEmbedding`
- same-domain declarations inspected: `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_of_isClosedEmbedding`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`
- `source-facing`: the closed-subspace pullback statement for a constructible subset
- `core/canonical`: `Topology.IsConstructible.preimage_of_isClosedEmbedding`
- `bridge/view`: the subtype inclusion `Subtype.val : Z → X` supplies the owner inputs from
  `IsClosed Z` and `IsCompact Zᶜ`
- target layer here: direct recall/use of the canonical owner theorem, since the source item adds
  no extra mathematics beyond that closed-subspace specialization

Primitive data belongs to the owner theorem: a closed embedding together with compact complement of
its range. For the subtype inclusion of a closed subset, both facts are derived canonically from
`IsClosed Z` and `IsCompact Zᶜ`, so this file should recall the owner rather than keep a parallel
local wheel.
-/

/- Lemma 5.15.7: if `Z ⊆ X` is closed and `Zᶜ` is quasi-compact, then the trace of a constructible
subset `E ⊆ X` on the closed subspace `Z` is constructible in `Z`. This is the closed-subspace
specialization of the canonical theorem `Topology.IsConstructible.preimage_of_isClosedEmbedding`. -/
recall IsConstructible.preimage_of_isClosedEmbedding

end Topology
