module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace Topology

/- Domain-style sampling for constructible pullbacks along subspace inclusions:
- owner declaration: `Topology.IsConstructible.preimage_of_isOpenEmbedding`
- same-domain project declarations: `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_of_isClosedEmbedding`, and
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`
- `source-facing`: the trace of a constructible subset on an open subspace
- `core/canonical`: `Topology.IsConstructible.preimage_of_isOpenEmbedding`
- `bridge/view`: the subtype inclusion `Subtype.val : U → X` supplies the owner input from
  `IsOpen U`
- target layer here: direct recall/use of the canonical owner theorem, since the source item adds
  no extra mathematics beyond that open-subspace specialization

Primitive data belongs to the owner theorem: an open embedding and a constructible subset. For the
subtype inclusion of an open subset, the open embedding is derived canonically from `IsOpen U`, so
this file should recall the owner rather than keep a parallel wrapper theorem.
-/

/- Lemma 5.15.4: if `U ⊆ X` is open and `E ⊆ X` is constructible, then `E ∩ U` is constructible
in the open subspace `U`. This is the open-subspace specialization of the canonical theorem
`Topology.IsConstructible.preimage_of_isOpenEmbedding`. -/
recall IsConstructible.preimage_of_isOpenEmbedding

end Topology
