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

/- Domain-style sampling for constructible images along subspace inclusions:
- owner declaration: `Topology.IsConstructible.image_of_isOpenEmbedding`
- same-domain chapter bridges:
  `Topology.IsConstructible.preimage_subtypeVal_of_isOpen`,
  `Topology.IsConstructible.image_subtypeVal_of_isClosed_of_isRetrocompact_compl`
- target layer here: `bridge/view`, specializing the owner theorem to the open-subspace map
  `Subtype.val : U → X`

Primitive data belongs to the owner theorem: an open embedding together with retrocompact range.
For the subtype inclusion of an open subset, both facts are derived canonically from `IsOpen U`
and `IsRetrocompact U`, so this file should recall the owner rather than keep a parallel wrapper
theorem.
-/

/- Lemma 5.15.5: if `U ⊆ X` is a retrocompact open and `E ⊆ U` is constructible in the open
subspace `U`, then `E` is constructible in `X`. This is the open-subspace specialization of the
canonical theorem `Topology.IsConstructible.image_of_isOpenEmbedding`. -/
recall IsConstructible.image_of_isOpenEmbedding

end Topology
