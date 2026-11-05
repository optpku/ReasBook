module

import Mathlib.Topology.GDelta.Basic
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for nowhere dense subsets and subspace inclusions:
- owner declaration: `IsNowhereDense.image_val`
- same-domain declarations inspected:
  `IsNowhereDense`,
  `Topology.IsInducing.isNowhereDense_image`,
  `IsOpenMap.isNowhereDense_preimage`
- target layer here: `bridge/view`, since Lemma 5.21.3 is just the open-subspace specialization of
  the owner theorem for the subtype map `Subtype.val : U → X`

Primitive data is only the nowhere dense subset of the subspace. The openness of `U` from the
textbook wording is derived, not used by the canonical theorem, so it should not remain as public
API data here.
-/

/- Lemma 5.21.3: this is the open-subspace specialization of the canonical theorem
`IsNowhereDense.image_val`, whose statement is stronger because it applies to an arbitrary
subspace. -/
recall IsNowhereDense.image_val
