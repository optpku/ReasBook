module

import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {ι : Type u} {X : ι → Type v}
variable [∀ i, TopologicalSpace (X i)]

/- Domain-style sampling for Tychonoff compactness in topological spaces:
- whole-space owner: `CompactSpace`
- product-space whole-space instance: `Pi.compactSpace`
- set-level product compactness theorem: `isCompact_univ_pi`
- chapter canonicalization of quasi-compact spaces: Definition 5.12.1 identifies them with
  `CompactSpace`

Layer triage:
- `source-facing`: quasi-compactness of the product space
- `core/canonical`: `CompactSpace`
- `bridge/view`: `isCompact_univ_pi`, whose whole-space specialization gives `Pi.compactSpace`

Primitive data here is only the ambient product topology together with compactness of the factors.
No local wrapper or parallel Tychonoff declaration should be kept, because the owner instance
already has the exact source-facing meaning.
-/

/- Theorem 5.14.4 (Tychonov): if each factor `X i` is quasi-compact, then the product space
`∀ i, X i` is quasi-compact. Via Definition 5.12.1, quasi-compactness is `CompactSpace`, so this
is exactly the canonical product-space compactness instance `Pi.compactSpace`. -/
recall Pi.compactSpace

/- Companion recall: mathlib also provides the set-level Tychonoff theorem `isCompact_univ_pi`,
from which the whole-space instance `Pi.compactSpace` is derived. -/
recall isCompact_univ_pi

end
