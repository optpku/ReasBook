module

import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Gleason's minimal compact surjective subsets:
- primary domain: compactness/Zorn-minimality for continuous surjections in general topology
- sampled owner declarations:
  `exists_compact_surjective_zorn_subset`,
  `image_subset_closure_compl_image_compl_of_isOpen`,
  `ExtremallyDisconnected.homeoCompactToT2`
- best owner abstraction for this item: the theorem
  `exists_compact_surjective_zorn_subset`

Layer triage:
- `source-facing`: the Stacks formulation using a compact subset `E ⊆ X`
- `core/canonical`: mathlib's owner theorem `exists_compact_surjective_zorn_subset`, phrased with
  `CompactSpace E` for the subtype
- `bridge/view`: the equivalent `IsCompact E` restatement, which should stay companion-only if
  needed downstream

Primitive data is only the continuous surjection. The compactness of the chosen subset is derived
from the owner theorem. A local theorem obtained only by rewriting `CompactSpace E` as
`IsCompact (E : Set X)` would be a duplicate wrapper around the canonical owner rather than new
source-level mathematics, so this item should refine to direct recall/use of the owner theorem.
-/

/- Lemma 5.26.5: the canonical owner theorem
`exists_compact_surjective_zorn_subset` already gives exactly the Stacks minimal-surjective-subset
construction, packaging the chosen subset through the compact subtype `E`. Keeping a second theorem
that only rewrites this as `IsCompact (E : Set X)` would create redundant API. -/
recall exists_compact_surjective_zorn_subset
