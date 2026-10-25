module

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for closed retract subspaces in Hausdorff spaces:
- owner abstraction: `Function.LeftInverse.isClosed_range`
- same-domain declarations inspected:
  `Function.LeftInverse`,
  `Function.leftInverse_iff_comp`,
  `Function.LeftInverse.isClosed_range`,
  `Function.LeftInverse.isClosedEmbedding`

Layer triage:
- `source-facing`: a continuous section/retraction pair with `f ∘ s = id`
- `core/canonical`: the left-inverse owner theorem `Function.LeftInverse.isClosed_range`
- `bridge/view`: rewriting the source section/retraction equation as a `Function.LeftInverse`

Primitive data is the left-inverse relation together with continuity of the two maps. The
section/retraction equation `f ∘ s = id` is derived presentation data via
`Function.leftInverse_iff_comp`, so this file should stay a direct recall of the owner theorem
rather than keeping a parallel local closed-range wrapper.
-/

/- Lemma 5.3.3: a retract subspace of a Hausdorff space is closed. This is exactly the canonical
theorem `Function.LeftInverse.isClosed_range`. -/
recall Function.LeftInverse.isClosed_range
