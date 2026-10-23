module

import Mathlib.Topology.Separation.Regular
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling for connected components in compact Hausdorff spaces:
- owner abstraction: `connectedComponent x`
- same-domain declarations inspected:
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`,
  `isTopologicalBasis_isClopen`

Layer triage:
- `source-facing`: the connected component of a point is the intersection of all open-and-closed
  subsets containing that point
- `core/canonical`: mathlib's owner theorem `connectedComponent_eq_iInter_isClopen`
- `bridge/view`: none needed here, since the source statement already matches the canonical owner
  theorem exactly

Primitive data is only the ambient compact Hausdorff space and the point `x`; there is no extra
source-defined wrapper or auxiliary construction. The refined file should therefore remain a direct
recall of the canonical theorem, not a parallel local alias or `_iff` reformulation.
-/

section

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/- Lemma 5.12.11: in a quasi-compact Hausdorff space, the connected component of a point is the
intersection of all open and closed subsets containing that point. This is exactly the canonical
mathlib theorem `connectedComponent_eq_iInter_isClopen`. -/
recall connectedComponent_eq_iInter_isClopen (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s

end
