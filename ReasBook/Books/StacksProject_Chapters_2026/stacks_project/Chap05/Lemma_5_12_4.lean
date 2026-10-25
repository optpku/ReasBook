module

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling for quasi-compact subsets in Hausdorff spaces:
- whole-space owner: `CompactSpace`
- subset-level canonical predicate: `IsCompact`
- canonical closedness theorem: `IsCompact.isClosed`
- canonical separation theorem: `SeparatedNhds.of_isCompact_isCompact`

Layer triage:
- `source-facing`: a quasi-compact subset of a Hausdorff space is closed, and disjoint
  quasi-compact subsets admit disjoint open neighborhoods
- `core/canonical`: `IsCompact` in a `T2Space`
- `bridge/view`: `SeparatedNhds` as the owner-style formulation of disjoint open neighborhoods

Primitive data here are only the ambient topology and Hausdorff structure. The closedness and
separation conclusions are derived API from the canonical compactness owner, so this file should
stay a direct recall of the upstream theorems rather than reintroducing local wrapper lemmas.
-/
section

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/- Lemma 5.12.4: in a Hausdorff space, every quasi-compact subset is closed. In mathlib the
Stacks quasi-compactness condition for subsets is the canonical predicate `IsCompact`, and the
statement is exactly the canonical theorem `IsCompact.isClosed`. -/
recall IsCompact.isClosed

/- Companion recall: in a Hausdorff space, disjoint quasi-compact subsets admit disjoint open
neighborhoods. In mathlib this is the canonical separation statement
`SeparatedNhds.of_isCompact_isCompact`; by definition, `SeparatedNhds E F` is exactly the
existence of disjoint open neighborhoods of `E` and `F`. -/
recall SeparatedNhds.of_isCompact_isCompact

end
