module

import Mathlib.Topology.NoetherianSpace
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for finite unions of Noetherian subspaces:
- primary domain: Noetherian topological spaces and finite unions of Noetherian subspaces
- sampled owner declarations:
  `TopologicalSpace.NoetherianSpace`,
  `TopologicalSpace.NoetherianSpace.set`,
  `TopologicalSpace.NoetherianSpace.range`,
  `TopologicalSpace.NoetherianSpace.iUnion`
- best owner abstraction: the canonical owner is `TopologicalSpace.NoetherianSpace`
- primitive data: a finite family `Xᵢ ⊆ X` together with `NoetherianSpace Xᵢ` for each index
- derived API: the induced Noetherianity of the union, already exposed upstream as the owner theorem
  `TopologicalSpace.NoetherianSpace.iUnion`

Layer triage:
- `source-facing`: Lemma 5.9.4, asserting that a finite union of Noetherian subspaces is
  Noetherian
- `core/canonical`: `TopologicalSpace.NoetherianSpace.iUnion`
- `bridge/view`: none needed, since the source statement already coincides with the owner theorem

This file should therefore stay as a direct canonical recall rather than introducing a parallel
local lemma or an unpacked specification theorem.
-/

/- Lemma 5.9.4: if `X` is a topological space and `Xᵢ ⊆ X` is a finite family of subsets such
that each `Xᵢ` is Noetherian with the induced topology, then the union `⋃ i, Xᵢ` is Noetherian
with the induced topology. This is exactly the canonical theorem
`TopologicalSpace.NoetherianSpace.iUnion`. -/
recall TopologicalSpace.NoetherianSpace.iUnion
