module

import Mathlib.Topology.Irreducible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for irreducible subsets in point-set topology:
- best owner abstraction: the predicate `IsIrreducible` and its owner-level API in
  `Mathlib/Topology/Irreducible.lean`
- same-domain declarations inspected:
  `IsIrreducible.image`,
  `IsIrreducible.closure`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `irreducibleComponent_mem_irreducibleComponents`

Layer triage:
- `source-facing`: irreducibility of a subset and its behavior under continuous maps
- `core/canonical`: the existing mathlib irreducibility API
- `bridge/view`: irreducible components as canonical maximal irreducible supersets

Primitive data here is just the owner predicate `IsIrreducible`; there is no additional local data
or wrapper structure to package. Since Lemma 5.8.2 is exactly the owner theorem for images, the
correct refinement is a direct canonical recall rather than a parallel local theorem shell.
-/

/- Lemma 5.8.2: the image of an irreducible subset under a continuous map is irreducible.
This is exactly the canonical theorem `IsIrreducible.image`. -/
recall IsIrreducible.image
