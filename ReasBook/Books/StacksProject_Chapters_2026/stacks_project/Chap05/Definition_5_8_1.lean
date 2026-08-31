module

import Mathlib.Topology.Irreducible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Definition 5.8.1:
- primary domain: irreducibility in point-set topology
- owner abstractions:
  `IrreducibleSpace` for irreducible spaces,
  `irreducibleComponents` for irreducible components
- same-domain declarations inspected:
  `irreducibleSpace_def`,
  `irreducibleComponents`,
  `isClosed_of_mem_irreducibleComponents`,
  `irreducibleComponents_eq_maximals_closed`

Layer triage:
- `source-facing`: the Stacks notions of an irreducible topological space and its irreducible
  components
- `core/canonical`: `IrreducibleSpace` and `irreducibleComponents X`
- `bridge/view`: `irreducibleSpace_def` and `irreducibleComponents_eq_maximals_closed`, which
  expose the textbook-form predicates without introducing a second owner

Primitive data lives at the owner level. The nonempty-univ characterization and the maximal closed
irreducible characterization are derived API and should remain companion recalls rather than
parallel local definitions.
-/

/- Canonical recall: the Stacks notion that a topological space is irreducible is the canonical
mathlib class `IrreducibleSpace`. -/
recall IrreducibleSpace

/- Companion recall: the textbook-form set-level characterization of an irreducible space is the
canonical theorem `irreducibleSpace_def`. -/
recall irreducibleSpace_def

/-
Definition 5.8.1 (2): the canonical mathlib object for irreducible components is the set
`irreducibleComponents X` of maximal irreducible subsets of `X`.
-/
recall irreducibleComponents

/- Companion recall: the source-facing maximal closed irreducible description of irreducible
components is already the canonical theorem `irreducibleComponents_eq_maximals_closed`. -/
recall irreducibleComponents_eq_maximals_closed
