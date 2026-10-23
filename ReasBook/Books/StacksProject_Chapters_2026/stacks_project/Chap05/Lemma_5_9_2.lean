module

import Mathlib.Topology.NoetherianSpace
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 5.9.2:
- primary domain: Noetherian topological spaces and irreducible components
- sampled owner declarations:
  `TopologicalSpace.NoetherianSpace.set`,
  `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`,
  `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`,
  `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`
- best owner abstraction: the canonical owner is `TopologicalSpace.NoetherianSpace`
- primitive data: the ambient `NoetherianSpace X` instance
- derived API: Noetherianity of subspaces, finiteness of `irreducibleComponents X`, and the
  existence of a nonempty open subset inside an irreducible component

Layer triage:
- `source-facing`: the three textbook consequences recorded in Lemma 5.9.2
- `core/canonical`: the existing `TopologicalSpace.NoetherianSpace` API in mathlib
- `bridge/view`: none needed here, since each clause already has the exact canonical owner-side
  statement

The current file stored only derived API as parallel local theorem names. Since the owner object
and the exact interfaces already exist upstream, the right refinement is direct canonical recall.
-/

/- Lemma 5.9.2 (1): every subspace of a Noetherian topological space is Noetherian. -/
recall TopologicalSpace.NoetherianSpace.set

/- Lemma 5.9.2 (2): a Noetherian topological space has only finitely many irreducible
components. -/
recall TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/- Lemma 5.9.2 (3): every irreducible component of a Noetherian topological space contains a
nonempty open subset of the ambient space. -/
recall TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
