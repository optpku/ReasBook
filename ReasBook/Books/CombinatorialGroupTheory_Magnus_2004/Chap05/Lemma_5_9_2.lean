/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Topology.NoetherianSpace

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable (X : Type u) [TopologicalSpace X]

/-!
Primary domain: Noetherian topological spaces and irreducible components.

Layer triage:
- `source-facing`: a Noetherian topological space `X`, its subspaces, its irreducible components,
  and the claim that each irreducible component contains a nonempty open subset of `X`.
- `core/canonical`: `TopologicalSpace.NoetherianSpace` is mathlib's owner abstraction for
  Noetherian spaces, and `irreducibleComponents X` is the owner for irreducible components.
- `bridge/view`: this file is recall-only. Each numbered clause of Lemma `5.9.2` already exists as
  a canonical owner theorem in mathlib, so the faithful refinement is direct recall rather than a
  parallel local wrapper.

Domain sampling:
1. `TopologicalSpace.NoetherianSpace.set` is the canonical subspace instance for Noetherian
   spaces.
2. `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents` is the canonical finiteness
   theorem for irreducible components of a Noetherian space.
3. `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` is the
   canonical theorem that an irreducible component of a Noetherian space contains a nonempty open
   subset.
4. `irreducibleComponents X` from `Mathlib.Topology.Irreducible` is the owner set of irreducible
   components used by the third clause.

Primitive vs. derived:
- primitive public data: the ambient topological space `X` together with the instance
  `[TopologicalSpace.NoetherianSpace X]`;
- derived API: Noetherianity of subspaces, finiteness of irreducible components, and the existence
  of a nonempty open subset inside each irreducible component.
-/

/- Lemma 5-9-2 (1): any subset of a Noetherian topological space, with the induced topology, is
Noetherian. -/
#check TopologicalSpace.NoetherianSpace.set

/- Lemma 5-9-2 (2): a Noetherian topological space has finitely many irreducible components. -/
#check TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/- Lemma 5-9-2 (3): each irreducible component of a Noetherian topological space contains a
nonempty open subset of the ambient space. -/
#check TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent

end
