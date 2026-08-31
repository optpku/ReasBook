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
Domain-style sampling for irreducible subsets and irreducible components:
- owner abstraction: `irreducibleComponents X` and `irreducibleComponent x`, with supporting
  owner-level lemmas in `Mathlib/Topology/Irreducible.lean`
- same-domain declarations inspected:
  `IsIrreducible.closure`,
  `isClosed_of_mem_irreducibleComponents`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `mem_irreducibleComponent`

Layer triage:
- `source-facing`: closure of irreducible sets, irreducible components, and the canonical
  irreducible component through a point
- `core/canonical`: the existing topological irreducibility API in mathlib
- `bridge/view`: `irreducibleComponent_mem_irreducibleComponents` and
  `sUnion_irreducibleComponents`

Primitive data already belongs to the owner objects `irreducibleComponents` and
`irreducibleComponent`. The statements in this file are derived owner-level API, so the correct
refinement is direct canonical recall rather than introducing any local wrapper or parallel alias.
-/

universe u

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.8.3 (1): the closure of an irreducible subset of `X` is irreducible. -/
recall IsIrreducible.closure

/- Lemma 5.8.3 (2): every irreducible component of `X` is closed. -/
recall isClosed_of_mem_irreducibleComponents

/- Lemma 5.8.3 (3): every irreducible subset of `X` is contained in an irreducible component of
`X`. -/
recall exists_mem_irreducibleComponents_subset_of_isIrreducible

/-
Lemma 5.8.3 (4): every point `x` of `X` lies in the canonical irreducible component
`irreducibleComponent x` through `x`.
-/
recall mem_irreducibleComponent

/- Companion recall: the canonical set `irreducibleComponent x` is indeed an irreducible
component of `X`. -/
recall irreducibleComponent_mem_irreducibleComponents

/-
Companion reformulation of Lemma 5.8.3 (4): `X` is the union of its irreducible
components.
-/
recall sUnion_irreducibleComponents
