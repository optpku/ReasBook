module

import Mathlib.Order.Directed
import Mathlib.Tactic.Recall

@[expose] public section

universe u

/- Domain-style sampling for Definition 4.21.1:
- primary domain: order-theoretic indexing objects used later as filtered preorder categories;
- relevant owner declarations inspected:
  `Preorder`,
  `PartialOrder`,
  `IsDirectedOrder`,
  `CategoryTheory.isFiltered_of_directed_le_nonempty`;
- best owner abstraction:
  - `source-facing`: a directed set is a preordered type equipped with `Nonempty I` and
    `IsDirectedOrder I`;
  - `core/canonical`: the owner typeclasses `Preorder`, `PartialOrder`, and `IsDirectedOrder`;
  - `bridge/view`: a nonempty directed preorder is canonically a filtered category via
    `CategoryTheory.isFiltered_of_directed_le_nonempty`;
- primitive data: the preorder relation, its reflexive/transitive structure, optional antisymmetry,
  and the directed-upper-bound condition;
- derived API: upper-bound witnesses from `exists_ge_ge` and the induced filtered-category
  structure on the associated thin category. -/

/- Source/core/bridge triage for Definition 4.21.1:
- `source-facing`: preordered sets, directed sets, partially ordered sets, and directed partially
  ordered sets.
- `core/canonical`: `Preorder`, `PartialOrder`, and `IsDirectedOrder`.
- `bridge/view`: `CategoryTheory.isFiltered_of_directed_le_nonempty` when the preorder is viewed
  as a category. -/

/- Definition 4.21.1 (1) and (2): a preorder on `I`, hence a preordered set, is the canonical
typeclass `Preorder I`. -/
recall Preorder

variable (I : Type u)

/- Definition 4.21.1 (3): on a preordered type `I`, directedness is the canonical owner
typeclass `IsDirectedOrder I`; together with `Nonempty I`, this is exactly the source notion of a
directed set. -/
section

variable [Preorder I]

#check Nonempty I
recall IsDirectedOrder

end

/- Definition 4.21.1 (4) and (5): a partial order on `I`, hence a partially ordered set, is the
canonical typeclass `PartialOrder I`. -/
recall PartialOrder

/- Definition 4.21.1 (6): since `PartialOrder I` extends `Preorder I`, a directed partially
ordered set has the same additional source data already recalled above, namely `Nonempty I` and
`IsDirectedOrder I`; no new owner declaration is needed here. -/
