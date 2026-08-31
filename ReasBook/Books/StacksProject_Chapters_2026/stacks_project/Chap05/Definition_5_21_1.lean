module

import all Mathlib.Topology.GDelta.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for interior and nowhere dense subsets:
- owner declarations: `interior`, `IsNowhereDense`
- same-domain declarations inspected: `interior_subset`, `interior_maximal`,
  `IsNowhereDense`

Layer triage:
- `source-facing`: the interior of a subset and the nowhere dense predicate on a subset
- `core/canonical`: `interior`, `IsNowhereDense`
- `bridge/view`: the largest-open-subset characterization via `interior_subset` and
  `interior_maximal`

Primitive data is only the subset `T`. The maximality property of the interior is derived API from
the owner operator `interior`, so this file should directly recall the canonical owners and their
built-in companion theorems rather than introducing any local wrapper definitions or aliases.
-/

/- Definition 5.21.1 (1): for a subset `T ⊆ X`, its interior is the canonical set `interior T`. -/
recall interior

/- Companion recall: `interior T` is contained in `T`. -/
recall interior_subset

/- Companion recall: every open subset of `T` is contained in `interior T`, so `interior T` is the
largest open subset of `X` contained in `T`. -/
recall interior_maximal

/- Definition 5.21.1 (2): the Stacks notion of a nowhere dense subset is the canonical predicate
`IsNowhereDense`, defined by `interior (closure T) = ∅`. -/
recall IsNowhereDense
