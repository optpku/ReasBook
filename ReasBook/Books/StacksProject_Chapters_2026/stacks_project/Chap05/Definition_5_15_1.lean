module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for constructible and locally constructible subsets:
- inspected canonical declarations: `Topology.IsConstructible`, `Topology.IsLocallyConstructible`,
  `Topology.IsConstructible.isLocallyConstructible`, and
  `Topology.IsLocallyConstructible.iff_of_isOpenCover`.
- best owner abstractions: `Topology.IsConstructible` for constructible subsets and
  `Topology.IsLocallyConstructible` for their local form.
- primitive-vs-derived split:
  primitive data: membership in the canonical constructible-subset predicate, and membership in the
    canonical locally constructible predicate.
  derived API: the implication from constructible to locally constructible, and the source-style
    open-cover reformulation of local constructibility.

Layer triage:
- `source-facing`: Definition 5.15.1 introduces constructible and locally constructible subsets.
- `core/canonical`: the mathlib owner predicates `Topology.IsConstructible` and
  `Topology.IsLocallyConstructible`.
- `bridge/view`: `Topology.IsLocallyConstructible.iff_of_isOpenCover`, which recovers the source
  open-cover phrasing without introducing a parallel local definition.

This file should therefore stay at the direct canonical recall layer, with only a thin companion
bridge for the source open-cover formulation of local constructibility.
-/

/- Definition 5.15.1 (1) is recalled canonically by `Topology.IsConstructible`: in mathlib this is
the Boolean-subalgebra-generated notion equivalent to the Stacks source formulation by finite
unions of subsets `U ∩ Vᶜ` with `U` and `V` open and retrocompact. -/
recall IsConstructible

/- Definition 5.15.1 (2) is recalled canonically by `Topology.IsLocallyConstructible`: this is
the standard local formulation equivalent to the Stacks source open-cover condition that each
trace `E ∩ Vᵢ` be constructible in the subspace `Vᵢ`. -/
recall IsLocallyConstructible

/- Companion recall: the source open-cover formulation of local constructibility is the canonical
equivalence `Topology.IsLocallyConstructible.iff_of_isOpenCover`. -/
recall IsLocallyConstructible.iff_of_isOpenCover
