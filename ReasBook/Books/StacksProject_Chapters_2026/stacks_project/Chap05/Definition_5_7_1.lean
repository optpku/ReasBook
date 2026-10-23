module

import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Connected.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for connectedness in topological spaces:
- primary domain: connected spaces and connected components in point-set topology;
- owner abstractions: `ConnectedSpace`, `connectedComponent`;
- same-domain declarations inspected:
  `ConnectedSpace`,
  `connectedSpace_iff_clopen`,
  `connectedComponent`,
  `IsConnected.subset_connectedComponent`.

Layer triage:
- `source-facing`: the textbook criterion for connected spaces and the characterization of
  connected components as maximal connected subsets;
- `core/canonical`: `ConnectedSpace` and `connectedComponent`;
- `bridge/view`: `connectedSpace_iff_clopen` for clause `(1)`, and the maximality theorem below for
  clause `(2)`.

Primitive data belongs only to the owner declarations `ConnectedSpace` and `connectedComponent`.
The maximality clause is derived API from `connectedComponent`, but there is no exact upstream
theorem with the source-facing `Maximal IsConnected` interface, so the right refinement is a thin
bridge theorem rather than a second owner or a compatibility wrapper. -/

/- Canonical recall: the Stacks notion that a topological space is connected is the canonical
mathlib class `ConnectedSpace`. -/
recall ConnectedSpace

/- Definition 5.7.1: a topological space is connected if and only if it is nonempty and its
only clopen subsets are `∅` and `univ`. This is exactly the canonical theorem
`connectedSpace_iff_clopen`. -/
recall connectedSpace_iff_clopen

/- Canonical recall: the connected component through a point is the canonical mathlib set
`connectedComponent x`. -/
recall connectedComponent

/-
The maximality criterion for connected components is source-facing rather than a bare recall:
mathlib owns connected
components through `connectedComponent`, while the Stacks phrasing uses maximal connected subsets.
The theorem below is the minimal bridge from that source wording to the canonical owner.
-/
/-- A subset of `X` is a connected component if and only if it is a maximal
connected subset, equivalently one of the canonical sets `connectedComponent x`. This is the
source-facing bridge from the textbook maximality criterion to mathlib's owner `connectedComponent`.
-/
theorem maximal_isConnected_iff_eq_connectedComponent (T : Set X) :
    Maximal IsConnected T ↔ ∃ x : X, T = connectedComponent x := by
  constructor
  · intro hT
    obtain ⟨x, hx⟩ := hT.prop.nonempty
    exact ⟨x, hT.eq_of_subset isConnected_connectedComponent (hT.prop.subset_connectedComponent hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨isConnected_connectedComponent,
      fun S hS hsubset ↦ hS.subset_connectedComponent (hsubset mem_connectedComponent)⟩
