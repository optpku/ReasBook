module

import Mathlib.Tactic.Recall
public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for local quasi-compactness in topological spaces:
- owner abstraction: `LocallyCompactSpace`
- same-domain declarations inspected:
  `LocallyCompactSpace`,
  `compact_basis_nhds`,
  `local_compact_nhds`,
  `LocallyCompactSpace.of_hasBasis`

Layer triage:
- `source-facing`: the Stacks neighborhood-basis formulation at each point
- `core/canonical`: `LocallyCompactSpace`
- `bridge/view`: the equivalence below between the source phrasing and the owner class

Primitive data belongs to `LocallyCompactSpace.local_compact_nhds`: every neighborhood contains a
compact neighborhood. The neighborhood-basis statement is derived API, so this file should bridge
to the owner abstraction instead of introducing a parallel wrapper definition.
-/

/- Canonical recall for the mathlib class `LocallyCompactSpace`, which is the owner abstraction
for locally quasi-compact spaces in this file. -/
recall LocallyCompactSpace

/- Companion recall: `compact_basis_nhds` is the canonical pointwise basis theorem attached to the
owner class `LocallyCompactSpace`. -/
recall compact_basis_nhds

-- Proof sketch: combine the forward direction with `compact_basis_nhds`, which gives a basis of
-- compact neighborhoods at each point, and the reverse direction with
-- `LocallyCompactSpace.of_hasBasis`, since the basis elements provided by the hypothesis are
-- already assumed compact.
/-- Definition 5.13.1: a topological space is locally quasi-compact exactly when each point has a
neighborhood-filter basis consisting of quasi-compact neighborhoods. This is the source-facing
bridge from the textbook wording to the owner class `LocallyCompactSpace`. -/
theorem locallyCompactSpace_iff_hasBasis_quasiCompact_neighborhoods :
    LocallyCompactSpace X ↔
      ∀ x, (𝓝 x).HasBasis (fun K : Set X ↦ K ∈ 𝓝 x ∧ IsCompact K) id := by
  constructor
  · intro h x
    letI := h
    simpa using compact_basis_nhds x
  · intro h
    exact LocallyCompactSpace.of_hasBasis h fun _ _ hK ↦ hK.2
