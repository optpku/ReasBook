module

public import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for local connectedness in topological spaces:
- owner abstraction: `LocallyConnectedSpace`
- canonical bridge declarations:
  `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected`,
  `locallyConnectedSpace_iff_connected_basis`,
  `LocallyConnectedSpace.open_connected_basis`,
  `locallyConnectedSpace_of_connected_bases`
- same-domain declarations inspected:
  `LocallyConnectedSpace`,
  `locallyConnectedSpace_iff_hasBasis_isOpen_isConnected`,
  `locallyConnectedSpace_iff_connected_basis`,
  `LocallyConnectedSpace.open_connected_basis`,
  `locallyConnectedSpace_of_connected_bases`

Layer triage:
- `source-facing`: the textbook criterion that every neighborhood filter has a basis of connected
  neighborhoods
- `core/canonical`: the mathlib owner class `LocallyConnectedSpace`
- `bridge/view`: the equivalence between the owner and neighborhood-basis formulations, first with
  open connected neighborhoods, then preconnected neighborhoods, and finally connected
  neighborhoods

Primitive data belongs to the owner class `LocallyConnectedSpace`, whose field uses open connected
neighborhoods. The source-facing “connected neighborhoods” criterion is derived API, so this file
should recall the owner and keep only the thin neighborhood-basis bridge below. -/

/- Canonical recall: the mathlib owner for local connectedness is `LocallyConnectedSpace`. -/
recall LocallyConnectedSpace

/- Companion recall: mathlib’s canonical bridge theorem uses preconnected neighborhoods. -/
recall locallyConnectedSpace_iff_connected_basis

/- Companion recall: a basis of connected neighborhoods canonically rebuilds the owner. -/
recall locallyConnectedSpace_of_connected_bases

/-- Definition 5.7.10: a topological space is locally connected if every point has a fundamental
system of connected neighborhoods, equivalently if each neighborhood filter has a basis of
connected neighborhoods. -/
-- Proof sketch: forget openness from `LocallyConnectedSpace.open_connected_basis` in the forward
-- direction, and rebuild the owner from the connected neighborhood bases using
-- `locallyConnectedSpace_of_connected_bases` in the reverse direction.
theorem locallyConnectedSpace_iff_hasBasis_connected_neighborhoods :
    LocallyConnectedSpace X ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set X ↦ s ∈ 𝓝 x ∧ IsConnected s) id := by
  constructor
  · intro h x
    letI := h
    refine (LocallyConnectedSpace.open_connected_basis x).to_hasBasis
      (fun s hs ↦ ⟨s, ⟨mem_nhds_iff.mpr ⟨s, subset_rfl, hs.1, hs.2.1⟩, hs.2.2⟩, subset_rfl⟩)
      ?_
    intro s hs
    exact (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp hs.1
  · intro h
    exact locallyConnectedSpace_of_connected_bases (fun _ s ↦ s)
      (fun x s ↦ s ∈ 𝓝 x ∧ IsConnected s) h
      (fun _ _ hs ↦ hs.2.isPreconnected)
