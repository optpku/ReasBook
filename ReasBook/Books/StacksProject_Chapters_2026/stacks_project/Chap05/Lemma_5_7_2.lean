module

public import Mathlib.Topology.Connected.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for connectedness under continuous images:
- primary domain: connected subsets of topological spaces
- sampled same-domain declarations:
  `ConnectedSpace`,
  `connectedComponent`,
  `IsConnected.image`,
  `IsConnected.closure`
- best owner abstraction for this item: `IsConnected.image`
- primitive data: a connected subset `s` and a map continuous on `s`
- derived API: the textbook specialization where the map is globally continuous

Layer triage:
- `source-facing`: the image of a connected subset under a continuous map is connected
- `core/canonical`: `IsConnected.image`
- `bridge/view`: `Continuous f` specialized to `hf.continuousOn`

This item is not a second owner theorem; it is the source-facing global-continuity bridge to the
canonical theorem `IsConnected.image`.
-/

/-- Lemma 5.7.2: the image of a connected subset under a continuous map is connected.

This is the textbook global-continuity specialization of the canonical theorem
`IsConnected.image`. -/
theorem isConnected_image {s : Set X} (hs : IsConnected s) {f : X → Y} (hf : Continuous f) :
    IsConnected (f '' s) :=
  hs.image f hf.continuousOn

end
