module

public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for Stacks tag `0377`:
- primary domain: coinducing maps and the induced map on connected components
- same-domain declarations inspected:
  `Topology.isCoinducing_iff_isClosed`,
  `Topology.IsCoinducing.of_isClosed_preimage_iff_isClosed`,
  `Topology.IsCoinducing.continuous`,
  `Topology.IsCoinducing.connectedComponentsMap_bijective`

Layer triage:
- `source-facing`: the Stacks closed-set criterion on subsets of `Y`
- `core/canonical`: the owner predicate `Topology.IsCoinducing`
- `bridge/view`: the induced map on `ConnectedComponents`

Primitive data is the closed-set criterion itself. Continuity of `f` and the connected-components
map are derived API from the owner `IsCoinducing`, so this file should reuse that owner directly
rather than introduce a parallel local wrapper.
-/
/- The source closed-set criterion is the canonical bridge to `Topology.IsCoinducing`. -/
recall IsCoinducing.of_isClosed_preimage_iff_isClosed

/- Canonical library form of Stacks tag `0377`: a coinducing map with connected fibers induces a
bijection on connected components. -/
recall IsCoinducing.connectedComponentsMap_bijective

-- Proof sketch: the closed-set hypothesis is exactly the coinducing criterion, so continuity of
-- `f` is derived rather than primitive. Then apply the canonical connected-components theorem for
-- coinducing maps with connected fibers.
/-- Lemma 5.7.5: if every fiber `f ⁻¹' {y}` is connected, and a subset of `Y` is closed exactly
when its preimage is closed, then the induced map on connected components is bijective. This is
the Stacks-style closed-set bridge to the canonical recalled
`IsCoinducing.connectedComponentsMap_bijective`. -/
theorem connectedComponentsMap_bijective_of_connected_fibers_of_isClosed_iff
    (hfiber : ∀ y : Y, IsConnected (f ⁻¹' {y}))
    (hclosed : ∀ T : Set Y, IsClosed T ↔ IsClosed (f ⁻¹' T)) :
    ((IsCoinducing.of_isClosed_preimage_iff_isClosed
      (fun T ↦ (hclosed T).symm)).continuous.connectedComponentsMap).Bijective := by
  let hf : IsCoinducing f :=
    IsCoinducing.of_isClosed_preimage_iff_isClosed fun T ↦ (hclosed T).symm
  simpa [hf] using hf.connectedComponentsMap_bijective hfiber

end
