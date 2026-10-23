module

public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for connected components under open quotient maps:
- primary domain: connected components of topological spaces under open/coinducing maps
- earlier chapter owner abstraction: `IsOpenQuotientMap`
- same-domain declarations inspected:
  `IsOpenQuotientMap`,
  `IsOpenQuotientMap.isQuotientMap`,
  `connectedComponentsMap_bijective_of_connected_fibers_of_isClosed_iff`,
  `Topology.IsCoinducing.connectedComponentsMap_bijective`

Layer triage:
- `source-facing`: the Stacks open-map criterion with connected fibers
- `core/canonical`: `IsOpenQuotientMap`, whose quotient-map/coinducing consequences are derived
- `bridge/view`: the induced map `Continuous.connectedComponentsMap` on connected components

Primitive data is just continuity, openness, and the connected-fibre hypothesis. Surjectivity and
the quotient/coinducing package are derived from the owner abstraction, so this file should expose
the owner-level open-quotient theorem and keep the source wording as a thin wrapper.
-/

/- Canonical library form used below: a coinducing map with connected fibers induces a bijection
on connected components. -/
recall Topology.IsCoinducing.connectedComponentsMap_bijective

namespace IsOpenQuotientMap

/-- Canonical open-quotient form of Lemma 5.7.6: an open quotient map with connected fibres
induces a bijection on connected components. -/
theorem connectedComponentsMap_bijective (hf : IsOpenQuotientMap f)
    (hfibers : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    Function.Bijective hf.continuous.connectedComponentsMap := by
  let hcoind := hf.isQuotientMap.isCoinducing
  simpa using hcoind.connectedComponentsMap_bijective hfibers

end IsOpenQuotientMap

-- Proof sketch: connected fibers force surjectivity, so `f` packages as an `IsOpenQuotientMap`;
-- the source wording is then just the owner-level theorem above.
/-- Lemma 5.7.6: an open continuous map with connected fibres induces a bijection on connected
components. This is the source-wording bridge to the owner theorem
`IsOpenQuotientMap.connectedComponentsMap_bijective`. -/
theorem connectedComponents_bijective_of_isOpenMap_of_connectedFibers
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    hcont.connectedComponentsMap.Bijective := by
  let hf : IsOpenQuotientMap f := ⟨fun y ↦ (hfibers y).nonempty, hcont, hopen⟩
  exact hf.connectedComponentsMap_bijective hfibers

end
