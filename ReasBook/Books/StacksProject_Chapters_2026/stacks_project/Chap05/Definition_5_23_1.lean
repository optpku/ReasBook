module

import Mathlib.Topology.Spectral.Basic
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for spectral topological spaces:
- owner declarations: `SpectralSpace`, `PrespectralSpace`, `QuasiSeparatedSpace`, `IsSpectralMap`
- canonical owner abstraction: `SpectralSpace`
- supporting owner fields: `T0Space`, `CompactSpace`, `QuasiSober`, `QuasiSeparatedSpace`,
  `PrespectralSpace`

Layer triage:
- `source-facing`: Definition 5.23.1 recalls the textbook notion of a spectral space
- `core/canonical`: `SpectralSpace`
- `bridge/view`: direct reuse of the inherited canonical field-level API from `SpectralSpace`

Primitive data belongs to the canonical owner class `SpectralSpace`; the inherited field-level
typeclass API is already available directly, so this item should remain a pure canonical recall.
-/

/- Definition 5.23.1: the Stacks notion of a spectral topological space is the canonical
mathlib typeclass `SpectralSpace`. -/
recall SpectralSpace

/- Companion recall: spectral maps are already owned by the canonical predicate `IsSpectralMap`,
so this item reuses that owner directly rather than introducing a local wrapper. -/
recall IsSpectralMap
