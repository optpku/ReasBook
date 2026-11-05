module

import Mathlib.Topology.Spectral.Hom
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for quasi-compact maps in topological spaces:
- owner declarations: `IsSpectralMap`, `IsSpectralMap.comp`, `IsRetrocompact`
- chapter owner recall: `Definition_5_12_1` identifies the Stacks quasi-compact-map notion with
  `IsSpectralMap`

Layer triage:
- `source-facing`: quasi-compact maps are stable under composition
- `core/canonical`: `IsSpectralMap`
- `bridge/view`: none needed here, since mathlib already provides the exact composed-map theorem

Primitive data is only the owner predicate `IsSpectralMap`; closure under composition is derived
API from the canonical theorem `IsSpectralMap.comp`, so this file should not introduce a parallel
local wrapper.
-/

/- Lemma 5.12.2: a composition of quasi-compact maps is quasi-compact. Via
Definition 5.12.1, the Stacks quasi-compact-map notion is the canonical mathlib predicate
`IsSpectralMap`, and this is exactly `IsSpectralMap.comp`. -/
recall IsSpectralMap.comp
