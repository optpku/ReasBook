module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
public import Mathlib.Data.Finset.Defs
public import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Compactness.Compact

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

/- Domain-style sampling for quasi-compactness in topological spaces:
- primary domain: compactness/spectrality for spaces, maps, and subsets
- same-domain declarations inspected:
  `CompactSpace`,
  `isCompact_iff_finite_subcover`,
  `IsSpectralMap`,
  `IsRetrocompact_iff_isSpectralMap_subtypeVal`
- best owner abstractions: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`

Layer triage:
- `source-facing`: the whole-space finite-subcover characterization
- `core/canonical`: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- `bridge/view`: the whole-space specialization of `isCompact_iff_finite_subcover`

Primitive data belongs to the owner abstractions above. This file should not keep parallel local
wrappers when the source item is only recalling those canonical notions.
-/

section

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.12.1 (space): the Stacks notion of a quasi-compact topological space is the
canonical typeclass `CompactSpace`. -/
recall CompactSpace

/-- Definition 5.12.1 (space): a topological space is quasi-compact if and only if every open cover
admits a finite subcover. -/
theorem quasiCompactSpace_iff_finite_subcover :
    CompactSpace X ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → univ ⊆ ⋃ i, U i → ∃ s : Finset ι, univ ⊆ ⋃ i ∈ s, U i := by
  rw [← isCompact_univ_iff, isCompact_iff_finite_subcover]

end

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Definition 5.12.1 (map): the Stacks notion of a quasi-compact map is the canonical predicate
`IsSpectralMap`. -/
recall IsSpectralMap

/- Source-facing unpacking: `IsSpectralMap f` is by definition the conjunction of continuity of
`f` and compactness of preimages of compact open subsets. No parallel wrapper theorem is needed,
since this item is only recalling the canonical owner predicate. -/

end

section

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.12.1 (subset): the Stacks notion of a retrocompact subset is the canonical
predicate `IsRetrocompact`. -/
recall IsRetrocompact

/- Companion recall: retrocompactness of a subset is equivalent to the subtype inclusion being a
spectral map. -/
recall IsRetrocompact_iff_isSpectralMap_subtypeVal

end
