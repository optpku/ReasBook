module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Constructible

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology TopologicalSpace

universe u v

/- Domain-style sampling for quasi-compact images in topological spaces:
- owner declarations: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- canonical range compactness: `isCompact_range`
- canonical subset bridge: `IsRetrocompact_iff_isSpectralMap_subtypeVal`

Layer triage:
- `source-facing`: Lemma 5.12.7 identifies compactness and retrocompactness consequences for the
  image of a quasi-compact map
- `core/canonical`: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- `bridge/view`: the range inclusion `Set.range f → Y`

Primitive data is the owner predicate `IsSpectralMap f`; retrocompactness of `range f` is derived
through the canonical subtype-inclusion bridge.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Canonical recall: if `X` is quasi-compact, then the image `f(X)` is quasi-compact. This is
exactly the canonical theorem `isCompact_range`. -/
recall isCompact_range

-- Proof sketch: apply `IsRetrocompact_iff_isSpectralMap_subtypeVal` to the subtype inclusion of
-- `range f` and use `hf` to show compactness of preimages of compact open subsets.
/-- Lemma 5.12.7: if `f` is quasi-compact, then the image `f(X)` is retrocompact. -/
theorem IsSpectralMap.isRetrocompact_range (hf : IsSpectralMap f) :
    IsRetrocompact (range f) := by
  -- Rewrite retrocompactness of the image as spectrality of its subtype inclusion.
  rw [IsRetrocompact_iff_isSpectralMap_subtypeVal]
  refine ⟨continuous_subtype_val, ?_⟩
  intro t htOpen htCompact
  -- Move compactness on the subtype back to `Y`, where the source identity is visible.
  rw [IsEmbedding.subtypeVal.isCompact_iff, Set.image_preimage_eq_inter_range,
    Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.inter_comm]
  -- The source proof now applies verbatim: compactness of `f ⁻¹' t` maps to compactness of
  -- `f '' (f ⁻¹' t) = t ∩ range f`.
  have hImage : IsCompact (f '' (f ⁻¹' t)) :=
    (hf.isCompact_preimage_of_isOpen htOpen htCompact).image hf.continuous
  simpa [Set.image_preimage_eq_inter_range, Set.inter_comm] using hImage

end
