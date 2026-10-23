module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for compact-to-Hausdorff homeomorphism criteria:
- owner abstraction: `isHomeomorph_iff_continuous_bijective`
- same-domain declarations inspected:
  `isHomeomorph_iff_isEmbedding_surjective`,
  `isHomeomorph_iff_continuous_isClosedMap_bijective`,
  `isHomeomorph_iff_continuous_bijective`,
  `Lemma_5_26_4.isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed`

Layer triage:
- `source-facing`: the Stacks criterion that a continuous bijection from a quasi-compact space to a
  Hausdorff space is a homeomorphism
- `core/canonical`: mathlib's owner theorem `isHomeomorph_iff_continuous_bijective`
- `bridge/view`: downstream arguments that supply bijectivity or closed-map data and then invoke
  the owner theorem

Primitive data is exactly continuity and bijectivity, with compactness of the source and
Hausdorffness of the target carried canonically by `[CompactSpace X]` and `[T2Space Y]`. The
closed-map package is derived by the owner theorem, so this file should keep the source-facing
forward implication as its public item and use the stronger canonical `↔` theorem only as
justification or companion recall.
-/

/-- Helper for Lemma 5.17.8: a continuous map from a compact space to a Hausdorff space is a
closed map. -/
lemma continuous_isClosedMap_of_compact_t2 [CompactSpace X] [T2Space Y] (hf : Continuous f) :
    IsClosedMap f := by
  intro s hs
  -- Closed subsets of a compact space remain compact.
  have hs_compact : IsCompact s := hs.isCompact
  -- Continuous images of compact sets are compact.
  have himage_compact : IsCompact (f '' s) := hs_compact.image hf
  -- Compact subsets of a Hausdorff space are closed.
  exact himage_compact.isClosed

/-- Lemma 5.17.8: if `f : X → Y` is continuous and bijective, `X` is quasi-compact, and `Y` is
Hausdorff, then `f` is a homeomorphism. -/
theorem isHomeomorph_of_continuous_bijective [CompactSpace X] [T2Space Y]
    (hf : Continuous f) (hbij : Function.Bijective f) :
    IsHomeomorph f := by
  -- Follow the source proof: first show that `f` is a closed map.
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  -- The canonical criterion now reduces the claim to continuity, closedness, and bijectivity.
  exact ⟨hf, continuous_isClosedMap_of_compact_t2 (f := f) hf, hbij⟩

/- Companion recall: the stronger canonical compact-to-Hausdorff criterion packages this lemma as
an `iff`, with the reverse implication supplied by every homeomorphism. -/
recall isHomeomorph_iff_continuous_bijective

end
