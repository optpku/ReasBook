module

public import Mathlib.Topology.Constructible

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for constructibility on finite retrocompact open covers:
- primary domain: constructible subsets and their locality on open covers;
- sampled canonical declarations:
  `Topology.IsConstructible.preimage_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsLocallyConstructible.iff_of_isOpenCover`,
  `TopologicalSpace.IsOpenCover.iUnion_inter`.
- best owner abstraction: `Topology.IsConstructible` is the owner predicate; the finite-cover
  reconstruction and the subtype image/preimage identification are derived API.
- primitive-vs-derived split:
  primitive data: the indexed open cover, retrocompactness of each cover member, and the
    constructible traces on those members;
  derived API: the ambient constructible pieces
    `Subtype.val '' ((V i : Set X) ↓∩ E) = (V i : Set X) ∩ E`
    and the cover identity `⋃ i, ((V i : Set X) ∩ E) = E`.

Layer triage:
- `source-facing`: Lemma 5.15.6 itself, asserting locality of constructibility on a finite
  retrocompact open cover;
- `core/canonical`: `Topology.IsConstructible`;
- `bridge/view`: the subtype inclusions `Subtype.val : V i → X` together with
  `IsOpenCover.iUnion_inter`.
-/

-- Proof sketch: use the canonical constructible-set API for open embeddings. For the forward
-- implication, pull back along each `Subtype.val : V i → X`. For the reverse implication, push
-- each constructible trace forward along the same open embedding, then reconstruct `E` as the
-- finite union of these traces over the cover.
/-- Lemma 5.15.6: a subset `E ⊆ X` is constructible if and only if its trace on each member of a
finite retrocompact open cover is constructible in that open subspace. -/
theorem isConstructible_iff_forall_preimage_subtypeVal_of_finite_retrocompact_openCover
    {ι : Type v} [Finite ι] (V : ι → Opens X) (hV : IsOpenCover V)
    (hretro : ∀ i, IsRetrocompact (V i : Set X)) {E : Set X} :
    IsConstructible E ↔ ∀ i, IsConstructible ((V i : Set X) ↓∩ E) := by
  constructor
  · intro hE i
    -- Pull back the ambient constructible set along the open-subspace inclusion.
    simpa using hE.preimage_of_isOpenEmbedding (V i).2.isOpenEmbedding_subtypeVal
  · intro hE
    -- Reassemble `E` from its traces on the cover and prove each trace constructible in `X`.
    rw [← hV.iUnion_inter E]
    exact IsConstructible.iUnion fun i ↦ by
      -- Push the constructible trace forward along the retrocompact open embedding.
      simpa [image_preimage_eq_range_inter, inter_comm] using
        (hE i).image_of_isOpenEmbedding (V i).2.isOpenEmbedding_subtypeVal
        (by simpa using hretro i)
