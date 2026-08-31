module

import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 5.26.2:
- primary domain: Gleason's Zorn-subset-condition lemmas in general topology
- sampled owner declarations:
  `ExtremallyDisconnected`,
  `CompactT2.Projective.extremallyDisconnected`,
  `exists_compact_surjective_zorn_subset`,
  `image_subset_closure_compl_image_compl_of_isOpen`
- best owner abstraction for this item: the theorem
  `image_subset_closure_compl_image_compl_of_isOpen` itself
- primitive data: a continuous surjection `ρ` and the Zorn-subset condition on proper closed
  subsets of the source
- derived API: the closure containment `ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ)` for open `G`

Layer triage:
- `source-facing`: the closure statement under the Zorn-subset condition
- `core/canonical`: `image_subset_closure_compl_image_compl_of_isOpen`
- `bridge/view`: downstream uses of this theorem inside the extremally disconnected/projective
  compact Hausdorff development

This item is already owned canonically by mathlib, so the refined file should recall that theorem
directly rather than keep any parallel local alias or wrapper.
-/

/- Lemma 5.26.2: if `ρ` is a continuous surjection satisfying the Zorn-subset condition, then
for any open `G`, the image `ρ '' G` is contained in the closure of the complement of
`ρ '' Gᶜ`. This is exactly the canonical mathlib theorem
`image_subset_closure_compl_image_compl_of_isOpen`. -/
recall image_subset_closure_compl_image_compl_of_isOpen
