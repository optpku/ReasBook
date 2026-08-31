module

import Mathlib.Topology.GDelta.Basic
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for nowhere dense images:
- primary domain: general topology of nowhere dense subsets under inducing maps
- sampled owner-level declarations:
  `Topology.IsInducing.isNowhereDense_image`,
  `Topology.IsClosedEmbedding.isInducing`,
  `IsNowhereDense.image_val`,
  `IsHomeomorph.isClosedEmbedding`
- best owner abstraction: `Topology.IsInducing.isNowhereDense_image`
- primitive data: a map together with the owner hypothesis `IsInducing`, and a nowhere dense
  subset of the source
- derived API: closed-embedding and subtype specializations obtained by passing to inducing maps

Layer triage:
- `source-facing`: nowhere dense images under a homeomorphism onto a closed subset
- `core/canonical`: `Topology.IsInducing.isNowhereDense_image`
- `bridge/view`: `Topology.IsClosedEmbedding.isInducing`
-/

/- Lemma 5.21.5 is exactly the canonical owner theorem that nowhere dense subsets have nowhere
dense image under an inducing map. The stronger closed-embedding wording from the source is a
derived specialization, so this file recalls the owner result directly. -/
recall Topology.IsInducing.isNowhereDense_image
