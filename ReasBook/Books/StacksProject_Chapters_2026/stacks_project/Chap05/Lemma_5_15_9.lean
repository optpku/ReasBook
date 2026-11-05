module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace Topology

/- Domain-style sampling for constructible images along closed-subspace inclusions:
- primary domain: constructible subsets and their stability under maps preserving the
  retrocompact-open generators used by `Topology.IsConstructible`;
- sampled canonical declarations:
  `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_of_isClosedEmbedding`,
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isClosedEmbedding`;
- best owner abstraction: `Topology.IsConstructible.image_of_isClosedEmbedding`.

Primitive-vs-derived split:
- primitive data: a closed embedding together with retrocompact complement of its range;
- derived API: the closed-subspace specialization obtained from `Subtype.val : Z → X`.

Layer triage:
- `source-facing`: a constructible subset of a closed subspace has constructible image in the
  ambient space under the Stacks closed-subspace hypotheses;
- `core/canonical`: `Topology.IsConstructible.image_of_isClosedEmbedding`;
- `bridge/view`: the subtype inclusion `Subtype.val : Z → X`, whose owner hypotheses are supplied
  canonically by `IsClosed Z` and `IsRetrocompact Zᶜ`.

This file should therefore recall the owner theorem rather than keep a parallel local wrapper.
-/

/- Lemma 5.15.9: if `Z ⊆ X` is closed and `Zᶜ` is retrocompact open in `X`, then a constructible
subset of the closed subspace `Z` has constructible image in `X`. This is the closed-subspace
specialization of the canonical theorem
`Topology.IsConstructible.image_of_isClosedEmbedding`. -/
recall IsConstructible.image_of_isClosedEmbedding

end Topology
