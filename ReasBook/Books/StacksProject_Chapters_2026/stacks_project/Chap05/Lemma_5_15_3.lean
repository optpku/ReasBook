module

import Mathlib.Topology.Constructible
import Mathlib.Tactic.Recall
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Domain-style sampling for constructible preimages in topological spaces:
- primary domain: constructible subsets, retrocompact opens, and pullback stability in topology;
- sampled canonical declarations:
  `IsConstructible.preimage`,
  `IsConstructible.preimage_of_isOpenEmbedding`,
  `IsConstructible.preimage_of_isClosedEmbedding`,
  `IsSpectralMap.isConstructible_preimage`;
- best owner abstraction: the owner of the general pullback-stability statement is the mathlib
  theorem `IsConstructible.preimage`; the open-embedding, closed-embedding, and spectral-map forms
  are derived specializations;
- primitive-vs-derived split: the primitive data are continuity of `f` together with the
  retrocompact-open preimage hypothesis. The constructible-preimage conclusion and its stronger
  special cases are derived API from that owner theorem.

Layer triage:
- `source-facing`: the Stacks lemma on pullbacks of constructible subsets under maps preserving
  retrocompact opens;
- `core/canonical`: `IsConstructible.preimage`;
- `bridge/view`: the open-embedding, closed-embedding, and spectral-map specializations.
-/

/- Lemma 5.15.3: if `f : X → Y` is continuous and inverse images of retrocompact open subsets are
retrocompact, then inverse images of constructible subsets are constructible. This is exactly the
canonical theorem `Topology.IsConstructible.preimage`. -/
recall IsConstructible.preimage
