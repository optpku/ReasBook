module

public import Mathlib.Topology.Constructible
import stacks_project.Chap05.Lemma_5_12_13

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology

namespace Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [NoetherianSpace X] {f : X → Y}

/- Domain-style sampling for constructible pullbacks in Noetherian spaces:
- primary domain: constructible subsets, retrocompact opens, and pullback stability in topology;
- sampled owner/domain declarations:
  `IsConstructible.preimage`,
  `IsConstructible.preimage_of_isOpenEmbedding`,
  `IsConstructible.preimage_of_isClosedEmbedding`,
  `isRetrocompact_of_noetherianSpace`;
- best owner abstraction: `Topology.IsConstructible.preimage`;
- primitive-vs-derived split: the primitive data are the constructible subset `E`, the continuity
  of `f`, and the source-side `NoetherianSpace` instance. The retrocompact-open preimage condition
  required by the owner theorem is derived from `isRetrocompact_of_noetherianSpace`, so it should
  not remain separate public data here.

Layer triage:
- `source-facing`: Stacks Lemma 5.16.2, the Noetherian-source specialization of constructible
  pullback stability;
- `core/canonical`: `Topology.IsConstructible.preimage`;
- `bridge/view`: this file's specialization obtained by deriving the retrocompact-open pullback
  hypothesis from `NoetherianSpace X`.
-/

-- Proof sketch: apply the owner theorem `Topology.IsConstructible.preimage`. In a Noetherian
-- source space every subset is retrocompact, so the required retrocompactness of the preimage of
-- an open retrocompact subset of `Y` is automatic.
/-- Lemma 5.16.2: for a continuous map with Noetherian source, the preimage of a constructible set
is constructible. -/
theorem IsConstructible.preimage_of_continuous_of_noetherianSpace
    {E : Set Y} (hE : IsConstructible E) (hf : Continuous f) :
    IsConstructible (f ⁻¹' E) :=
  hE.preimage hf fun _ _ _ ↦ isRetrocompact_of_noetherianSpace _

end

end Topology
