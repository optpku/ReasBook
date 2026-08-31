module

public import Mathlib.Topology.Constructible
import stacks_project.Chap05.Lemma_5_15_10
import stacks_project.Chap05.Lemma_5_15_8

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {T E : Set X}

/- Domain-style sampling for constructible pullbacks along subtype inclusions in prespectral spaces:
- primary domain: constructible subsets and their restriction to constructible subspaces;
- sampled declarations:
  `Topology.IsConstructible.preimage`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`,
  `Topology.IsConstructible.isRetrocompact`,
  `PrespectralSpace.isTopologicalBasis`;
- best owner abstraction: the chapter owner for subtype pullback is
  `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`; the ambient prespectral
  structure and the retrocompactness of the subspace are supporting data for that owner;
- primitive-vs-derived split: the primitive data are the ambient constructible subset being
  pulled back and the retrocompact subspace. `PrespectralSpace X` is canonical ambient structure,
  and `Topology.IsConstructible.isRetrocompact` derives the owner input from the source-facing
  constructibility hypothesis on the subspace.

Layer triage:
- `source-facing`: Lemma 5.15.11, the constructible-subspace specialization of the trace theorem;
- `core/canonical`: `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`;
- `bridge/view`: this file's derivation of the owner input from
  `Topology.IsConstructible.isRetrocompact`.
-/

-- Proof sketch: derive that the constructible subspace `T` is retrocompact by
-- `Topology.IsConstructible.isRetrocompact`, then feed that derived input into the canonical
-- subtype-pullback owner `Topology.IsConstructible.preimage_subtypeVal_of_isRetrocompact`.
/-- Lemma 5.15.11: if compact open subsets form a topological basis of `X` and `T, E ⊆ X` are
constructible, then the intersection `T ∩ E`, viewed as a subset of the subspace `T`, is
constructible in `T`. The ambient basis hypothesis is expressed canonically as
`[PrespectralSpace X]`. -/
theorem IsConstructible.preimage_subtypeVal_of_isConstructible
    (hE : IsConstructible E) (hT : IsConstructible T) :
    IsConstructible (T ↓∩ E) :=
  hE.preimage_subtypeVal_of_isRetrocompact hT.isRetrocompact

end

end Topology
