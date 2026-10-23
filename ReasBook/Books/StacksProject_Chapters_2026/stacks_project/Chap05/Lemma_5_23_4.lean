module

public import Mathlib.Topology.Spectral.ConstructibleTopology
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace Topology

/- Domain-style sampling for spectral maps and constructible topologies:
- primary domain: spectral maps between spectral spaces, compared with continuity for the
  constructible topologies;
- sampled owner declarations:
  `IsSpectralMap`,
  `IsSpectralMap.continuous_constructibleTopology`,
  `WithConstructibleTopology`,
  `compactSpace_withConstructibleTopology`,
  `PrespectralSpace.isTopologicalBasis`;
- best owner abstraction: `IsSpectralMap` is the core owner for the map property, while
  constructible-topology continuity is derived bridge API from that owner.

Layer triage:
- `source-facing`: this lemma is the textbook equivalence between spectrality of a continuous map
  and continuity for the constructible topologies;
- `core/canonical`: `IsSpectralMap` and the constructible-topology owner `WithConstructibleTopology`;
- `bridge/view`: `IsSpectralMap.continuous_constructibleTopology` gives the forward direction, and
  compactness of `WithConstructibleTopology` on a spectral space recovers the compact-open
  preimage condition for the converse.

Primitive data is only the owner predicate `IsSpectralMap f` together with the ambient spectral
space structures. Constructible continuity, clopen patch subsets, and compactness transport back to
the original topology are derived API and should not be duplicated by a parallel local owner.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

-- Proof sketch: for a spectral map, quasi-compact opens pull back to quasi-compact opens, hence
-- constructible subsets pull back to constructible subsets and `f` is continuous for the generated
-- constructible topologies. Conversely, if `f` is constructibly continuous, then the preimage of a
-- quasi-compact open is clopen in the constructible topology on `X`, hence compact there; the
-- identity map to the original topology is continuous and surjective, so that preimage is compact
-- in the original topology, giving `IsSpectralMap f`.
/-- Lemma 5.23.4: for spectral spaces, a continuous map is spectral if and only if it is
continuous for the constructible topologies on source and target. -/
theorem isSpectralMap_iff_continuous_constructibleTopology (hfcont : Continuous f) :
    IsSpectralMap f ↔
      Continuous[constructibleTopology X, constructibleTopology Y] f := by
  constructor
  · exact IsSpectralMap.continuous_constructibleTopology
  · intro hpatch
    refine ⟨hfcont, fun s hsOpen hsCompact ↦ ?_⟩
    have hPatchCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
    have hsClosedPatch : IsClosed[constructibleTopology Y] s :=
      (isClopen_constructibleTopology_of_isConstructible (hsCompact.isConstructible hsOpen)).1
    have hpreClosed := by
      letI : TopologicalSpace X := constructibleTopology X
      letI : TopologicalSpace Y := constructibleTopology Y
      exact hsClosedPatch.preimage hpatch
    have hpreCompactPatch := by
      letI : TopologicalSpace X := constructibleTopology X
      letI : CompactSpace X := by
        simpa [WithConstructibleTopology] using hPatchCompact
      exact hpreClosed.isCompact
    have hOriginalOpen : ∀ ⦃U : Set X⦄, IsOpen U → IsOpen[constructibleTopology X] U := by
      intro U hU
      refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hU
      · intro V hV
        exact hV.2.isOpen_constructibleTopology_of_isOpen hV.1
      · intro S hS
        let _ : TopologicalSpace X := constructibleTopology X
        exact isOpen_sUnion fun V hV ↦ hS V hV
    have hContToOriginal := continuous_id_of_le hOriginalOpen
    simpa using
      @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X› (f ⁻¹' s) id
        hpreCompactPatch hContToOriginal

end
