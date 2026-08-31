module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology
import stacks_project.Chap05.Lemma_5_23_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology

/- Domain-style sampling for spectral maps and constructible topologies:
- primary domain: spectral maps of spectral spaces, viewed through constructible subsets and the
  constructible topology;
- sampled canonical declarations:
  `IsSpectralMap`,
  `Topology.IsConstructible.preimage`,
  `constructibleTopology`,
  `constructibleTopology_t2_totallyDisconnected_and_compact_of_spectralSpace`;
- best owner abstractions: `IsSpectralMap` for the map data and
  `Topology.IsConstructible.preimage` for the pullback-stability statement; compactness and
  Hausdorffness of the constructible topology are derived from the owner `WithConstructibleTopology`
  package already established in `Lemma_5_23_2`.

Layer triage:
- `source-facing`: Lemma 5.23.3, giving the constructible-topology continuity, quasi-compact
  fibers, and constructible-closed image of a spectral map;
- `core/canonical`: `IsSpectralMap`, `Topology.IsConstructible.preimage`, and
  `WithConstructibleTopology`;
- `bridge/view`: the constructible-preimage specialization and the continuity statement for
  `constructibleTopology`.

Primitive data is only the spectral-map owner together with the earlier compact Hausdorff package
for the constructible topology on a spectral space. Constructible preimages, compact fibers, and
constructible-closed range are derived API and should be obtained from those owners rather than by
parallel local wrappers.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

-- Proof sketch: a spectral map pulls back each subbasic open of the constructible topology to a
-- subbasic open of the constructible topology. For compact opens this is the defining spectral-map
-- compactness condition, and for closed compact-complement subsets it follows by taking
-- complements.
/-- Lemma 5.23.3 (1): a spectral map of spectral spaces is continuous for the constructible
topologies. -/
theorem IsSpectralMap.continuous_constructibleTopology (hf : IsSpectralMap f) :
    Continuous[constructibleTopology X, constructibleTopology Y] f := by
  rw [constructibleTopology, continuous_generateFrom_iff]
  intro s hs
  rcases hs with (⟨hsOpen, hsCompact⟩ | ⟨hsClosed, hsCompactCompl⟩)
  · exact (hf.isCompact_preimage_of_isOpen hsOpen hsCompact).isOpen_constructibleTopology_of_isOpen
      (hsOpen.preimage hf.continuous)
  · exact
      (show IsCompact ((f ⁻¹' s)ᶜ) from by
        simpa [Set.preimage_compl] using
          hf.isCompact_preimage_of_isOpen hsClosed.isOpen_compl hsCompactCompl).isOpen_constructibleTopology_of_isClosed
        (hsClosed.preimage hf.continuous)

end

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

-- Proof sketch: the general owner theorem
-- `Topology.IsConstructible.preimage` therefore gives constructible preimages, which are open in
-- the constructible topology by Lemma 5.23.2.
/-- Companion bridge for Lemma 5.23.3 (1): equivalently, a spectral map pulls back constructible
subsets to constructible subsets. -/
theorem IsSpectralMap.isConstructible_preimage (hf : IsSpectralMap f) {s : Set Y}
    (hs : IsConstructible s) : IsConstructible (f ⁻¹' s) :=
  hs.preimage hf.continuous fun _ hUopen hUretro ↦
    (hf.isCompact_preimage_of_isOpen hUopen hUretro.isCompact).isRetrocompact
      (hUopen.preimage hf.continuous)

-- Proof sketch: in the constructible topology on `Y`, the singleton `{y}` is closed because that
-- topology is Hausdorff by Lemma 5.23.2. Its preimage is then closed in the compact
-- constructible topology on `X`, hence compact there, and the identity map from the constructible
-- topology to the original topology is continuous.
/-- Lemma 5.23.3 (2): every fiber of a spectral map of spectral spaces is quasi-compact. -/
theorem IsSpectralMap.isCompact_fiber (hf : IsSpectralMap f) (y : Y) :
    IsCompact (f ⁻¹' ({y} : Set Y)) := by
  -- Pass from the original topology to the constructible one by expanding opens along the
  -- compact-open basis of the spectral topology.
  have hOriginalOpen : ∀ ⦃U : Set X⦄, IsOpen U → IsOpen[constructibleTopology X] U := by
    intro U hU
    refine PrespectralSpace.isTopologicalBasis.isOpen_induction ?_ ?_ hU
    · intro V hV
      exact hV.2.isOpen_constructibleTopology_of_isOpen hV.1
    · intro S hS
      let _ : TopologicalSpace X := constructibleTopology X
      exact isOpen_sUnion fun V hV ↦ hS V hV
  -- This is the textbook map `X' → X`, used to transport compactness of the patch fiber back to
  -- the original topology.
  have hContToOriginal : @Continuous X X (constructibleTopology X) ‹TopologicalSpace X› id :=
    continuous_id_of_le hOriginalOpen
  have hPatchContinuous : Continuous[constructibleTopology X, constructibleTopology Y] f :=
    hf.continuous_constructibleTopology
  have hPatchT2Y : @T2Space Y (constructibleTopology Y) :=
    constructibleTopology_t2Space_of_spectralSpace
  have hPatchCompactX : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  -- In the constructible topology on `Y`, singleton fibers are closed because the patch topology
  -- is Hausdorff, so their preimages in the compact patch space `X'` are compact.
  have hFiberCompactPatch : @IsCompact X (constructibleTopology X) (f ⁻¹' ({y} : Set Y)) := by
    letI : TopologicalSpace X := constructibleTopology X
    letI : TopologicalSpace Y := constructibleTopology Y
    letI : T2Space Y := hPatchT2Y
    letI : CompactSpace X := hPatchCompactX
    have hFiberClosedPatch : IsClosed (f ⁻¹' ({y} : Set Y)) := by
      exact isClosed_singleton.preimage hPatchContinuous
    exact hFiberClosedPatch.isCompact
  -- The identity map on the underlying set sends the compact patch fiber onto the original fiber.
  simpa using
    @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X›
      (f ⁻¹' ({y} : Set Y)) id hFiberCompactPatch hContToOriginal

-- Proof sketch: by part `(1)`, the map is continuous for the constructible topologies. Since a
-- spectral space is compact in the constructible topology and that topology on `Y` is Hausdorff by
-- Lemma 5.23.2, the image is compact and therefore closed.
/-- Lemma 5.23.3 (3): the image of a spectral map of spectral spaces is closed for the
constructible topology. -/
theorem IsSpectralMap.isClosed_range_constructibleTopology (hf : IsSpectralMap f) :
    IsClosed[constructibleTopology Y] (range f) := by
  have hPatchContinuous : Continuous[constructibleTopology X, constructibleTopology Y] f :=
    hf.continuous_constructibleTopology
  have hPatchCompactX : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  have hPatchT2Y : @T2Space Y (constructibleTopology Y) :=
    constructibleTopology_t2Space_of_spectralSpace
  -- The constructible topology makes the source compact, so the constructible-topology image is
  -- compact by continuity from part `(1)`.
  have hRangeCompact : @IsCompact Y (constructibleTopology Y) (range f) := by
    letI : TopologicalSpace X := constructibleTopology X
    letI : TopologicalSpace Y := constructibleTopology Y
    letI : CompactSpace X := hPatchCompactX
    simpa using isCompact_range hPatchContinuous
  -- The constructible topology on a spectral space is Hausdorff, so compact subsets are closed.
  letI : TopologicalSpace Y := constructibleTopology Y
  letI : T2Space Y := hPatchT2Y
  exact hRangeCompact.isClosed

end
