module

public import Mathlib.Topology.Spectral.Basic
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3
import stacks_project.Chap05.Lemma_5_23_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology

/- Domain-style sampling for bijective spectral maps of spectral spaces:
- primary domain: spectral spaces, constructible topology, and specialization/generalization
  lifting along spectral maps
- sampled owner declarations:
  `IsSpectralMap.continuous_constructibleTopology`,
  `constructibleTopology_t2Space_of_spectralSpace`,
  `constructibleTopology_compactSpace_of_spectralSpace`,
  `SpecializingMap.stableUnderSpecialization_image`,
  `GeneralizingMap.stableUnderGeneralization_image`
- best owner abstraction: `IsSpectralMap` is the primitive map owner, while the canonical bridge
  to homeomorphisms runs through the constructible topologies, where spectral spaces become compact
  Hausdorff and a bijective spectral map becomes a homeomorphism

Layer triage:
- `source-facing`: Lemma 5.23.11, giving a homeomorphism criterion for a bijective spectral map
  under a lifting hypothesis
- `core/canonical`: `IsSpectralMap`, `SpecializingMap`, `GeneralizingMap`, and `IsHomeomorph`
- `bridge/view`: the constructible-topology homeomorphism and the patch-open/patch-closed
  criteria from Lemma `5.23.6`

Primitive data is only the spectral-map owner, bijectivity, and one lifting predicate. The
constructible-topology homeomorphism, image stability of specialization/generalization-stable
subsets, and the resulting open-map argument are all derived API and should not be repackaged as a
parallel public wrapper.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [SpectralSpace X] [SpectralSpace Y] {f : X → Y}

/-- Helper for Lemma 5.23.11: a bijective spectral map is a homeomorphism for the
constructible topologies on spectral spaces. -/
private theorem isHomeomorph_constructibleTopology (hf : IsSpectralMap f)
    (hf_bijective : Function.Bijective f) :
    @IsHomeomorph X Y (constructibleTopology X) (constructibleTopology Y) f := by
  -- In the constructible topology, spectral spaces are compact and Hausdorff.
  let hXCompact : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  let hYT2 : @T2Space Y (constructibleTopology Y) :=
    constructibleTopology_t2Space_of_spectralSpace
  -- A continuous bijection from compact to Hausdorff is a homeomorphism.
  exact
    (@isHomeomorph_iff_continuous_bijective X Y (constructibleTopology X) (constructibleTopology Y)
      f hXCompact hYT2).2 ⟨hf.continuous_constructibleTopology, hf_bijective⟩

/-- Helper for Lemma 5.23.11: lifted generalizations make a bijective spectral map open. -/
private theorem isOpenMap_of_isSpectralMap_bijective_of_generalizingMap
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f) (hgen : GeneralizingMap f) :
    IsOpenMap f := by
  let hpatch := isHomeomorph_constructibleTopology hf hf_bijective
  -- It suffices to check openness on the quasi-compact open basis of a spectral space.
  refine (PrespectralSpace.isTopologicalBasis.isOpenMap_iff).2 ?_
  intro U hU
  -- A basis open is patch-open, and its image is patch-open under the constructible homeomorphism.
  have hU_patch_open : IsOpen[constructibleTopology X] U :=
    hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  have hpatch_openMap : @IsOpenMap X Y (constructibleTopology X) (constructibleTopology Y) f :=
    @IsHomeomorph.isOpenMap X Y (constructibleTopology X) (constructibleTopology Y) f hpatch
  have hImage_patch_open : IsOpen[constructibleTopology Y] (f '' U) :=
    hpatch_openMap _ hU_patch_open
  -- Generalization stability upgrades a patch-open subset of a spectral space to an open subset.
  have hImage_gen : StableUnderGeneralization (f '' U) :=
    hgen.stableUnderGeneralization_image hU.1.stableUnderGeneralization
  exact isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
    hImage_patch_open hImage_gen

/-- Helper for Lemma 5.23.11: lifted specializations make a bijective spectral map open. -/
private theorem isOpenMap_of_isSpectralMap_bijective_of_specializingMap
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f) (hspec : SpecializingMap f) :
    IsOpenMap f := by
  let hpatch := isHomeomorph_constructibleTopology hf hf_bijective
  -- Again, it is enough to test openness on the quasi-compact open basis.
  refine (PrespectralSpace.isTopologicalBasis.isOpenMap_iff).2 ?_
  intro U hU
  -- Pass to complements so that the patch homeomorphism gives a closed image.
  have hU_patch_open : IsOpen[constructibleTopology X] U :=
    hU.2.isOpen_constructibleTopology_of_isOpen hU.1
  have hUcompl_patch_closed : @IsClosed X (constructibleTopology X) Uᶜ :=
    @IsOpen.isClosed_compl X (constructibleTopology X) U hU_patch_open
  have hpatch_closedMap : @IsClosedMap X Y (constructibleTopology X) (constructibleTopology Y) f :=
    @IsHomeomorph.isClosedMap X Y (constructibleTopology X) (constructibleTopology Y) f hpatch
  have hCompl_patch_closed : IsClosed[constructibleTopology Y] (f '' Uᶜ) :=
    hpatch_closedMap _ hUcompl_patch_closed
  -- Specialization stability upgrades a patch-closed subset of a spectral space to a closed subset.
  have hCompl_spec : StableUnderSpecialization (f '' Uᶜ) :=
    hspec.stableUnderSpecialization_image hU.1.isClosed_compl.stableUnderSpecialization
  have hCompl_closed : IsClosed (f '' Uᶜ) :=
    isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
      hCompl_patch_closed hCompl_spec
  -- Bijectivity identifies the complement of the image with the image of the complement.
  rw [← isClosed_compl_iff, ← Set.image_compl_eq hf_bijective]
  exact hCompl_closed

-- Proof sketch: pass to the constructible topologies, where a spectral space is compact Hausdorff;
-- then a bijective spectral map is a homeomorphism there. For lifted generalizations, the image of
-- each quasi-compact open basis element is patch-open and stable under generalization, hence open
-- in the original topology by Lemma `5.23.6`. For lifted specializations, apply the same argument
-- to the complement of a quasi-compact open basis element to show its image complement is closed,
-- so the basis image itself is open. Thus `f` is an open bijection, hence a homeomorphism.
/-- Lemma 5.23.11: a bijective spectral map between spectral spaces is a homeomorphism if either
specializations or generalizations lift along the map. -/
theorem isHomeomorph_of_isSpectralMap_bijective_of_lift_specializations_or_generalizations
    (hf : IsSpectralMap f) (hf_bijective : Function.Bijective f)
    (hLift : SpecializingMap f ∨ GeneralizingMap f) : IsHomeomorph f := by
  -- Once the map is known to be open in the original topology, continuity and bijectivity finish.
  refine ⟨hf.continuous, ?_, hf_bijective⟩
  rcases hLift with hspec | hgen
  · exact isOpenMap_of_isSpectralMap_bijective_of_specializingMap hf hf_bijective hspec
  · exact isOpenMap_of_isSpectralMap_bijective_of_generalizingMap hf hf_bijective hgen

end
