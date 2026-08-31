module

public import Mathlib.Topology.Spectral.ConstructibleTopology
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

/- Domain-style sampling for patch-closed subspaces of spectral spaces:
- primary domain: spectral spaces, constructible topology, and spectral subspaces;
- sampled owner declarations:
  `SpectralSpace`,
  `PrespectralSpace.of_isTopologicalBasis'`,
  `isOpen_constructibleTopology_of_isConstructible`,
  `IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed`;
- best owner abstractions:
  `SpectralSpace` for the ambient/subspace notion,
  `constructibleTopology` for patch-closedness,
  and the generic-point owner `IsGenericPoint` for the irreducible-closure contradiction.

Layer triage:
- `source-facing`: Lemma 5.23.5, asserting that a constructible-topology-closed subspace of a
  spectral space is spectral in the induced topology;
- `core/canonical`: `SpectralSpace`, `constructibleTopology`, and the compact-open basis owner
  `PrespectralSpace.isTopologicalBasis`;
- `bridge/view`: the closed-subspace spectral helper and the constructible-topology continuity of
  subtype maps.

Primitive data is only the ambient spectral-space structure and the patch-closed subset. The
compact-open basis, quasi-separatedness, and the needed generic-point contradiction are derived
from the existing owners and should not be repackaged locally.
-/

noncomputable section

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X] {E : Set X}

private theorem isTopologicalBasis_subtype_compactOpens (S : Set X) :
    IsTopologicalBasis
      (Set.range fun U : CompactOpens X ↦ (Subtype.val : S → X) ⁻¹' (U : Set X)) := by
  convert
    (PrespectralSpace.isTopologicalBasis.isInducing IsEmbedding.subtypeVal.isInducing :
      IsTopologicalBasis
        (((Subtype.val : S → X) ⁻¹' ·) '' { U : Set X | IsOpen U ∧ IsCompact U }))
  ext V
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨(U : Set X), ⟨U.isOpen, U.isCompact⟩, rfl⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨⟨⟨U, hU.2⟩, hU.1⟩, rfl⟩

private theorem spectralSpace_subtype_of_isClosed {S : Set X} (hS : IsClosed S) :
    SpectralSpace S := by
  let b : CompactOpens X → Set S := fun U ↦ (Subtype.val : S → X) ⁻¹' (U : Set X)
  have hBasis : IsTopologicalBasis (Set.range b) :=
    isTopologicalBasis_subtype_compactOpens S
  have hCompactBasis : ∀ U : CompactOpens X, IsCompact (b U) := by
    intro U
    rw [Subtype.isCompact_iff]
    simpa [b, Set.image_preimage_eq_inter_range, Set.inter_comm] using U.isCompact.inter_right hS
  have hCompactInter :
      ∀ U V : CompactOpens X, IsCompact (b U ∩ b V) := by
    intro U V
    have hUV_compact :
        IsCompact ((U : Set X) ∩ (V : Set X)) :=
      QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X) U.isOpen U.isCompact V.isOpen
        V.isCompact
    rw [Subtype.isCompact_iff]
    simpa [b, Set.image_inter, Set.image_preimage_eq_inter_range, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using
      ((hUV_compact.inter_right hS).inter_right hS :
        IsCompact ((((U : Set X) ∩ (V : Set X)) ∩ S) ∩ S))
  have hCompactSubspace : IsCompact S := hS.isCompact
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hCompactSubspace
  refine
    { toT0Space := IsEmbedding.subtypeVal.t0Space
      toCompactSpace := inferInstance
      toQuasiSober := hS.isClosedEmbedding_subtypeVal.quasiSober
      toQuasiSeparatedSpace := QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
      toPrespectralSpace := PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis }

/-- Helper for Lemma 5.23.5: a subset closed in the constructible topology contains a
specialization point over each point in its ordinary closure. -/
private theorem exists_specializingPoint_of_mem_closure_patch_closed
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) {x : X} (hx : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := by
  let 𝒰 : Type u := { U : CompactOpens X // x ∈ (U : Set X) }
  let F : 𝒰 → Set X := fun U ↦ E ∩ (U.1 : Set X)
  have hPatchCompact : CompactSpace (WithConstructibleTopology X) := inferInstance
  have hF_closed_patch : ∀ U : 𝒰, IsClosed[constructibleTopology X] (F U) := by
    intro U
    have hU_constructible : IsConstructible (U.1 : Set X) :=
      U.1.isCompact.isConstructible U.1.isOpen
    have hU_closed_patch : IsClosed[constructibleTopology X] (U.1 : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible hU_constructible).1
    letI : TopologicalSpace X := constructibleTopology X
    exact hE.inter hU_closed_patch
  have hF_nonempty : ∀ U : 𝒰, (F U).Nonempty := by
    intro U
    rcases mem_closure_iff.1 hx (U.1 : Set X) U.1.isOpen U.2 with ⟨z, hzU, hzE⟩
    exact ⟨z, hzE, hzU⟩
  have hF_directed : Directed (· ⊇ ·) F := by
    intro U V
    refine ⟨⟨U.1 ⊓ V.1, by simpa [CompactOpens.coe_inf] using ⟨U.2, V.2⟩⟩, ?_, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2.1⟩
    · intro y hy
      exact ⟨hy.1, hy.2.2⟩
  haveI : Nonempty 𝒰 := ⟨⟨⊤, by simp⟩⟩
  have hF_compact_patch : ∀ U : 𝒰, @IsCompact X (constructibleTopology X) (F U) := by
    intro U
    letI : TopologicalSpace X := constructibleTopology X
    letI : CompactSpace X := by
      simpa [WithConstructibleTopology] using hPatchCompact
    exact (hF_closed_patch U).isCompact
  obtain ⟨y, hy⟩ :=
    Set.nonempty_iInter.mp <|
      @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        X (constructibleTopology X) 𝒰 inferInstance F hF_directed hF_nonempty
        hF_compact_patch hF_closed_patch
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure]
    refine mem_closure_iff.2 fun U hU hxU ↦ ?_
    obtain ⟨V, ⟨hV_open, hV_compact⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
    let W : 𝒰 := ⟨⟨⟨V, hV_compact⟩, hV_open⟩, hxV⟩
    exact ⟨y, hVU (hy W).2, by simp⟩
  let Utop : 𝒰 := ⟨⊤, by simp⟩
  exact ⟨y, (hy Utop).1, hyx⟩

-- Proof sketch: argue as in Stacks Project, Tag 0902. Quasi-compactness comes from patch
-- compactness, sobriety from the generic point of the closure of a closed irreducible subset,
-- and the quasi-compact open basis is given by intersections `E ∩ U` with `U` quasi-compact open
-- in `X`.
/-- Lemma 5.23.5: if `X` is spectral and `E ⊆ X` is closed in the constructible topology, then
`E` with the induced topology is a spectral space. In particular this applies when `E` is
constructible or closed in `X`. -/
theorem spectralSpace_subtype_of_isClosed_constructibleTopology
    (hE : IsClosed[constructibleTopology X] E) : SpectralSpace E := by
  let b : CompactOpens X → Set E := fun U ↦ (Subtype.val : E → X) ⁻¹' (U : Set X)
  have hBasis : IsTopologicalBasis (Set.range b) :=
    isTopologicalBasis_subtype_compactOpens E
  have hOriginalOpen :
      ∀ ⦃s : Set X⦄, IsOpen s → IsOpen[constructibleTopology X] s := by
    intro s hs
    obtain ⟨S, hSB, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
    exact @isOpen_sUnion X (constructibleTopology X) S fun t ht ↦
      (hSB ht).2.isOpen_constructibleTopology_of_isOpen (hSB ht).1
  have hContToOriginal : @Continuous X X (constructibleTopology X) ‹TopologicalSpace X› id := by
    rw [continuous_def]
    intro s hs
    exact hOriginalOpen hs
  have hPatchCompact : @CompactSpace X (constructibleTopology X) :=
    constructibleTopology_compactSpace_of_spectralSpace
  have hCompact_of_patch_closed {s : Set X} (hs : IsClosed[constructibleTopology X] s) :
      IsCompact s := by
    have hs_compact : @IsCompact X (constructibleTopology X) s := by
      letI : TopologicalSpace X := constructibleTopology X
      letI : CompactSpace X := hPatchCompact
      change IsCompact s
      exact IsClosed.isCompact hs
    simpa using
      @IsCompact.image X X (constructibleTopology X) ‹TopologicalSpace X› s id hs_compact
        hContToOriginal
  have hCompactSubspace : IsCompact E := by
    exact hCompact_of_patch_closed hE
  have hCompactBasis : ∀ U : CompactOpens X, IsCompact (b U) := by
    intro U
    have hU_closed_constructible : IsClosed[constructibleTopology X] (U : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible
        (U.isCompact.isConstructible U.isOpen)).1
    have hEU_closed_constructible : IsClosed[constructibleTopology X] (E ∩ (U : Set X)) := by
      letI : TopologicalSpace X := constructibleTopology X
      exact hE.inter hU_closed_constructible
    rw [Subtype.isCompact_iff]
    simpa [b, Set.image_preimage_eq_inter_range, Set.inter_comm] using
      hCompact_of_patch_closed hEU_closed_constructible
  have hCompactInter :
      ∀ U V : CompactOpens X, IsCompact (b U ∩ b V) := by
    intro U V
    have hU_closed_constructible : IsClosed[constructibleTopology X] (U : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible
        (U.isCompact.isConstructible U.isOpen)).1
    have hV_closed_constructible : IsClosed[constructibleTopology X] (V : Set X) :=
      (isClopen_constructibleTopology_of_isConstructible
        (V.isCompact.isConstructible V.isOpen)).1
    have hTarget_closed :
        IsClosed[constructibleTopology X] (E ∩ (E ∩ ((U : Set X) ∩ (V : Set X)))) := by
      letI : TopologicalSpace X := constructibleTopology X
      exact hE.inter <| hE.inter <| hU_closed_constructible.inter hV_closed_constructible
    rw [Subtype.isCompact_iff]
    convert
      (hCompact_of_patch_closed hTarget_closed :
        IsCompact (E ∩ (E ∩ ((U : Set X) ∩ (V : Set X))))) using 1
    ext x
    simp [b, Set.image_inter, Set.image_preimage_eq_inter_range, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm]
  letI : CompactSpace E := isCompact_iff_compactSpace.mp hCompactSubspace
  have hQuasiSober : QuasiSober E := by
    rw [quasiSober_iff]
    intro S hS_irred hS_closed
    let T : Set X := (Subtype.val : E → X) '' S
    let C : Set X := closure T
    have hT_subset : T ⊆ E := by
      rintro _ ⟨y, hyS, rfl⟩
      exact y.2
    have hT_irred : IsIrreducible T := hS_irred.image Subtype.val continuous_subtype_val.continuousOn
    have hC_irred : IsIrreducible C := hT_irred.closure
    have hC_spectral : SpectralSpace C :=
      spectralSpace_subtype_of_isClosed isClosed_closure
    letI : SpectralSpace C := hC_spectral
    have hSC_eq :
        S = (Subtype.val : E → X) ⁻¹' C := by
      calc
        S = closure S := hS_closed.closure_eq.symm
        _ = (Subtype.val : E → X) ⁻¹' closure T := by
          simpa [T] using IsEmbedding.subtypeVal.closure_eq_preimage_closure_image S
        _ = (Subtype.val : E → X) ⁻¹' C := rfl
    let T' : Set C := (Subtype.val : C → X) ⁻¹' E
    have hT'_closed :
        IsClosed[constructibleTopology C] T' := by
      have hClosureProper : IsProperMap (Subtype.val : C → X) :=
        isClosed_closure.isClosedEmbedding_subtypeVal.isProperMap
      have hClosureSpectralMap : IsSpectralMap (Subtype.val : C → X) :=
        hClosureProper.isSpectralMap
      have hSubtypePatchCont :
          Continuous[constructibleTopology C, constructibleTopology X] (Subtype.val : C → X) :=
        hClosureSpectralMap.continuous_constructibleTopology
      letI : TopologicalSpace C := constructibleTopology C
      letI : TopologicalSpace X := constructibleTopology X
      exact (show IsClosed E from hE).preimage
        (show Continuous (Subtype.val : C → X) from hSubtypePatchCont)
    let S' : Set C := (Subtype.val : C → X) ⁻¹' T
    have hS'_subset : S' ⊆ T' := by
      intro z hz
      exact hT_subset hz
    have hImageS' : (Subtype.val : C → X) '' S' = T := by
      rw [Set.image_preimage_eq_of_subset]
      simpa [C] using (subset_closure : T ⊆ closure T)
    have hClosureS' : closure S' = univ := by
      calc
        closure S' = (Subtype.val : C → X) ⁻¹' closure ((Subtype.val : C → X) '' S') := by
          simpa using IsEmbedding.subtypeVal.closure_eq_preimage_closure_image S'
        _ = (Subtype.val : C → X) ⁻¹' closure T := by simp [hImageS']
        _ = univ := by ext z; simp
    have hClosureT' : closure T' = univ := by
      apply eq_univ_iff_forall.2
      intro z
      have hz : z ∈ closure S' := by simp [hClosureS']
      exact closure_mono hS'_subset hz
    letI : IrreducibleSpace C := Subtype.irreducibleSpace hC_irred
    let x : C := genericPoint C
    have hx_mem_closure : x ∈ closure T' := by
      simp [hClosureT']
    obtain ⟨y, hyT', hyx⟩ :=
      exists_specializingPoint_of_mem_closure_patch_closed hT'_closed hx_mem_closure
    have hy_generic_C : IsGenericPoint y (univ : Set C) := by
      rw [isGenericPoint_iff_specializes]
      intro z
      constructor
      · intro hyz
        simp
      · intro hz
        exact hyx.trans (genericPoint_specializes z)
    have hy_closure : closure ({y.1} : Set X) = C := by
      have hPreimageClosure :
          (Subtype.val : C → X) ⁻¹' closure ({y.1} : Set X) = univ := by
        calc
          (Subtype.val : C → X) ⁻¹' closure ({y.1} : Set X)
              = closure ({y} : Set C) := by
                symm
                simpa using
                  IsEmbedding.subtypeVal.closure_eq_preimage_closure_image ({y} : Set C)
          _ = univ := hy_generic_C.def
      have hC_subset : C ⊆ closure ({y.1} : Set X) := by
        intro z hz
        have : (⟨z, hz⟩ : C) ∈ (Subtype.val : C → X) ⁻¹' closure ({y.1} : Set X) := by
          simp [hPreimageClosure]
        exact this
      have hclosure_subset : closure ({y.1} : Set X) ⊆ C :=
        isClosed_closure.closure_subset_iff.2 (by simp)
      exact subset_antisymm hclosure_subset hC_subset
    refine ⟨⟨y.1, hyT'⟩, ?_⟩
    calc
      closure ({⟨y.1, hyT'⟩} : Set E)
          = (Subtype.val : E → X) ⁻¹' closure ({y.1} : Set X) := by
            simpa using
              IsEmbedding.subtypeVal.closure_eq_preimage_closure_image ({⟨y.1, hyT'⟩} : Set E)
      _ = (Subtype.val : E → X) ⁻¹' C := by rw [hy_closure]
      _ = S := hSC_eq.symm
  refine
    { toT0Space := IsEmbedding.subtypeVal.t0Space
      toCompactSpace := inferInstance
      toQuasiSober := hQuasiSober
      toQuasiSeparatedSpace := QuasiSeparatedSpace.of_isTopologicalBasis hBasis hCompactInter
      toPrespectralSpace := PrespectralSpace.of_isTopologicalBasis' hBasis hCompactBasis }

end
