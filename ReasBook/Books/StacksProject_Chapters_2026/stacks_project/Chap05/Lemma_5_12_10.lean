module

public import Mathlib.Topology.Spectral.Prespectral

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
  [QuasiSeparatedSpace X]

namespace PrespectralSpace

/- Domain-style sampling:
- primary domain: connected components and clopen separation in compact prespectral
  quasi-separated spaces;
- same-domain owner declarations inspected:
  `PrespectralSpace.isTopologicalBasis`,
  `QuasiSeparatedSpace.inter_isCompact`,
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`;
- best owner abstraction: `connectedComponent x`, with the compact-open hypotheses carried by the
  canonical ambient owners `PrespectralSpace` and `QuasiSeparatedSpace`, not by a parallel
  basis-data wrapper.

Layer triage:
- `source-facing`: the Stacks lemma identifying `connectedComponent x` with the intersection of
  the clopen neighborhoods of `x` under the weaker prespectral/quasi-separated hypotheses.
- `core/canonical`: `connectedComponent`, `IsClopen`, `PrespectralSpace`, `QuasiSeparatedSpace`.
- `bridge/view`: the clopen-superset reformulation is derivable from the source-facing theorem and
  `connectedComponent_subset_iInter_isClopen`, so it is not kept as separate public API here.

Primitive data is only the point `x` together with the ambient owner instances
`[CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]`. The basis and compact-intersection
machinery is derived from those owners, so it should not remain encoded in the public theorem
name.
-/

-- Proof sketch: the inclusion from the connected component into every clopen neighbourhood is
-- canonical. For the reverse inclusion, let `S` be the intersection of all clopen neighbourhoods
-- of `x`; using compactness of closed subsets, the basis of compact opens, and compactness of
-- intersections of compact opens, show that any clopen decomposition of `S` yields a clopen
-- neighbourhood of `x` cutting off one side, so `S` is connected and hence equals
-- `connectedComponent x`.
/-
This is source-facing rather than a recall: mathlib's global theorem
`connectedComponent_eq_iInter_isClopen` assumes `[T2Space X]`, while the Stacks lemma keeps the
weaker `[PrespectralSpace X] [QuasiSeparatedSpace X]` hypotheses. The canonical forward inclusion is
still reused directly from mathlib; only the reverse inclusion is specific to this source item.
-/
/-- Lemma 5.12.10: in a quasi-compact topological space with a basis of quasi-compact opens whose
pairwise intersections are quasi-compact, the connected component containing `x` is the
intersection of all open and closed subsets containing `x`.

This is stated using the canonical typeclass interface
`[PrespectralSpace X] [QuasiSeparatedSpace X]` for the basis and intersection hypotheses.
The point-based clopen-neighborhood surface is the canonical owner-facing interface; equivalent
reformulations indexed by clopen supersets of `connectedComponent x` are derived views and should
be downstream bridges, not parallel owners. -/
theorem connectedComponent_eq_iInter_isClopen
    (x : X) :
    connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z := by
  classical
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  set S : Set X := ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z with hS
  have hxS : x ∈ S := by
    rw [hS]
    exact mem_iInter.2 fun Z ↦ Z.2.2
  refine IsPreconnected.subset_connectedComponent ?_ hxS
  have hS_closed : IsClosed S := by
    rw [hS]
    exact isClosed_iInter fun Z ↦ Z.2.1.isClosed
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hS_closed]
  intro a b ha hb hSab hab
  have hSa_compact : IsCompact (S ∩ a) := (hS_closed.inter ha).isCompact
  have hSb_compact : IsCompact (S ∩ b) := (hS_closed.inter hb).isCompact
  have hSa_subset_bcompl : S ∩ a ⊆ bᶜ := by
    intro y hy hyb
    exact hab.le_bot ⟨hy.2, hyb⟩
  have hSb_subset_acompl : S ∩ b ⊆ aᶜ := by
    intro y hy hya
    exact hab.symm.le_bot ⟨hy.2, hya⟩
  obtain ⟨U, hU_compact, hU_open, hSaU, hUb⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hSa_compact hb.isOpen_compl hSa_subset_bcompl
  obtain ⟨V, hV_compact, hV_open, hSbV, hVa⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hSb_compact ha.isOpen_compl hSb_subset_acompl
  have hS_subset_UV : S ⊆ U ∪ V := by
    intro y hyS
    rcases hSab hyS with hya | hyb
    · exact Or.inl (hSaU ⟨hyS, hya⟩)
    · exact Or.inr (hSbV ⟨hyS, hyb⟩)
  have hSUV_empty : S ∩ (U ∩ V) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro y hy
    rcases hSab hy.1 with hya | hyb
    · exact hVa hy.2.2 hya
    · exact hUb hy.2.1 hyb
  let K : Set X := (U ∩ V) ∪ (U ∪ V)ᶜ
  have hK_compact : IsCompact K := by
    refine (QuasiSeparatedSpace.inter_isCompact U V hU_open hU_compact hV_open hV_compact).union ?_
    exact (hU_open.union hV_open).isClosed_compl.isCompact
  have hKS_empty : K ∩ S = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro y hy
    rcases hy.1 with hyUV | hyUV
    · have : y ∉ S ∩ (U ∩ V) := by simp [hSUV_empty]
      exact this ⟨hy.2, hyUV⟩
    · exact hyUV (hS_subset_UV hy.2)
  obtain ⟨u, hu⟩ :=
    hK_compact.elim_finite_subfamily_closed
      (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
      (fun Z ↦ Z.2.1.isClosed) hKS_empty
  let C : Set X := ⋂ Z ∈ u, (Z : Set X)
  have hC_clopen : IsClopen C := isClopen_biInter_finset fun Z _ ↦ Z.2.1
  have hxC : x ∈ C := by
    exact mem_iInter₂.2 fun Z hZ ↦ Z.2.2
  have hKC_empty : K ∩ C = ∅ := by
    simpa [C] using hu
  have hC_subset_UV : C ⊆ U ∪ V := by
    intro y hyC
    by_contra hyUV
    have hyK : y ∈ K := Or.inr <| by simpa using hyUV
    have : y ∈ K ∩ C := ⟨hyK, hyC⟩
    simp [hKC_empty] at this
  have hCUV_empty : C ∩ U ∩ V = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro y hy
    have hyK : y ∈ K := Or.inl ⟨hy.1.2, hy.2⟩
    have : y ∈ K ∩ C := ⟨hyK, hy.1.1⟩
    simp [hKC_empty] at this
  rcases hSab hxS with hxa | hxb
  · have hxU : x ∈ U := hSaU ⟨hxS, hxa⟩
    have hCU_clopen : IsClopen (C ∩ U) :=
      isClopen_inter_of_disjoint_cover_clopen' hC_clopen hC_subset_UV hU_open hV_open hCUV_empty
    have hS_subset_CU : S ⊆ C ∩ U := by
      rw [hS]
      exact iInter_subset (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
        ⟨C ∩ U, hCU_clopen, ⟨hxC, hxU⟩⟩
    left
    intro y hyS
    have hyCU : y ∈ C ∩ U := hS_subset_CU hyS
    rcases hSab hyS with hya | hyb
    · exact hya
    · exact (hUb hyCU.2 hyb).elim
  · have hxV : x ∈ V := hSbV ⟨hxS, hxb⟩
    have hCVU_empty : C ∩ V ∩ U = ∅ := by
      simpa [inter_assoc, inter_left_comm, inter_comm] using hCUV_empty
    have hCV_clopen : IsClopen (C ∩ V) :=
      isClopen_inter_of_disjoint_cover_clopen' hC_clopen (by simpa [union_comm] using hC_subset_UV)
        hV_open hU_open hCVU_empty
    have hS_subset_CV : S ⊆ C ∩ V := by
      rw [hS]
      exact iInter_subset (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
        ⟨C ∩ V, hCV_clopen, ⟨hxC, hxV⟩⟩
    right
    intro y hyS
    have hyCV : y ∈ C ∩ V := hS_subset_CV hyS
    rcases hSab hyS with hya | hyb
    · exact (hVa hyCV.2 hya).elim
    · exact hyb

end PrespectralSpace
