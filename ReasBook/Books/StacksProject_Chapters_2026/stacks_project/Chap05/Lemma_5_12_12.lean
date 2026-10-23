module

public import Mathlib.Topology.Spectral.Prespectral
import stacks_project.Chap05.Lemma_5_12_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
  [QuasiSeparatedSpace X] {T : Set X}

/- Domain-style sampling for intersections of clopen supersets and connected-component saturation:
- primary domain: connected components and clopen separation in compact prespectral
  quasi-separated spaces
- same-domain owner declarations inspected:
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`,
  `IsClopen.connectedComponent_subset`,
  `connectedComponent_subset_iInter_isClopen`,
  `IsClopen.biUnion_connectedComponent_eq`
- best owner abstraction: `connectedComponent x`, with the ambient hypotheses carried by
  `PrespectralSpace` and `QuasiSeparatedSpace`

Layer triage:
- `source-facing`: the subset-level criterion that a set is an intersection of clopen subsets
  exactly when it is closed and a union of connected components
- `core/canonical`: the pointwise owner `connectedComponent x` together with clopen neighborhood
  API
- `bridge/view`: the subset-level `sInter` proof step for the family of all clopen supersets of
  `T`, derived from the pointwise owner

Primitive data are the subset `T`, its closedness, and the component-saturation property
`∀ x ∈ T, connectedComponent x ⊆ T`. The clopen-superset intersection is derived from those data,
so the file should remain a bridge theorem over the connected-component owner rather than
introducing a parallel wrapper notion.
-/

-- Proof sketch: write `T` as an `sInter` of clopen subsets, and use that arbitrary intersections
-- of closed sets are closed.
/-- Lemma 5.12.12 (1): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is an intersection of open and closed subsets, then it is closed.
-/
theorem isClosed_of_isIntersectionOfClopens
    (hT : ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S) :
    IsClosed T := by
  rcases hT with ⟨S, hS_clopen, rfl⟩
  -- An intersection of clopen subsets is an intersection of closed subsets.
  exact isClosed_sInter fun Z hZ ↦ (hS_clopen Z hZ).isClosed

-- Proof sketch: every clopen set containing `x` contains the full connected component of `x`; an
-- intersection of such clopen sets is therefore saturated under connected components.
/-- Lemma 5.12.12 (2): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is an intersection of open and closed subsets, then it is a union
of connected components of `X`. -/
theorem connectedComponent_subset_of_isIntersectionOfClopens
    (hT : ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S)
    (x : X) (hx : x ∈ T) :
    connectedComponent x ⊆ T := by
  rcases hT with ⟨S, hS_clopen, rfl⟩
  rw [mem_sInter] at hx
  intro y hy
  rw [mem_sInter]
  intro Z hZ
  -- Each clopen factor containing `x` contains the whole connected component of `x`.
  exact (hS_clopen Z hZ).connectedComponent_subset (hx Z hZ) hy

/-- Helper for Lemma 5.12.12: a component-saturated subset is disjoint from the connected
component of any point outside it. -/
lemma disjoint_connectedComponent_of_not_mem
    (hT_components : ∀ y ∈ T, connectedComponent y ⊆ T) {x : X} (hx : x ∉ T) :
    T ∩ connectedComponent x = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro y hy
  -- A point of `T ∩ connectedComponent x` forces `x` back into `T` by component saturation.
  have hxy : connectedComponent y = connectedComponent x := (connectedComponent_eq hy.2).symm
  have hx_component : x ∈ connectedComponent y := by
    rw [hxy]
    exact mem_connectedComponent
  exact hx (hT_components y hy.1 hx_component)

/-- Helper for Lemma 5.12.12: a closed component-saturated subset can be separated from any
outside point by a clopen superset. -/
lemma exists_isClopen_superset_not_mem_of_isClosed_of_component_saturated
    (hT_closed : IsClosed T) (hT_components : ∀ y ∈ T, connectedComponent y ⊆ T)
    {x : X} (hx : x ∉ T) :
    ∃ U : Set X, IsClopen U ∧ T ⊆ U ∧ x ∉ U := by
  classical
  have h_disjoint : T ∩ connectedComponent x = ∅ :=
    disjoint_connectedComponent_of_not_mem hT_components hx
  have h_inter :
      T ∩ ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, (Z : Set X) = ∅ := by
    -- Rewrite the connected component as the intersection of its clopen neighbourhoods.
    simpa [PrespectralSpace.connectedComponent_eq_iInter_isClopen x] using h_disjoint
  obtain ⟨u, hu⟩ :=
    hT_closed.isCompact.elim_finite_subfamily_closed
      (fun Z : { Z : Set X // IsClopen Z ∧ x ∈ Z } ↦ (Z : Set X))
      (fun Z ↦ Z.2.1.isClosed) h_inter
  let V : Set X := ⋂ Z ∈ u, (Z : Set X)
  have hV_clopen : IsClopen V := by
    -- A finite intersection of the chosen clopen neighbourhoods is still clopen.
    exact isClopen_biInter_finset fun Z _ ↦ Z.2.1
  have hxV : x ∈ V := by
    -- Every chosen neighbourhood contains `x`, so their finite intersection does too.
    exact mem_iInter₂.2 fun Z hZ ↦ Z.2.2
  have hTV_empty : T ∩ V = ∅ := by
    simpa [V] using hu
  refine ⟨Vᶜ, hV_clopen.compl, ?_, ?_⟩
  · -- Disjointness of `T` and `V` means `T` lands in the complement of `V`.
    intro y hyT
    simp only [mem_compl_iff]
    intro hyV
    have hyTV : y ∈ T ∩ V := ⟨hyT, hyV⟩
    simp [hTV_empty] at hyTV
  · -- Since `x ∈ V`, the separating clopen superset `Vᶜ` omits `x`.
    intro hxVcompl
    exact hxVcompl hxV

-- Proof sketch: intersect all clopen supersets of `T`; closedness gives compactness of `T`, and
-- component saturation lets one separate any point outside `T` from `T` by a clopen superset.
/-- Lemma 5.12.12 (3): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is closed and is a union of connected components of `X`, then it
is an intersection of open and closed subsets. -/
theorem isIntersectionOfClopens_of_isClosed_of_union_connectedComponents
    (hT_closed : IsClosed T) (hT_components : ∀ x ∈ T, connectedComponent x ⊆ T) :
    ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S := by
  classical
  refine ⟨{ U : Set X | IsClopen U ∧ T ⊆ U }, ?_, ?_⟩
  · intro U hU
    exact hU.1
  · apply Subset.antisymm
    · intro y hyT
      rw [mem_sInter]
      intro U hU
      exact hU.2 hyT
    · intro y hy_inter
      by_contra hyT
      obtain ⟨U, hU_clopen, hTU, hyU⟩ :=
        exists_isClopen_superset_not_mem_of_isClosed_of_component_saturated
          hT_closed hT_components hyT
      -- The separating clopen superset belongs to the defining family of the intersection.
      have hy_mem : y ∈ U := by
        rw [mem_sInter] at hy_inter
        exact hy_inter U ⟨hU_clopen, hTU⟩
      exact hyU hy_mem

end
