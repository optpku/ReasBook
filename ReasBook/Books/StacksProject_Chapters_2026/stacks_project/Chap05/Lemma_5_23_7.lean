module

public import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

variable [SpectralSpace X]

/- Domain-style sampling for spectral separation via specializations:
- owner declarations inspected: `SpectralSpace`, `PrespectralSpace.isTopologicalBasis`,
  `compactSpace_withConstructibleTopology`, `specializes_iff_forall_open`, `SeparatedNhds`
- best owner abstraction: the compact-open basis owner `PrespectralSpace.isTopologicalBasis`,
  together with compactness of `constructibleTopology X`
- primitive data: compact open neighborhoods in a spectral space, and separation by neighborhoods
  via `SeparatedNhds`
- derived API: specialization is recovered from membership in every open neighborhood via
  `specializes_iff_forall_open`

Layer triage:
- `source-facing`: the Stacks dichotomy between a common generalization and separated
  neighborhoods
- `core/canonical`: compact-open basis plus constructible-topology compactness
- `bridge/view`: the source conclusion is expressed through `SeparatedNhds` and `z ⤳ x`, `z ⤳ y`

The public theorem is genuinely source-facing, so it should stay a theorem rather than collapse to
an owner recall. The proof should nevertheless reuse the canonical owner data instead of rebuilding
local wrapper notions of quasi-compact neighborhoods or constructible compactness.
-/

-- Proof sketch: if `x` and `y` do not admit disjoint open neighbourhoods, then every pair of
-- quasi-compact open neighbourhoods of `x` and `y` has nonempty intersection. In the compact
-- constructible topology, finite-intersection compactness gives a point lying in every compact
-- open neighbourhood of both points, hence specializing to both `x` and `y`.
/-- Lemma 5.23.7: in a spectral space, either there exists a third point specializing to both
`x` and `y`, or the singleton subsets `{x}` and `{y}` are separated by neighborhoods, i.e. there
exist disjoint open neighbourhoods containing `x` and `y`. -/
theorem exists_point_specializing_to_both_or_disjoint_open_neighborhoods (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨ SeparatedNhds ({x} : Set X) ({y} : Set X) := by
  by_cases hsep : SeparatedNhds ({x} : Set X) ({y} : Set X)
  · exact Or.inr hsep
  · let 𝒦 : Set (Set X) := {U : Set X | IsOpen U ∧ IsCompact U ∧ (x ∈ U ∨ y ∈ U)}
    have hInter :
        ∀ {U V : Set X}, IsOpen U → IsCompact U → x ∈ U →
          IsOpen V → IsCompact V → y ∈ V → (U ∩ V).Nonempty := by
      intro U V hUopen hUcompact hxU hVopen hVcompact hyV
      by_contra hUV
      apply hsep
      refine ⟨U, V, hUopen, hVopen, ?_, ?_, ?_⟩
      · simpa using singleton_subset_iff.mpr hxU
      · simpa using singleton_subset_iff.mpr hyV
      · exact disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hUV)
    have h𝒦_closed : ∀ U ∈ 𝒦, @IsClosed X (constructibleTopology X) U := by
      intro U hU
      have hUcompact : IsCompact (Uᶜᶜ) := by
        simpa using hU.2.1
      have hUcompl_open : @IsOpen X (constructibleTopology X) Uᶜ := by
        simpa using hUcompact.isOpen_constructibleTopology_of_isClosed hU.1.isClosed_compl
      simpa using @IsOpen.isClosed_compl X (constructibleTopology X) Uᶜ hUcompl_open
    have h𝒦_fip : ∀ t ⊆ 𝒦, t.Finite → (⋂₀ t).Nonempty := by
      intro t ht htfin
      let tx : Set (Set X) := {U : Set X | U ∈ t ∧ x ∈ U}
      let ty : Set (Set X) := {U : Set X | U ∈ t ∧ y ∈ U}
      have htxfin : tx.Finite := htfin.subset fun U hU ↦ hU.1
      have htyfin : ty.Finite := htfin.subset fun U hU ↦ hU.1
      have htx_open : ∀ U ∈ tx, IsOpen U := by
        intro U hU
        exact (ht hU.1).1
      have hty_open : ∀ U ∈ ty, IsOpen U := by
        intro U hU
        exact (ht hU.1).1
      have htx_compact : ∀ U ∈ tx, IsCompact U := by
        intro U hU
        exact (ht hU.1).2.1
      have hty_compact : ∀ U ∈ ty, IsCompact U := by
        intro U hU
        exact (ht hU.1).2.1
      have hx_mem : x ∈ ⋂₀ tx := by
        rw [Set.mem_sInter]
        intro U hU
        exact hU.2
      have hy_mem : y ∈ ⋂₀ ty := by
        rw [Set.mem_sInter]
        intro U hU
        exact hU.2
      have htx_isCompact : IsCompact (⋂₀ tx) :=
        QuasiSeparatedSpace.isCompact_sInter htxfin (fun U hU ↦ Or.inl (htx_open U hU))
          htx_compact
      have hty_isCompact : IsCompact (⋂₀ ty) :=
        QuasiSeparatedSpace.isCompact_sInter htyfin (fun U hU ↦ Or.inl (hty_open U hU))
          hty_compact
      have htx_isOpen : IsOpen (⋂₀ tx) := htxfin.isOpen_sInter htx_open
      have hty_isOpen : IsOpen (⋂₀ ty) := htyfin.isOpen_sInter hty_open
      obtain ⟨z, hztx, hzty⟩ :=
        hInter htx_isOpen htx_isCompact hx_mem hty_isOpen hty_isCompact hy_mem
      refine ⟨z, ?_⟩
      rw [Set.mem_sInter]
      intro U hU
      have hUxy : x ∈ U ∨ y ∈ U := (ht hU).2.2
      cases hUxy with
      | inl hxU =>
          exact Set.mem_sInter.1 hztx U ⟨hU, hxU⟩
      | inr hyU =>
          exact Set.mem_sInter.1 hzty U ⟨hU, hyU⟩
    obtain ⟨z, hz𝒦⟩ :
        (⋂₀ 𝒦).Nonempty := by
      exact
        @CompactSpace.nonempty_sInter X (constructibleTopology X)
          compactSpace_withConstructibleTopology 𝒦 h𝒦_closed h𝒦_fip
    refine Or.inl ⟨z, ?_, ?_⟩
    · rw [specializes_iff_forall_open]
      intro U hU hxU
      obtain ⟨V, ⟨hVopen, hVcompact⟩, hxV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
      have hV𝒦 : V ∈ 𝒦 := ⟨hVopen, hVcompact, Or.inl hxV⟩
      exact hVU (Set.mem_sInter.1 hz𝒦 V hV𝒦)
    · rw [specializes_iff_forall_open]
      intro U hU hyU
      obtain ⟨V, ⟨hVopen, hVcompact⟩, hyV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyU hU
      have hV𝒦 : V ∈ 𝒦 := ⟨hVopen, hVcompact, Or.inr hyV⟩
      exact hVU (Set.mem_sInter.1 hz𝒦 V hV𝒦)
