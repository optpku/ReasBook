module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
import stacks_project.Chap05.Lemma_5_22_2
import stacks_project.Chap05.Lemma_5_23_2
import stacks_project.Chap05.Lemma_5_23_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/- Domain-style sampling for Lemma 5.23.8:
- primary domain: spectral spaces, constructible topology, specialization order, and irreducible
  components
- owner declarations inspected:
  `TotallyDisconnectedSpace`,
  `totallyDisconnectedSpace_iff_connectedComponent_subsingleton`,
  `irreducibleComponent`,
  `PrespectralSpace.isTopologicalBasis`
- best owner abstraction: the ambient spectral-space/topological-space owners together with the
  canonical owner set `irreducibleComponent x`
- primitive data: the ambient topological owner instances and the canonical irreducible component
  through a point
- derived API: singleton/closedness consequences, trivial-specialization criteria, and the
  constructible-topology comparison

Layer triage:
- `source-facing`: the Stacks TFAE statement for spectral spaces
- `core/canonical`: mathlib’s owners `TotallyDisconnectedSpace`, `irreducibleComponent`,
  `constructibleTopology`, and `PrespectralSpace.isTopologicalBasis`
- `bridge/view`: the TFAE implications relating those owner-level notions

The theorem is source-facing, so it remains a theorem. The refinement target is therefore its
proof surface: reuse owner-level declarations directly, delete local proof noise, and avoid
parallel wrappers or redundant argument plumbing.
-/

-- Proof sketch: combine the earlier spectral-space criteria. Lemma `5.22.2` gives the profinite
-- versus compact Hausdorff totally disconnected comparison; spectral spaces are sober, so
-- triviality of specializations is equivalent to every point being closed and to every point being
-- the generic point of its irreducible component; Lemma `5.23.6` identifies constructible subsets
-- with clopen subsets under trivial specialization, and the definition of `constructibleTopology`
-- turns closedness of quasi-compact opens into equality with the original topology.
/-- Lemma 5.23.8: for a spectral space, the eight explicit visible conditions in the Stacks
statement are equivalent: profiniteness, Hausdorffness, total disconnectedness, closedness of
quasi-compact opens, triviality of specializations, closedness of all points, each point being the
generic point of an irreducible component, and equality of the constructible and given topologies.
-/
theorem spectralSpace_profinite_criteria
    (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P),
        T2Space X,
        TotallyDisconnectedSpace X,
        ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U,
        ∀ ⦃x y : X⦄, x ⤳ y → x = y,
        ∀ x : X, IsClosed ({x} : Set X),
        ∀ x : X, IsGenericPoint x (irreducibleComponent x),
        constructibleTopology X = ‹TopologicalSpace X› ] := by
  tfae_have 1 → 3 := by
    rintro ⟨P, ⟨e⟩⟩
    exact e.symm.totallyDisconnectedSpace
  tfae_have 2 → 4 := by
    intro hT2 U hU hUcompact
    letI : T2Space X := hT2
    exact hUcompact.isClosed
  tfae_have 3 → 7 := by
    intro hTot x
    letI : TotallyDisconnectedSpace X := hTot
    -- A totally disconnected irreducible component is a singleton, so its generic point is the
    -- unique point it contains.
    have hpre : IsPreconnected (irreducibleComponent x) :=
      isIrreducible_irreducibleComponent.2.isPreconnected
    have hsub :
        (irreducibleComponent x).Subsingleton :=
      hpre.subsingleton
    have hEq : irreducibleComponent x = ({x} : Set X) := by
      ext y
      constructor
      · intro hy
        exact hsub hy mem_irreducibleComponent
      · rintro rfl
        exact mem_irreducibleComponent
    have hxClosed : IsClosed ({x} : Set X) := by
      exact hEq ▸ (isClosed_irreducibleComponent : IsClosed (irreducibleComponent x))
    exact hxClosed.closure_eq.trans hEq.symm
  tfae_have 4 → 8 := by
    intro hCompactOpenClosed
    apply le_antisymm
    · intro s hs
      obtain ⟨S, hSB, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
      exact @isOpen_sUnion X (constructibleTopology X) S fun t ht ↦
        (hSB ht).2.isOpen_constructibleTopology_of_isOpen (hSB ht).1
    · rw [constructibleTopology]
      exact le_generateFrom fun s hs ↦ by
        rcases hs with hs | hs
        · exact hs.1
        · simpa using (hCompactOpenClosed sᶜ hs.1.isOpen_compl hs.2).isOpen_compl
  tfae_have 5 → 6 := by
    intro hSpecializesEq x
    letI : T1Space X := t1Space_iff_specializes_imp_eq.mpr fun _ _ h ↦ hSpecializesEq h
    exact isClosed_singleton
  tfae_have 5 → 8 := by
    intro hSpecializesEq
    apply le_antisymm
    · intro s hs
      obtain ⟨S, hSB, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
      exact @isOpen_sUnion X (constructibleTopology X) S fun t ht ↦
        (hSB ht).2.isOpen_constructibleTopology_of_isOpen (hSB ht).1
    · rw [constructibleTopology]
      exact le_generateFrom fun s hs ↦ by
        rcases hs with hs | hs
        · exact hs.1
        · exact
            isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
              (hs.2.isOpen_constructibleTopology_of_isClosed hs.1)
              (fun _ _ hxy hx ↦ by simpa [hSpecializesEq hxy] using hx)
  tfae_have 6 → 5 := by
    intro hClosed _ _ hxy
    letI : T1Space X := ⟨hClosed⟩
    exact hxy.eq
  tfae_have 7 → 5 := by
    intro hGeneric x y hxy
    have hy_mem : y ∈ irreducibleComponent x := by
      rw [← (hGeneric x).def]
      exact hxy.mem_closure
    have hComponentSubset : irreducibleComponent y ⊆ irreducibleComponent x := by
      rw [← (hGeneric y).def]
      exact closure_minimal (singleton_subset_iff.mpr hy_mem) isClosed_irreducibleComponent
    have hComponentSubset' : irreducibleComponent x ⊆ irreducibleComponent y :=
      (irreducibleComponent_mem_irreducibleComponents y).2
        isIrreducible_irreducibleComponent hComponentSubset
    have hEq :
        irreducibleComponent x = irreducibleComponent y :=
      subset_antisymm hComponentSubset' hComponentSubset
    have hyGeneric : IsGenericPoint y (irreducibleComponent x) := by
      simpa [hEq] using hGeneric y
    exact (hGeneric x).eq hyGeneric
  tfae_have 8 → 1 := by
    intro hEq
    letI : T2Space X := hEq ▸ constructibleTopology_t2Space_of_spectralSpace
    letI : TotallyDisconnectedSpace X := hEq ▸
      constructibleTopology_totallyDisconnectedSpace_of_spectralSpace
    letI : CompactSpace X := hEq ▸ constructibleTopology_compactSpace_of_spectralSpace
    exact t2Space_compactSpace_totallyDisconnectedSpace_implies_exists_profinite X
  tfae_have 8 → 2 := by
    intro hEq
    exact hEq ▸ constructibleTopology_t2Space_of_spectralSpace
  tfae_finish

end
