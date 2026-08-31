module

public import Mathlib.Topology.Spectral.ConstructibleTopology
import stacks_project.Chap05.Lemma_5_23_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/- Domain-style sampling for Lemma 5.23.6:
- primary domain: spectral spaces, constructible topology, and specialization/generalization
  stability of subsets
- inspected owner declarations:
  `constructibleTopology`,
  `constructibleTopology_t2_totallyDisconnected_and_compact_of_spectralSpace`,
  `isClopen_constructibleTopology_of_isConstructible`,
  `stableUnderGeneralization_compl_iff`
- best owner abstraction: the compact Hausdorff owner `WithConstructibleTopology X` attached to a
  spectral space, together with a subset `E ⊆ X` closed in that constructible topology
- primitive data: the constructible-topology-closed subset `E`; specialization/generalization
  stability is derived extra structure used only for clauses `(2)` and `(3)`
- derived API: clause `(1)` extracts a specializing point from compactness in the constructible
  topology, while clauses `(2)` and `(3)` are closure/open consequences derived from clause `(1)`
  and the canonical complement bridge between specialization and generalization stability

Layer triage:
- `source-facing`: the three Stacks clauses relating constructible-topology closed/open subsets to
  specialization/generalization behavior in a spectral space
- `core/canonical`: the owner abstraction is `WithConstructibleTopology X`
- `bridge/view`: `stableUnderGeneralization_compl_iff`

No upstream theorem in mathlib or earlier Chapter 5 files was found with the exact source-facing
interface of clause `(1)`. The canonical reuse point is therefore the constructible-topology owner
of the ambient spectral space, not a parallel local wrapper around constructible closed data.
-/

-- Proof sketch: intersect `E` with the quasi-compact open neighbourhoods of `x`; in the compact
-- Hausdorff constructible topology these traces are closed, hence compact, and finite
-- intersections stay nonempty because `x` lies in the ordinary closure of `E`.
/-- Lemma 5.23.6 (1): if `E ⊆ X` is closed in the constructible topology of a spectral space and
`x` lies in the ordinary closure of `E`, then `x` is the specialization of some point of `E`.
This matches the Stacks Project statement for subsets closed in the constructible topology, for
example constructible subsets. -/
theorem exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology
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

-- Proof sketch: apply part (1) to a point `x ∈ closure E`; the resulting point of `E`
-- specializing to `x` forces `x ∈ E` by specialization stability, so `closure E ⊆ E`.
/-- Lemma 5.23.6 (2): a constructible-topology-closed subset of a spectral space that is stable
under specialization is closed in the original topology. -/
theorem isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
    {E : Set X} (hE : IsClosed[constructibleTopology X] E)
    (hE_spec : StableUnderSpecialization E) : IsClosed E := by
  exact isClosed_of_closure_subset fun x hx ↦ by
    rcases exists_specializingPoint_of_mem_closure_of_isClosed_constructibleTopology hE hx with
      ⟨y, hyE, hyx⟩
    exact hE_spec hyx hyE

-- Proof sketch: apply part (2) to the complement of `E`; patch-openness gives patch-closedness of
-- the complement, and generalization stability of `E` becomes specialization stability of `Eᶜ`.
/-- Lemma 5.23.6 (3): a subset of a spectral space that is open in the constructible topology and
stable under generalization is open in the original topology. This matches the Stacks Project
statement for subsets open in the constructible topology, for example constructible subsets. -/
theorem isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
    {E : Set X} (hE : IsOpen[constructibleTopology X] E)
    (hE_gen : StableUnderGeneralization E) : IsOpen E := by
  rw [← isClosed_compl_iff]
  have hE_closed : IsClosed[constructibleTopology X] Eᶜ := by
    letI : TopologicalSpace X := constructibleTopology X
    exact hE.isClosed_compl
  exact
    isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization hE_closed hE_gen.compl

end
