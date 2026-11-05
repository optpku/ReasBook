module

public import Mathlib.Topology.Spectral.Prespectral

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling:
- owner abstractions: `IsCompactOpenCovered`, `CompactOpens X`, `PrespectralSpace.isBasis_opens`
- same-domain declarations inspected: `IsCompactOpenCovered.of_isOpenMap`,
  `IsCompactOpenCovered.exists_mem_of_isBasis`,
  `PrespectralSpace.isBasis_opens`,
  `CompactOpens.map`

Layer triage:
- `source-facing`: a finite refinement theorem for an open cover of a compact open subset
- `core/canonical`: `IsCompactOpenCovered` together with the compact-open basis on prespectral
  spaces and open subspaces
- `bridge/view`: the finite operational surface lives on `Finset (CompactOpens X)`, while the
  compact-open pieces inside the covering opens are extracted from the owner abstraction

Primitive data are the compact open `U`, the indexed open family `V`, and the cover relation
`(U : Set X) ⊆ ⋃ i, V i`. The finite extraction and the compact-open pieces lying inside the cover
belong to the owner `IsCompactOpenCovered`; the resulting finite `Finset (CompactOpens X)` surface
is only a bridge/view assembled from those owner-level pieces. -/

-- Proof sketch: for each `x ∈ U`, pick a compact-open basis neighborhood contained in one
-- covering open `V i` and still contained in `U`. The resulting family covers `U`, so compactness
-- of `U` yields finitely many such basis pieces, which we then package as a finite family of
-- ambient compact opens subordinate to the original cover.
/-- Lemma 5.27.1: in a prespectral space, every open covering of a quasi-compact open subset
admits a finite refinement by quasi-compact opens. -/
theorem compactOpen_hasCofinalFiniteQuasiCompactRefiningCovers
    [PrespectralSpace X] (U : CompactOpens X)
    {ι : Type v} (V : ι → Opens X) (hV : (U : Set X) ⊆ ⋃ i, (V i : Set X)) :
    ∃ s : Finset (CompactOpens X),
      (U : Set X) = ⋃ W ∈ s, (W : Set X) ∧
        ∀ W ∈ s, ∃ i, (W : Set X) ⊆ V i := by
  classical
  -- For each point of `U`, choose a compact-open basis neighborhood inside one covering open.
  have hpiece :
      ∀ x : U, ∃ (K : CompactOpens X) (i : ι),
        (x : X) ∈ (K : Set X) ∧ (K : Set X) ⊆ (U : Set X) ∩ V i := by
    intro x
    rcases Set.mem_iUnion.1 (hV x.2) with ⟨i, hxi⟩
    have hxUV : (x : X) ∈ (((U.toOpens ⊓ V i : Opens X) : Opens X) : Set X) := by
      simpa using And.intro x.2 hxi
    obtain ⟨K, ⟨hKo, hKc⟩, hxK, hKUV⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hxUV
        (U.toOpens ⊓ V i).isOpen
    exact ⟨⟨⟨K, hKc⟩, hKo⟩, i, hxK, by simpa using hKUV⟩
  choose K idx hxK hKsub using hpiece
  -- Compactness of `U` now extracts finitely many of the chosen compact-open neighborhoods.
  obtain ⟨t, ht⟩ :=
    U.isCompact.elim_finite_subcover
      (fun x : U ↦ (K x : Set X))
      (fun x ↦ (K x).isOpen)
      (by
        intro x hx
        exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxK ⟨x, hx⟩⟩)
  let s : Finset (CompactOpens X) := t.image K
  -- The finite image family still covers `U`, and every chosen piece was already inside `U`.
  have hcover : (U : Set X) = ⋃ W ∈ s, (W : Set X) := by
    refine subset_antisymm ?_ ?_
    · intro x hx
      rcases Set.mem_iUnion₂.1 (ht hx) with ⟨y, hyt, hxy⟩
      exact Set.mem_iUnion₂.2 ⟨K y, Finset.mem_image.2 ⟨y, hyt, rfl⟩, hxy⟩
    · intro x hx
      rcases Set.mem_iUnion₂.1 hx with ⟨W, hWs, hxW⟩
      rcases Finset.mem_image.1 hWs with ⟨y, _, rfl⟩
      exact (hKsub y hxW).1
  -- Recover the original cover index for each compact-open piece from the chosen witnesses.
  have hsubordinate : ∀ W ∈ s, ∃ i, (W : Set X) ⊆ V i := by
    intro W hWs
    rcases Finset.mem_image.1 hWs with ⟨y, _, rfl⟩
    exact ⟨idx y, fun x hx ↦ (hKsub y hx).2⟩
  exact ⟨s, hcover, hsubordinate⟩
