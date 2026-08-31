module

public import Mathlib.Topology.Sets.Opens

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u v

section

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for basis refinements:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_iUnion`,
  `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion`,
  `Definition_5_5_1`

Layer triage:
- `source-facing`: a refinement statement for an indexed open cover of an open subset
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: the resulting indexed refining family of opens, each carried by a basis member

Primitive data is the basis owner `hB` together with the indexed open family `Ui` covering `U`.
The refining family should therefore be returned directly as basis members `V j ∈ B`, obtained by
applying the owner theorem `hB.open_eq_iUnion` to each member of the cover. The openness of each
`V j` is derived from `hB.isOpen`, so bundling those sets again as `Opens X` would only duplicate
owner data instead of exposing the source-facing refinement.
-/

/-- Helper for Lemma 5.5.3: every member of the given cover is contained in the set being
covered. -/
lemma cover_piece_subset_target
    {ι : Type v} (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∀ i, (Ui i : Set X) ⊆ (U : Set X) := by
  intro i
  -- Rewrite the covering equality so each `Ui i` becomes an explicit branch of the union.
  simpa [hUi] using Set.subset_iUnion (fun j => (Ui j : Set X)) i

/-- Helper for Lemma 5.5.3: every point of `U` lies in a basis member refining one cover
piece. -/
lemma point_has_basis_refining_cover_piece
    {ι : Type v} (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∀ x ∈ (U : Set X), ∃ i, ∃ V : {V : Set X // V ∈ B}, x ∈ (V : Set X) ∧
      (V : Set X) ⊆ (Ui i : Set X) := by
  intro x hx
  -- The cover equality provides a cover piece containing the chosen point.
  have hx' : x ∈ ⋃ i, (Ui i : Set X) := by
    simpa [hUi] using hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx'
  -- The basis axiom now refines that open neighborhood by a basis element.
  obtain ⟨V, hVB, hxV, hVUi⟩ := hB.exists_subset_of_mem_open hxi (Ui i).isOpen
  exact ⟨i, ⟨V, hVB⟩, hxV, hVUi⟩

/-- Helper for Lemma 5.5.3: a family of basis members indexed by points of `U` covers `U` once
each point belongs to its chosen basis member and each basis member refines the original cover. -/
lemma point_indexed_basis_refinement_covers
    {ι : Type v} (B : Set (Set X)) (U : Opens X) (Ui : ι → Opens X)
    (hUi : (U : Set X) = ⋃ i, (Ui i : Set X))
    (V : ULift.{v} U → {V : Set X // V ∈ B})
    (hmem : ∀ j : ULift.{v} U, ((j.down : U) : X) ∈ (V j : Set X))
    (href : ∀ j : ULift.{v} U, ∃ i, (V j : Set X) ⊆ (Ui i : Set X)) :
    (U : Set X) = ⋃ j, (V j : Set X) := by
  ext x
  constructor
  · intro hx
    -- Index the covering family by the point itself to obtain the forward inclusion.
    have hxV : x ∈ (V (ULift.up ⟨x, hx⟩) : Set X) := by
      simpa using hmem (ULift.up ⟨x, hx⟩)
    exact Set.mem_iUnion.mpr ⟨ULift.up ⟨x, hx⟩, hxV⟩
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hVUi⟩ := href j
    -- Refinement into one `Ui i` and the original cover put the point back inside `U`.
    exact cover_piece_subset_target U Ui hUi i (hVUi hxj)

/-- Lemma 5.5.3: every indexed open cover `U = ⋃ i Ui i` admits a refinement by members of the
basis `B`. -/
-- Proof sketch: index the refinement by points of `U`, choose for each point a basis neighborhood
-- refining one member of the cover, and then verify that these chosen basis members still cover `U`.
theorem exists_basis_refinement_of_cover
    {ι : Type v} (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∃ (J : Type (max u v)) (V : J → {V : Set X // V ∈ B}),
      (U : Set X) = ⋃ j, (V j : Set X) ∧ ∀ j, ∃ i, (V j : Set X) ⊆ Ui i := by
  classical
  -- Choose a refining basis member for each point of `U` using the pointwise basis argument.
  have hpoint :
      ∀ j : U, ∃ i, ∃ V : {V : Set X // V ∈ B}, (j : X) ∈ (V : Set X) ∧
        (V : Set X) ⊆ (Ui i : Set X) := by
    intro j
    exact point_has_basis_refining_cover_piece B hB U Ui hUi j j.property
  choose iOf VOf hmem hsub using hpoint
  refine ⟨ULift.{v} U, fun j ↦ VOf j.down, ?_⟩
  constructor
  · -- The chosen basis members cover `U` because each point indexes one of them.
    exact point_indexed_basis_refinement_covers B U Ui hUi (fun j ↦ VOf j.down)
      (fun j ↦ hmem j.down) (fun j ↦ ⟨iOf j.down, hsub j.down⟩)
  · -- The refinement property is exactly the containment chosen at each point.
    intro j
    exact ⟨iOf j.down, hsub j.down⟩

end
