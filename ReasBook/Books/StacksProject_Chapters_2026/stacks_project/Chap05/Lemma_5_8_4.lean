module

public import Mathlib.Topology.Irreducible
import Mathlib.SetTheory.ZFC.PSet

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.8.4:
- primary domain: irreducible components of a topological space
- inspected owner declarations:
  `irreducibleComponents`,
  `irreducibleComponents_eq_maximals_closed`,
  `isIrreducible_iff_sUnion_isClosed`,
  `mem_of_subset_sUnion_irreducibleComponents`
- best owner abstraction: `irreducibleComponents X` is the core/canonical owner; the present lemma
  is a `bridge/view` statement identifying a finite irredundant closed irreducible cover with that
  canonical set of components
- primitive-vs-derived split: the primitive data here are the finite family `S`, the cover
  equality, and the closedness/irreducibility/irredundancy hypotheses on its members; membership in
  `irreducibleComponents X` is derived from the owner maximality and finite-cover membership API
  rather than from a local duplicate notion of component
-/

/-- Helper for Lemma 5.8.4: an irreducible component in a finite closed irreducible cover must be
one of the covering members. -/
lemma irreducible_component_mem_cover
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    {Y : Set X} (hY : Y ∈ irreducibleComponents X) :
    Y ∈ S := by
  classical
  -- Rewrite component membership into the maximal closed-irreducible formulation.
  rw [irreducibleComponents_eq_maximals_closed] at hY
  change Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) Y at hY
  -- Irreducibility of `Y` forces it to lie in one closed member of the finite cover.
  obtain ⟨W, hW, hYW⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hY.1.2 hS.toFinset
      (fun W hW ↦ hclosed W (hS.mem_toFinset.mp hW))
      (by simp [hcover])
  have hWS : W ∈ S := hS.mem_toFinset.mp hW
  -- Maximality of the irreducible component upgrades inclusion to equality.
  have hWY : W ⊆ Y := hY.2 ⟨hclosed W hWS, hirr W hWS⟩ hYW
  have hYW_eq : Y = W := Subset.antisymm hYW hWY
  simpa [hYW_eq] using hWS

/-- Helper for Lemma 5.8.4: irredundancy forces one cover member contained in another to be equal
to it. -/
lemma subset_eq_of_irredundant_members
    (S : Set (Set X))
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z}))
    {Z W : Set X} (hZ : Z ∈ S) (hW : W ∈ S) (hZW : Z ⊆ W) :
    Z = W := by
  -- If `W ≠ Z`, then every point of `Z` already lies in the union of the other members.
  by_contra hne
  have hZsubset : Z ⊆ ⋃₀ (S \ {Z}) := by
    intro x hx
    refine mem_sUnion.2 ?_
    exact ⟨W, ⟨hW, by simpa [Set.mem_singleton_iff, eq_comm] using hne⟩, hZW hx⟩
  exact hirredundant Z hZ hZsubset

/-- Helper for Lemma 5.8.4: each member of the finite irredundant closed irreducible cover is an
irreducible component. -/
lemma cover_member_mem_irreducibleComponents
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z}))
    {Z : Set X} (hZ : Z ∈ S) :
    Z ∈ irreducibleComponents X := by
  -- Place `Z` inside an irreducible component, following Lemma 5.8.3's route.
  obtain ⟨Y, hY, hZY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible Z (hirr Z hZ)
  have hYS : Y ∈ S := irreducible_component_mem_cover S hS hcover hclosed hirr hY
  -- Irredundancy identifies that component with the original cover member.
  have hZY_eq : Z = Y := subset_eq_of_irredundant_members S hirredundant hZ hYS hZY
  simpa [hZY_eq] using hY

/-- Lemma 5.8.4: if a topological space is covered by finitely many irreducible closed subsets and
none of them is contained in the union of the others, then the irreducible components are exactly
those subsets. A finite family of closed irreducible subsets is represented canonically by a
finite set `S : Set (Set X)`, and the conclusion is equality with `irreducibleComponents X`. -/
theorem irreducibleComponents_eq_of_finite_irreducible_closed_cover
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirr : ∀ Z ∈ S, IsIrreducible Z)
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z})) :
    irreducibleComponents X = S := by
  classical
  -- Follow the source proof: first show every component belongs to the cover.
  refine Set.Subset.antisymm ?_ ?_
  · intro Y hY
    exact irreducible_component_mem_cover S hS hcover hclosed hirr hY
  · intro Z hZ
    -- Then show each cover member is itself a component by placing it inside one.
    exact cover_member_mem_irreducibleComponents S hS hcover hclosed hirr hirredundant hZ
