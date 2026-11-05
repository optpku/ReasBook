module
public import Mathlib.Topology.Bases

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u

section

variable {X : Type u}

/-
Domain-style sampling for generated topologies from basis data:
- owner abstraction: `TopologicalSpace.IsTopologicalBasis`
- same-domain declarations inspected:
  `TopologicalSpace.IsTopologicalBasis`,
  `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`,
  `TopologicalSpace.IsTopologicalBasis.exists_subset_inter`,
  `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`,
  `Definition_5_5_1`

Layer triage:
- `source-facing`: a family covering `X` and admitting local intersection refinements generates a
  topology for which it is a basis
- `core/canonical`: `TopologicalSpace.IsTopologicalBasis`
- `bridge/view`: the generated-topology basis construction and the ensuing uniqueness statement

Primitive data is exactly the owner fields `exists_subset_inter`, `sUnion_eq`, and
`eq_generateFrom`. The existence-and-uniqueness theorem is derived API from `eq_generateFrom`, so
this file should construct the canonical owner directly rather than introducing a parallel local
predicate or a large specification theorem.
-/

-- Proof sketch: the hypotheses are exactly the non-topological fields of
-- `TopologicalSpace.IsTopologicalBasis`, and the remaining field is witnessed by the generated
-- topology `generateFrom B`.
/-- Lemma 5.5.2: if `B` covers `X` and is stable under basis refinement of pairwise
intersections, then `B` is a topological basis for the generated topology `generateFrom B`. -/
theorem isTopologicalBasis_generateFrom (B : Set (Set X)) (hcover : sUnion B = univ)
    (hinter :
      ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ B → ∀ ⦃V : Set X⦄, V ∈ B →
        x ∈ U ∩ V → ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V)
    : let _ : TopologicalSpace X := generateFrom B
      IsTopologicalBasis B := by
  let _ : TopologicalSpace X := generateFrom B
  refine ⟨fun U hU V hV x hx ↦ hinter hU hV hx, hcover, rfl⟩

-- Proof sketch: existence is provided by `generateFrom B`, and uniqueness follows from the
-- `eq_generateFrom` field of a topological basis.
/-- Lemma 5.5.2, existence-and-uniqueness form: there exists a unique topology on `X` for which `B`
is a topological basis. -/
theorem existsUnique_topology_with_basis (B : Set (Set X)) (hcover : sUnion B = univ)
    (hinter :
      ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ B → ∀ ⦃V : Set X⦄, V ∈ B →
        x ∈ U ∩ V → ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V)
    : ∃! t : TopologicalSpace X, let _ : TopologicalSpace X := t
      IsTopologicalBasis B := by
  refine ⟨generateFrom B, isTopologicalBasis_generateFrom B hcover hinter, ?_⟩
  intro t ht
  simpa using ht.eq_generateFrom

end
