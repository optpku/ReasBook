module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Connected.Basic
import stacks_project.Chap05.Definition_5_7_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

/- Domain sampling / owner triage for Lemma 5.7.3:
- primary domain: connected subsets and connected components of a topological space
- core/canonical owner: `connectedComponent`
- sampled supporting declarations: `IsConnected.closure`, `isClosed_connectedComponent`,
  `IsConnected.subset_connectedComponent`, `connectedComponent_eq`
- project bridge reused below: `maximal_isConnected_iff_eq_connectedComponent`
- primitive data: the canonical subset `connectedComponent x`
- derived/source-facing API: uniqueness of the connected component containing a connected subset or
  a point, expressed via the chapter bridge `Maximal IsConnected`
-/

/- Lemma 5.7.3 (1): the closure of a connected subset of a topological space is connected.
This is exactly the canonical theorem `IsConnected.closure`. -/
recall IsConnected.closure

/- Lemma 5.7.3 (2): every connected component of a topological space is closed.
This is exactly the canonical theorem `isClosed_connectedComponent`. -/
recall isClosed_connectedComponent

-- Proof sketch: choose `x ∈ T`; then `T ⊆ connectedComponent x` by
-- `IsConnected.subset_connectedComponent`. Any other maximal connected superset is some
-- `connectedComponent y` by `maximal_isConnected_iff_eq_connectedComponent`, and containing `x`
-- forces `connectedComponent y = connectedComponent x` by `connectedComponent_eq`.
/-- Lemma 5.7.3 (1): every connected subset of `X` is contained in a unique connected component of
`X`. -/
theorem existsUnique_connectedComponent_superset_of_isConnected {T : Set X}
    (hT : IsConnected T) :
    ∃! C : Set X, Maximal IsConnected C ∧ T ⊆ C := by
  obtain ⟨x, hx⟩ := hT.nonempty
  refine ⟨connectedComponent x, ?_, ?_⟩
  · exact ⟨(maximal_isConnected_iff_eq_connectedComponent _).2 ⟨x, rfl⟩,
      hT.subset_connectedComponent hx⟩
  · intro C hC
    rcases (maximal_isConnected_iff_eq_connectedComponent C).1 hC.1 with ⟨y, rfl⟩
    exact connectedComponent_eq (hC.2 hx)

-- Proof sketch: apply the previous clause to the singleton `{x}`, which is connected.
/-- Lemma 5.7.3 (2): every point of `X` lies in a unique connected component of `X`, so `X` is the
disjoint union of its connected components. -/
theorem existsUnique_connectedComponent_through_point (x : X) :
    ∃! C : Set X, Maximal IsConnected C ∧ x ∈ C := by
  have hx : IsConnected ({x} : Set X) := isConnected_singleton
  simpa [singleton_subset_iff] using
    existsUnique_connectedComponent_superset_of_isConnected hx
