module

public import Mathlib.Topology.JacobsonSpace

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T0Space X]

/-
Domain-style sampling for closed points in compact `T0` spaces:
- owner set: `closedPoints X`
- canonical membership API: `mem_closedPoints_iff`
- subset compactness owner: `isCompact_of_finite_subcover`
- closed-point existence in nonempty closed sets: `IsClosed.exists_closed_singleton`

Layer triage:
- `source-facing`: compactness of the closed-point subset in a quasi-compact Kolmogorov space
- `core/canonical`: the owner set `closedPoints X` together with the subset compactness predicate
  `IsCompact`
- `bridge/view`: an open cover of `closedPoints X` covers all of `X`, because any nonempty closed
  complement would contain a closed point

Primitive data is only the owner set `closedPoints X`; compactness is derived through the canonical
finite-subcover interface, so this file should not introduce any parallel wrapper around closed
points or compactness.
-/

-- Proof sketch: if an open cover of `closedPoints X` failed to cover `X`, its closed complement
-- `Z` would be nonempty. Applying `IsClosed.exists_closed_singleton` to `Z` produces a closed
-- point of `X` lying in `Z`, contradicting the cover hypothesis. Thus the same opens cover all of
-- `X`, and compactness of `X` yields a finite subcover.
/-- Lemma 5.12.9: in a quasi-compact Kolmogorov space, the subset `closedPoints X` of closed
points is compact. -/
theorem isCompact_closedPoints : IsCompact (closedPoints X) := by
  refine isCompact_of_finite_subcover fun U hU hcover ↦ ?_
  -- First extend an open cover of `closedPoints X` to an open cover of all of `X`.
  have hXcover : (univ : Set X) ⊆ ⋃ i, U i := by
    by_contra hXcover
    rw [not_subset] at hXcover
    obtain ⟨x, -, hx⟩ := hXcover
    -- A point outside the union lies in the closed complement, which contains a closed point.
    obtain ⟨y, hy, hyclosed⟩ :=
      (isOpen_iUnion hU).isClosed_compl.exists_closed_singleton ⟨x, hx⟩
    -- That closed point belongs to `closedPoints X`, so the cover hypothesis forces it back
    -- into the union, contradicting membership in the complement.
    exact hy (hcover <| mem_closedPoints_iff.2 hyclosed)
  -- Compactness of `X` now gives a finite subcover, and restricting it preserves coverage of
  -- `closedPoints X`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hXcover
  exact ⟨t, (subset_univ _).trans ht⟩

end
