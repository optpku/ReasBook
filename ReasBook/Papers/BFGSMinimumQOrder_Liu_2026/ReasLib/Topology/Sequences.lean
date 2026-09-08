module

public import Mathlib.Topology.Sequences

public section

open Filter

universe u

/-- A point lies in the closure of a sequence's range exactly when it is attained or is an
`atTop` cluster point of the sequence. -/
lemma mem_closure_range_iff_mem_or_mapClusterPt {X : Type u} [TopologicalSpace X] [T1Space X]
    {x : ℕ → X} {y : X} :
    y ∈ closure (Set.range x) ↔ y ∈ Set.range x ∨ MapClusterPt y atTop x := by
  classical
  constructor
  · intro hy
    by_cases hyrange : y ∈ Set.range x
    · exact Or.inl hyrange
    · right
      rw [mapClusterPt_iff_frequently]
      intro s hs
      rw [frequently_atTop]
      intro N
      -- Remove the closed finite prefix so that a closure witness has index at least `N`.
      have hprefix_closed : IsClosed (x '' Set.Iio N) :=
        ((Set.finite_Iio N).image x).isClosed
      have hy_prefix : y ∉ x '' Set.Iio N := by
        intro hy_prefix
        rcases hy_prefix with ⟨n, hn, hny⟩
        exact hyrange ⟨n, hny⟩
      have htail_nhds : (x '' Set.Iio N)ᶜ ∈ nhds y :=
        hprefix_closed.isOpen_compl.mem_nhds hy_prefix
      have hs_tail_nhds : s ∩ (x '' Set.Iio N)ᶜ ∈ nhds y := inter_mem hs htail_nhds
      rcases (mem_closure_iff_nhds.mp hy) _ hs_tail_nhds with ⟨z, hz_tail, hz_range⟩
      rcases hz_range with ⟨n, rfl⟩
      refine ⟨n, ?_, hz_tail.1⟩
      exact Nat.le_of_not_lt fun hn ↦ hz_tail.2 ⟨n, hn, rfl⟩
  · rintro (hyrange | hcluster)
    · exact subset_closure hyrange
    · rw [mem_closure_iff_nhds]
      intro s hs
      -- A frequently occurring neighborhood hit supplies a point of the range in the neighborhood.
      rcases ((mapClusterPt_iff_frequently.mp hcluster) s hs).exists with ⟨n, hn⟩
      exact ⟨x n, hn, ⟨n, rfl⟩⟩

namespace IsClosed

/-- A closed set containing every `atTop` cluster point of a sequence remains closed after
adjoining the sequence's range. -/
theorem union_range_of_mapClusterPt {X : Type u} [TopologicalSpace X] [SequentialSpace X]
    [T1Space X] {Γ : Set X} (hΓ : IsClosed Γ) (x : ℕ → X)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) : IsClosed (Γ ∪ Set.range x) := by
  -- It suffices to show that every closure point is already in the enlarged set.
  rw [← closure_subset_iff_isClosed, closure_union, hΓ.closure_eq]
  intro y hy
  rcases hy with hyΓ | hyrange
  · exact Or.inl hyΓ
  · -- The range-closure bridge separates attained values from genuine tail cluster points.
    rcases mem_closure_range_iff_mem_or_mapClusterPt.mp hyrange with hyrange | hycluster
    · exact Or.inr hyrange
    · exact Or.inl (hcluster y hycluster)

end IsClosed
