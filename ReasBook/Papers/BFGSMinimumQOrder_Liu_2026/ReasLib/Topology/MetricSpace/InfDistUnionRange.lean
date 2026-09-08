module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

universe u v

namespace Metric

/-- Pointwise lower bounds to a background set and an indexed family combine into a
lower bound for the distance to their union after removing the distinguished point. -/
theorem le_infDist_union_range_diff_singleton
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    {Γ : Set X} {x : ι → X} {i : ι} {r : ℝ}
    (hnonempty : ((Γ ∪ Set.range x) \ {x i}).Nonempty)
    (hbackground : ∀ y ∈ Γ, y ≠ x i → r ≤ dist (x i) y)
    (hfamily : ∀ j, j ≠ i → r ≤ dist (x i) (x j)) :
    r ≤ infDist (x i) ((Γ ∪ Set.range x) \ {x i}) := by
  refine (le_infDist hnonempty).mpr ?_
  intro y hy
  have hyne : y ≠ x i := by
    intro hyi
    apply hy.2
    exact Set.mem_singleton_iff.mpr hyi
  rcases hy.1 with hyΓ | ⟨j, hj⟩
  · exact hbackground y hyΓ hyne
  · subst y
    apply hfamily j
    intro hji
    subst j
    exact hyne rfl

/-- If the distinguished point is outside a nonempty background set, lower bounds to that
set and to every other indexed point bound the corresponding punctured infimum distance. -/
theorem le_infDist_union_range_diff_singleton_of_not_mem
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    {Γ : Set X} {x : ι → X} {i : ι} {r : ℝ}
    (hΓ : Γ.Nonempty) (hi : x i ∉ Γ)
    (hbackground : ∀ y ∈ Γ, r ≤ dist (x i) y)
    (hfamily : ∀ j, j ≠ i → r ≤ dist (x i) (x j)) :
    r ≤ infDist (x i) ((Γ ∪ Set.range x) \ {x i}) := by
  have hnonempty : ((Γ ∪ Set.range x) \ {x i}).Nonempty := by
    rcases hΓ with ⟨y, hy⟩
    refine ⟨y, Or.inl hy, ?_⟩
    intro hyi
    apply hi
    have hyEq : y = x i := Set.mem_singleton_iff.mp hyi
    rwa [← hyEq]
  apply le_infDist_union_range_diff_singleton hnonempty
  · intro y hy _
    exact hbackground y hy
  · exact hfamily

end Metric
