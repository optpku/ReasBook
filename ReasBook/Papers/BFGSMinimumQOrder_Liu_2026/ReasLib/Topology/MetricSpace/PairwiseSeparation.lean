module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

universe u v

namespace Metric

/-- A positive pointwise lower bound on distances between distinct images makes
the indexed family injective. -/
theorem injective_of_pos_le_dist
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    (f : ι → X) (lower : ι → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hsep : ∀ i j, i ≠ j → lower i ≤ dist (f i) (f j)) :
    Function.Injective f := by
  intro i j hij
  by_contra hne
  have hbound := hsep i j hne
  rw [hij, dist_self] at hbound
  exact (not_le_of_gt (hlower i)) hbound

/-- A pointwise distance lower bound on a punctured set gives the same lower bound for its
infimum distance from the distinguished point. -/
theorem le_infDist_diff_singleton_of_pointwise_lower_bound
    {X : Type u} [PseudoMetricSpace X] {E : Set X} {x : X} {r : ℝ}
    (hnonempty : (E \ {x}).Nonempty)
    (hbound : ∀ y ∈ E, y ≠ x → r ≤ dist x y) :
    r ≤ infDist x (E \ {x}) := by
  refine (le_infDist hnonempty).mpr ?_
  intro y hy
  have hyne : y ≠ x := by
    intro hyx
    apply hy.2
    exact Set.mem_singleton_iff.mpr hyx
  exact hbound y hy.1 hyne

/-- A strictly positive pointwise separation certificate gives a strictly positive punctured
infimum distance from the distinguished point. -/
theorem infDist_pos_of_pointwise_lower_bound
    {X : Type u} [PseudoMetricSpace X] {E : Set X} {x : X} {r : ℝ}
    (hr : 0 < r) (hnonempty : (E \ {x}).Nonempty)
    (hbound : ∀ y ∈ E, y ≠ x → r ≤ dist x y) :
    0 < infDist x (E \ {x}) := by
  exact lt_of_lt_of_le hr (le_infDist_diff_singleton_of_pointwise_lower_bound hnonempty hbound)

/-- A pointwise distance lower bound separates every strictly smaller closed ball from the
punctured set carrying that bound. -/
theorem disjoint_closedBall_of_pointwise_lower_bound
    {X : Type u} [PseudoMetricSpace X] {E : Set X} {x : X} {r s : ℝ}
    (hrs : s < r)
    (hbound : ∀ y ∈ E, y ≠ x → r ≤ dist x y) :
    Disjoint (closedBall x s) (E \ {x}) := by
  refine Set.disjoint_left.mpr ?_
  intro y hyBall hySet
  have hyDist : dist x y ≤ s := mem_closedBall'.mp hyBall
  have hyNe : y ≠ x := by
    intro hyx
    exact hySet.2 (Set.mem_singleton_iff.mpr hyx)
  have hyLower : r ≤ dist x y := hbound y hySet.1 hyNe
  linarith

/-- Closed balls with radii whose pairwise sums are strictly below the corresponding center
distances form a pairwise-disjoint family. -/
theorem pairwiseDisjoint_closedBall_of_radius_add_lt_dist
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    (x : ι → X) (r : ι → ℝ)
    (hsep : ∀ ⦃i j : ι⦄, i ≠ j → r i + r j < dist (x i) (x j)) :
    Set.univ.PairwiseDisjoint (fun i ↦ closedBall (x i) (r i)) := by
  intro i _ j _ hij
  exact closedBall_disjoint_closedBall (hsep hij)

end Metric
