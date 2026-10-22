/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Topology/MetricSpace/IndexedSeparation.lean
-/

module

public import ReasLib.Topology.MetricSpace.InfDistUnionRange

public section

universe u v

namespace Metric

/-- Pointwise, index-dependent lower bounds to a background set and an indexed family give the
same lower bound for every corresponding punctured union infimum. -/
theorem le_infDist_union_range_diff_singleton_of_indexed_bound
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    {Γ : Set X} {x : ι → X} {b : ι → ℝ}
    (hΓ : Γ.Nonempty) (hnotmem : ∀ i, x i ∉ Γ)
    (hbackground : ∀ i y, y ∈ Γ → b i ≤ dist (x i) y)
    (hfamily : ∀ i j, i ≠ j → b i ≤ dist (x i) (x j)) :
    ∀ i, b i ≤ infDist (x i) ((Γ ∪ Set.range x) \ {x i}) := by
  intro i
  apply le_infDist_union_range_diff_singleton_of_not_mem hΓ (hnotmem i)
  · intro y hy
    exact hbackground i y hy
  · intro j hji
    exact hfamily i j hji.symm

/-- Positive indexed separation bounds produce positive punctured infimum distances from the
background set together with the indexed family. -/
theorem infDist_pos_union_range_diff_singleton_of_indexed_bound
    {ι : Type u} {X : Type v} [PseudoMetricSpace X]
    {Γ : Set X} {x : ι → X} {b : ι → ℝ}
    (hΓ : Γ.Nonempty) (hnotmem : ∀ i, x i ∉ Γ)
    (hpositive : ∀ i, 0 < b i)
    (hbackground : ∀ i y, y ∈ Γ → b i ≤ dist (x i) y)
    (hfamily : ∀ i j, i ≠ j → b i ≤ dist (x i) (x j)) :
    ∀ i, 0 < infDist (x i) ((Γ ∪ Set.range x) \ {x i}) := by
  intro i
  exact lt_of_lt_of_le (hpositive i)
    (le_infDist_union_range_diff_singleton_of_indexed_bound hΓ hnotmem hbackground hfamily i)

end Metric
