/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_24_Pairwise_disjoint_isolation_balls_from_all_pairs_separation.lean
-/

module

public import ReasLib.Topology.MetricSpace.Isolation

public section

universe u v

/- Infrastructure I.24 (Pairwise-disjoint isolation balls from all-pairs separation) (1):
the quarter-isolation closed balls centered at the indexed points are pairwise disjoint. -/
#check (Metric.pairwiseDisjoint_isolationClosedBall :
  ∀ {ι : Type u} {X : Type v} [MetricSpace X]
    (E : Set X) (x : ι → X) (_hx : ∀ k, x k ∈ E) (_hinj : Function.Injective x),
    Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.closedBall (x k) (Metric.isolationRadius E (x k))))

/- Infrastructure I.24 (Pairwise-disjoint isolation balls from all-pairs separation) (2):
each positive quarter-isolation closed ball in a closed set avoids `derivedSet E`. -/
#check (Metric.isolationClosedBall_disjoint_derivedSet :
  ∀ {X : Type v} [MetricSpace X] (E : Set X) (x : X),
    IsClosed E → 0 < Metric.isolationDistance E x →
      Disjoint (Metric.closedBall x (Metric.isolationRadius E x)) (derivedSet E))

/- Infrastructure I.24 (Pairwise-disjoint isolation balls from all-pairs separation) (3):
points in subsets of distinct isolation balls are separated by half the center distance. -/
#check (Metric.half_dist_le_of_mem_isolationClosedBall :
  ∀ {ι : Type u} {X : Type v} [MetricSpace X]
    (E : Set X) (x : ι → X) (_hx : ∀ k, x k ∈ E) (_hinj : Function.Injective x)
    (s : ι → Set X)
    (_hs : ∀ k, s k ⊆
      Metric.closedBall (x k) (Metric.isolationRadius E (x k)))
    {i j : ι}, i ≠ j → ∀ {y z : X}, y ∈ s i → z ∈ s j →
      dist (x i) (x j) / 2 ≤ dist y z)
