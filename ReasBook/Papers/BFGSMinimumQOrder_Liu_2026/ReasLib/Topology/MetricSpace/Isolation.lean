module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

noncomputable section

universe u v

namespace Metric

/-- The distance from `x` to the other points of `E`. -/
def isolationDistance {X : Type u} [MetricSpace X] (E : Set X) (x : X) : ℝ :=
  infDist x (E \ {x})

/-- The isolation distance is the infimum distance to the punctured set. -/
theorem isolationDistance_eq {X : Type u} [MetricSpace X] (E : Set X) (x : X) :
    isolationDistance E x = infDist x (E \ {x}) := by
  rfl

/-- Isolation distance is nonnegative. -/
theorem isolationDistance_nonneg {X : Type u} [MetricSpace X]
    (E : Set X) (x : X) :
    0 ≤ isolationDistance E x := by
  rw [isolationDistance_eq]
  exact infDist_nonneg

/-- One quarter of the distance from `x` to the other points of `E`.  Closed
balls of this radius around distinct members of `E` are pairwise disjoint. -/
def isolationRadius {X : Type u} [MetricSpace X] (E : Set X) (x : X) : ℝ :=
  isolationDistance E x / 4

/-- The isolation radius is one quarter of the punctured-set distance. -/
theorem isolationRadius_eq {X : Type u} [MetricSpace X] (E : Set X) (x : X) :
    isolationRadius E x = infDist x (E \ {x}) / 4 := by
  rfl

/-- Isolation radius is nonnegative. -/
theorem isolationRadius_nonneg {X : Type u} [MetricSpace X]
    (E : Set X) (x : X) :
    0 ≤ isolationRadius E x := by
  have hfour : (0 : ℝ) ≤ 4 := by
    norm_num
  rw [isolationRadius]
  exact div_nonneg (isolationDistance_nonneg E x) hfour

/-- When the isolation distance is positive, its quarter-radius is strictly
smaller. -/
theorem isolationRadius_lt_isolationDistance {X : Type u} [MetricSpace X]
    (E : Set X) (x : X) (hpos : 0 < isolationDistance E x) :
    isolationRadius E x < isolationDistance E x := by
  rw [isolationRadius]
  linarith

/-- Points in subsets of distinct quarter-isolation closed balls are separated by at least
half the distance between the centers. -/
theorem half_dist_le_of_mem_isolationClosedBall {ι : Type u} {X : Type v} [MetricSpace X]
    (E : Set X) (x : ι → X) (hx : ∀ k, x k ∈ E) (hinj : Function.Injective x)
    (s : ι → Set X)
    (hs : ∀ k, s k ⊆ closedBall (x k) (isolationRadius E (x k)))
    {i j : ι} (hij : i ≠ j) {y z : X} (hy : y ∈ s i) (hz : z ∈ s j) :
    dist (x i) (x j) / 2 ≤ dist y z := by
  -- Distinctness puts each center in the punctured set belonging to the other center.
  have hxj : x j ∈ E \ {x i} := by
    refine ⟨hx j, ?_⟩
    simpa only [Set.mem_singleton_iff] using (hinj.ne hij).symm
  have hxi : x i ∈ E \ {x j} := by
    refine ⟨hx i, ?_⟩
    simpa only [Set.mem_singleton_iff] using hinj.ne hij
  have hri : infDist (x i) (E \ {x i}) ≤ dist (x i) (x j) :=
    infDist_le_dist_of_mem hxj
  have hrj : infDist (x j) (E \ {x j}) ≤ dist (x i) (x j) := by
    rw [dist_comm]
    exact infDist_le_dist_of_mem hxi
  -- Ball membership bounds the two outer legs of the four-point triangle inequality.
  have hyi : dist (x i) y ≤ infDist (x i) (E \ {x i}) / 4 :=
    (by simpa only [isolationRadius_eq] using mem_closedBall'.mp (hs i hy))
  have hzj : dist z (x j) ≤ infDist (x j) (E \ {x j}) / 4 :=
    (by simpa only [isolationRadius_eq] using mem_closedBall.mp (hs j hz))
  have htriangle := dist_triangle4 (x i) y z (x j)
  -- The two quarter-radius contributions leave half the center distance between the sets.
  linarith

/-- The quarter-isolation closed balls centered at distinct members of a set are pairwise
disjoint. -/
theorem pairwiseDisjoint_isolationClosedBall {ι : Type u} {X : Type v} [MetricSpace X]
    (E : Set X) (x : ι → X) (hx : ∀ k, x k ∈ E) (hinj : Function.Injective x) :
    Set.univ.PairwiseDisjoint
      (fun k ↦ closedBall (x k) (isolationRadius E (x k))) := by
  -- Reduce pairwise disjointness to excluding a common point of two distinct balls.
  intro i _ j _ hij
  refine Set.disjoint_left.mpr ?_
  intro y hy hz
  have hseparated := half_dist_le_of_mem_isolationClosedBall E x hx hinj
    (fun k ↦ closedBall (x k) (isolationRadius E (x k)))
    (fun _ ↦ Set.Subset.rfl) hij hy hz
  have hcenters : 0 < dist (x i) (x j) := dist_pos.mpr (hinj.ne hij)
  -- Applying quantitative separation twice at the common point contradicts distinct centers.
  rw [dist_self] at hseparated
  linarith

/-- A quarter-isolation closed ball in a closed set is disjoint from the set's derived set
when the isolation distance is positive. -/
theorem isolationClosedBall_disjoint_derivedSet {X : Type v} [MetricSpace X]
    (E : Set X) (x : X) (hE : IsClosed E) (hpos : 0 < isolationDistance E x) :
    Disjoint (closedBall x (isolationRadius E x)) (derivedSet E) := by
  -- Every derived point lies in the closure of the punctured set, including the center itself.
  have hderived : derivedSet E ⊆ closure (E \ {x}) := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      exact mem_closure_iff_clusterPt.mpr
        (accPt_principal_iff_clusterPt.mp (mem_derivedSet.mp hy))
    · apply subset_closure
      refine ⟨(isClosed_iff_derivedSet_subset E).mp hE hy, ?_⟩
      simpa only [Set.mem_singleton_iff] using hyx
  have hpos' : 0 < infDist x (E \ {x}) := by
    simpa only [isolationDistance_eq] using hpos
  have hradius : infDist x (E \ {x}) / 4 < infDist x (E \ {x}) := by
    linarith
  -- The full isolation distance is unchanged by closure, so the quarter ball misses that closure.
  have hdisjoint :
      Disjoint (closedBall x (isolationRadius E x)) (closure (E \ {x})) := by
    apply disjoint_closedBall_of_lt_infDist
    rw [isolationRadius_eq, infDist_closure]
    exact hradius
  -- Restricting the right-hand set gives disjointness from the derived set itself.
  exact Disjoint.mono_right hderived hdisjoint

end Metric
