/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Theorem_1_49

open Filter
open scoped Topology

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

-- Proof sketch: in finite dimension, the closure of a bounded set is compact. The cluster-point
-- set is closed, hence compact inside that closure, and `Theorem_1_49` gives connectedness from
-- the vanishing successive increments.
/-- Lemma 2.53: for a bounded sequence in a finite-dimensional Hilbert space whose successive
increments converge to `0`, the set of its cluster points, expressed via the canonical filter-based
notion `MapClusterPt`, is compact and connected. -/
theorem sequenceClusterPointSet_isCompact_isConnected (x : ℕ → 𝓗)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (fun n ↦ x n - x (n + 1)) atTop (𝓝 0)) :
    IsCompact {y | MapClusterPt y atTop x} ∧ IsConnected {y | MapClusterPt y atTop x} := by
  let K : Set 𝓗 := closure (Set.range x)
  haveI : ProperSpace 𝓗 := FiniteDimensional.proper ℝ 𝓗
  have hKcompact : IsCompact K := by
    simpa [K] using hbounded.isCompact_closure
  have hseq_in_K : ∀ n, x n ∈ K := fun n ↦ subset_closure ⟨n, rfl⟩
  have hclosed : IsClosed {y | MapClusterPt y atTop x} := by
    simpa [MapClusterPt] using
      (isClosed_setOf_clusterPt : IsClosed {y | ClusterPt y (map x atTop)})
  have hsubset : {y | MapClusterPt y atTop x} ⊆ K := by
    intro y hy
    exact IsClosed.mem_of_mapClusterPt isClosed_closure hy
      (Filter.Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩)
  have hcompact : IsCompact {y | MapClusterPt y atTop x} :=
    hKcompact.of_isClosed_subset hclosed hsubset
  have hconnected : IsConnected {y | MapClusterPt y atTop x} := by
    refine isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero hKcompact hseq_in_K ?_
    simpa [dist_eq_norm] using hstep.norm
  exact ⟨hcompact, hconnected⟩
