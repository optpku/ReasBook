/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {α : Type u} [PseudoMetricSpace α]

/- Theorem 8.16 is `source-facing`: it is about convergence of a sequence under the Chapter 8
Fejér-monotonicity condition, while the canonical mathlib notion for a "limit point of a
sequence" is `MapClusterPt _ atTop x`. The source proof uses an already existing limit point, so
that hidden dependency is made explicit rather than being buried in a surrogate boundedness
package. -/

-- Proof sketch: choose a sequential cluster point `y` of `x`; the subset hypothesis puts `y` in
-- `S`, so Fejér monotonicity makes `n ↦ dist (x n) y` antitone. Extract a subsequence converging to
-- `y` from the cluster-point hypothesis; along that subsequence the distance to `y` tends to `0`.
-- An antitone nonnegative real sequence with a subsequence tending to `0` must itself tend to `0`,
-- hence `x` tends to `y`.
/-- Helper for Theorem 8.16: fixing a point of `S` turns the Fejér inequalities into an antitone
distance profile. -/
lemma dist_antitone_of_fejer_point
    {x : ℕ → α} {S : Set α} {y : α}
    (hFejer : ∀ z ∈ S, ∀ k : ℕ, dist (x (k + 1)) z ≤ dist (x k) z)
    (hyS : y ∈ S) :
    Antitone (fun k ↦ dist (x k) y) := by
  -- For the chosen point `y ∈ S`, the displayed Fejér inequality is exactly the successor-step
  -- hypothesis needed to obtain an antitone sequence on `ℕ`.
  refine antitone_nat_of_succ_le ?_
  intro k
  exact hFejer y hyS k

/-- Helper for Theorem 8.16: a sequential cluster point yields a subsequence whose distances to
that point converge to zero. -/
lemma subseq_dist_tendsto_zero_of_mapClusterPt
    {x : ℕ → α} {y : α}
    (hy : MapClusterPt y Filter.atTop x) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun n ↦ dist (x (ψ n)) y) Filter.atTop (nhds 0) := by
  -- A sequential cluster point produces a strictly monotone extraction converging to `y`.
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hy
  refine ⟨ψ, hψmono, ?_⟩
  -- Rewriting that subsequence convergence in metric form gives the required distance limit.
  rw [show (fun n ↦ dist (x (ψ n)) y) = (fun n ↦ dist ((x ∘ ψ) n) y) by
    rfl]
  exact (tendsto_iff_dist_tendsto_zero).mp hψtendsto

/-- Helper for Theorem 8.16: if the distance profile is antitone and one subsequence of distances
converges to zero, then the whole sequence converges to the same point. -/
lemma tendsto_of_antitone_dist_subseq_tendsto_zero
    {x : ℕ → α} {y : α}
    (hAnti : Antitone (fun k ↦ dist (x k) y))
    (hSubseq : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun n ↦ dist (x (ψ n)) y) Filter.atTop (nhds 0)) :
    Filter.Tendsto x Filter.atTop (nhds y) := by
  obtain ⟨ψ, hψmono, hψdist⟩ := hSubseq
  have hdist : Filter.Tendsto (fun k ↦ dist (x k) y) Filter.atTop (nhds 0) := by
    -- The monotone convergence criterion upgrades the subsequential distance limit to a full one.
    exact (tendsto_iff_tendsto_subseq_of_antitone hAnti hψmono.tendsto_atTop).2 hψdist
  -- In a pseudometric space, convergence is equivalent to the distance to the limit tending to
  -- zero.
  exact (tendsto_iff_dist_tendsto_zero).2 hdist

/-- Theorem 8.16: if a sequence is Fejér monotone with respect to a set `S`, every sequential
limit point of the sequence belongs to `S`, and the sequence has at least one sequential limit
point, then the whole sequence converges to one of its sequential limit points. -/
theorem tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo
    {x : ℕ → α} {S : Set α}
    (hFejer : ∀ y ∈ S, ∀ k : ℕ, dist (x (k + 1)) y ≤ dist (x k) y)
    (hlimitPoints_subset : {y : α | MapClusterPt y Filter.atTop x} ⊆ S)
    (hlimitPoint : ∃ y : α, MapClusterPt y Filter.atTop x) :
    ∃ y : α, MapClusterPt y Filter.atTop x ∧ Filter.Tendsto x Filter.atTop (nhds y) := by
  obtain ⟨y, hyCluster⟩ := hlimitPoint
  have hyS : y ∈ S := hlimitPoints_subset hyCluster
  -- The source proof fixes a cluster point `y`. Since `y ∈ S`, Fejér monotonicity makes the
  -- distance profile to `y` nonincreasing along the entire sequence.
  have hAnti : Antitone (fun k ↦ dist (x k) y) :=
    dist_antitone_of_fejer_point hFejer hyS
  have hSubseq : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun n ↦ dist (x (ψ n)) y) Filter.atTop (nhds 0) :=
    subseq_dist_tendsto_zero_of_mapClusterPt hyCluster
  -- The chosen cluster point is reached by a subsequence, and antitonicity upgrades that
  -- subsequential distance limit to full convergence of the original sequence.
  refine ⟨y, hyCluster, ?_⟩
  exact tendsto_of_antitone_dist_subseq_tendsto_zero hAnti hSubseq

end
