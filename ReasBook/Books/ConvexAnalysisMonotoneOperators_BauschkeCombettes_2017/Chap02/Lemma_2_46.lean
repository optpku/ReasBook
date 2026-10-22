/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_45

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology Pointwise

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- A weakly convergent sequence has no weak sequential cluster point other than its weak limit. -/
private lemma weak_cluster_point_eq_of_tendsto
    {x : ℕ → 𝓗} {y z : 𝓗}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 y)))
    (hz : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 z)) :
    z = y := by
  rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
  -- A strictly increasing subsequence of a convergent sequence has the same weak limit.
  have hφy :
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x (φ n))) atTop (𝓝 (toWeakSpace ℝ 𝓗 y)) := by
    simpa [Function.comp] using hy.comp hφ.tendsto_atTop
  -- Hausdorffness of the weak topology identifies the two subsequential limits.
  have hEq : toWeakSpace ℝ 𝓗 z = toWeakSpace ℝ 𝓗 y :=
    tendsto_nhds_unique hφz hφy
  exact (toWeakSpace ℝ 𝓗).injective hEq

variable [CompleteSpace 𝓗]

/-- Helper for Lemma 2.46: weak convergence of a sequence in a real Hilbert space forces its range
to be norm-bounded. -/
lemma bounded_range_of_tendsto_weakly
    {x : ℕ → 𝓗} {y : 𝓗}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 y))) :
    Bornology.IsBounded (Set.range x) := by
  let T : ℕ → 𝓗 →L[ℝ] ℝ := fun n ↦ InnerProductSpace.toDual ℝ 𝓗 (x n)
  have hpointwise : ∀ u : 𝓗, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    -- Weak convergence gives convergence of each scalar inner-product coordinate.
    have hu_tendsto :
        Tendsto (fun n ↦ inner ℝ (x n) u) atTop (𝓝 (inner ℝ y u)) := by
      simpa using
        (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ 𝓗 y) |>.comp hy
    have hu_bounded :
        Bornology.IsBounded (Set.range fun n ↦ inner ℝ (x n) u) :=
      Metric.isBounded_range_of_tendsto _ hu_tendsto
    rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    have hCn : ‖inner ℝ (x n) u‖ ≤ C := hC _ (Set.mem_range_self n)
    simpa [T, InnerProductSpace.toDual_apply_apply] using hCn
  -- Banach-Steinhaus upgrades the pointwise bounds to a uniform norm bound.
  obtain ⟨C, hC⟩ := uniform_boundedness_principle hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro z ⟨n, rfl⟩
  have hTn : ‖T n‖ ≤ C := hC n
  change ‖InnerProductSpace.toDual ℝ 𝓗 (x n)‖ ≤ C at hTn
  rw [(InnerProductSpace.toDual ℝ 𝓗).norm_map] at hTn
  exact hTn

/-- A bounded sequence in a real Hilbert space lies in a weakly sequentially compact ambient set. -/
private lemma weak_seq_compact_ambient_of_bounded_range
    {x : ℕ → 𝓗} (hx : Bornology.IsBounded (Set.range x)) :
    ∃ C : Set (WeakSpace ℝ 𝓗), IsSeqCompact C ∧
      ∀ n, toWeakSpace ℝ 𝓗 (x n) ∈ C := by
  obtain ⟨r, hsubset⟩ := hx.subset_closedBall (0 : 𝓗)
  let C : Set (WeakSpace ℝ 𝓗) := (toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r
  have hC : IsSeqCompact C := by
    simpa [C] using weak_image_closedBall_zero_isSeqCompact r
  have hx_mem : ∀ n, toWeakSpace ℝ 𝓗 (x n) ∈ C := by
    intro n
    exact ⟨x n, hsubset (Set.mem_range_self n), rfl⟩
  exact ⟨C, hC, hx_mem⟩

/-- Lemma 2.46: a sequence in a real Hilbert space converges weakly if and only if its range is
norm-bounded and it has at most one weak sequential cluster point. The weak convergence and weak
cluster-point conditions are expressed in the canonical weak topology `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: if `x` converges weakly to `y`, every weakly convergent subsequence has the same
-- weak limit by Hausdorffness of `WeakSpace ℝ 𝓗`, and boundedness follows from pointwise bounded
-- inner-product functionals via uniform boundedness. Conversely, boundedness places the range of
-- `x` inside a weakly sequentially compact set, so existence of a weak sequential cluster point
-- follows from weak compactness and Eberlein-Smulian; uniqueness of that cluster point then yields
-- weak convergence of the whole sequence by the Hausdorff sequential-compactness criterion.
theorem weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint
    (x : ℕ → 𝓗) :
    (∃ y : 𝓗, Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 y))) ↔
      Bornology.IsBounded (Set.range x) ∧
        ∀ y z : 𝓗,
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 y) →
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 z) →
          y = z := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨bounded_range_of_tendsto_weakly hy, ?_⟩
    intro z w hz hw
    -- Every weak cluster point must agree with the weak limit of the full sequence.
    calc
      z = y := weak_cluster_point_eq_of_tendsto hy hz
      _ = w := (weak_cluster_point_eq_of_tendsto hy hw).symm
  · rintro ⟨hx_bounded, hx_unique⟩
    rcases weak_seq_compact_ambient_of_bounded_range hx_bounded with ⟨C, hC, hxC⟩
    rcases bounded_sequence_has_weakly_convergent_subsequence x hx_bounded with
      ⟨y, φ, hφ, hφ_tendsto⟩
    have hy_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 y) :=
      ⟨φ, hφ, hφ_tendsto⟩
    refine ⟨y, ?_⟩
    -- Lemma 1.35 turns uniqueness of weak-space sequential cluster points into convergence.
    refine tendsto_of_unique_sequential_cluster_point hC hxC ?_
    intro w hw
    -- Translate a weak-space cluster point back to the original Hilbert space.
    have hw_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n))
          (toWeakSpace ℝ 𝓗 ((toWeakSpace ℝ 𝓗).symm w)) := by
      rcases hw.exists_subseq_tendsto with ⟨ψ, hψ, hψ_tendsto⟩
      exact ⟨ψ, hψ, by simpa [Function.comp] using hψ_tendsto⟩
    have hw_eq : (toWeakSpace ℝ 𝓗).symm w = y :=
      hx_unique _ _ hw_cluster hy_cluster
    simpa using congrArg (toWeakSpace ℝ 𝓗) hw_eq
