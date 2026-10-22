/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_37

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology
open scoped Pointwise

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- The weak image of a scaled closed unit ball agrees with the scalar multiple of the weak image
of the unit ball. -/
private lemma weak_image_smul_closedBall_eq_smul_weak_image_closedBall (r : ℝ) :
    ((toWeakSpace ℝ 𝓗) '' (r • Metric.closedBall (0 : 𝓗) 1)) =
      r • ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨toWeakSpace ℝ 𝓗 y, ?_, ?_⟩
    · exact ⟨y, hy, rfl⟩
    · simp
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    refine ⟨r • y, ?_, ?_⟩
    · exact ⟨y, hy, rfl⟩
    · simp

variable [CompleteSpace 𝓗]

private lemma weak_image_closedBall_zero_isCompact (r : ℝ) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) := by
  by_cases hr : 0 ≤ r
  · have hunit :
        IsCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
      isCompact_unitBall_weakSpace
    have hsmul :
        IsCompact
          (r • ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) :=
      IsCompact.smul r hunit
    rw [← smul_unitClosedBall_of_nonneg hr]
    rw [weak_image_smul_closedBall_eq_smul_weak_image_closedBall]
    exact hsmul
  · rw [Metric.closedBall_of_neg (lt_of_not_ge hr)]
    simp

/-- Helper for Lemma 2.45: every closed ball centered at `0` is weakly sequentially compact in a
real Hilbert space. -/
theorem weak_image_closedBall_zero_isSeqCompact (r : ℝ) :
    IsSeqCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) := by
  exact
    (weaklyCompact_iff_weaklySeqCompact (Metric.closedBall (0 : 𝓗) r)).mp
      (weak_image_closedBall_zero_isCompact r)

/-- Lemma 2.45: every bounded sequence in a real Hilbert space admits a weakly convergent
subsequence. Here weak convergence is expressed by convergence in `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: bound the range of the sequence inside a closed ball centered at `0`, use weak
-- compactness of that ball, convert it to weak sequential compactness via Eberlein-Smulian, and
-- then apply the subsequence characterization of sequential compactness in the weak topology.
theorem bounded_sequence_has_weakly_convergent_subsequence
    (x : ℕ → 𝓗) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ y : 𝓗, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ toWeakSpace ℝ 𝓗 (x (φ k))) atTop (𝓝 (toWeakSpace ℝ 𝓗 y)) := by
  obtain ⟨r, hsubset⟩ := hx.subset_closedBall (0 : 𝓗)
  have hseqCompactAmbient :
      IsSeqCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) :=
    weak_image_closedBall_zero_isSeqCompact r
  have hx_mem :
      ∀ n, toWeakSpace ℝ 𝓗 (x n) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) := by
    intro n
    refine ⟨x n, hsubset (Set.mem_range_self n), rfl⟩
  obtain ⟨w, hw, φ, hφ, hconv⟩ := hseqCompactAmbient hx_mem
  rcases hw with ⟨y, hy, rfl⟩
  refine ⟨y, φ, hφ, ?_⟩
  simpa [Function.comp] using hconv
