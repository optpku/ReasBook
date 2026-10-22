/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

/-- Helper for Lemma 2.39: every scaled closed unit ball is weakly sequentially compact in a real
Hilbert space. -/
private lemma isSeqCompact_weakImage_smul_unit_ball
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (a : ℝ) :
    IsSeqCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) := by
  have hweakCompact :
      IsCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) :=
    isCompact_weakImage_smul_unit_ball a
  -- Fact 2.37 converts weak compactness of the scaled ball into weak sequential compactness.
  exact (weaklyCompact_iff_weaklySeqCompact (a • {x : 𝓗 | ‖x‖ ≤ 1})).mp hweakCompact

/-- Lemma 2.39: for a norm-bounded subset of a real Hilbert space, weak closedness is equivalent to
weak sequential closedness. Both notions are expressed on the image of `C` in `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: the forward implication is the general fact that closed subsets are sequentially
-- closed. For the converse, place `C` inside a closed ball using boundedness, use weak sequential
-- compactness of that ball and sequential closedness of `C` to get weak sequential compactness of
-- `C`, then apply weak Eberlein-Smulian to obtain weak compactness and finally use Hausdorffness of
-- `WeakSpace ℝ 𝓗` to conclude weak closedness.
theorem weaklyClosed_iff_weaklySeqClosed_of_bounded
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    {C : Set 𝓗} (hC : Bornology.IsBounded C) :
    IsClosed ((toWeakSpace ℝ 𝓗) '' C) ↔ IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  constructor
  · intro hclosed
    -- Closed subsets are sequentially closed in every topological space.
    exact hclosed.isSeqClosed
  · intro hseqClosed
    have hclosedBall :
        (Metric.closedBall (0 : 𝓗) 1 : Set 𝓗) = {x : 𝓗 | ‖x‖ ≤ 1} := by
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm]
    rcases (NormedSpace.isBounded_iff_subset_smul_closedBall ℝ).1 hC with ⟨a, ha⟩
    have hsubset :
        C ⊆ a • {x : 𝓗 | ‖x‖ ≤ 1} := by
      simpa [hclosedBall] using ha
    have hsubsetWeak :
        (toWeakSpace ℝ 𝓗) '' C ⊆ (toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1}) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hsubset hx, rfl⟩
    have hseqCompactAmbient :
        IsSeqCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) :=
      isSeqCompact_weakImage_smul_unit_ball a
    have hseqCompactC : IsSeqCompact ((toWeakSpace ℝ 𝓗) '' C) :=
      hseqCompactAmbient.of_isSeqClosed_subset hseqClosed hsubsetWeak
    have hcompactC : IsCompact ((toWeakSpace ℝ 𝓗) '' C) :=
      (weaklyCompact_iff_weaklySeqCompact C).mpr hseqCompactC
    have hcompact_iff :
        IsCompact ((toWeakSpace ℝ 𝓗) '' C) ↔
          IsClosed ((toWeakSpace ℝ 𝓗) '' C) ∧ Bornology.IsBounded C :=
      weaklyCompact_iff_weaklyClosed_and_bounded
    exact (hcompact_iff.mp hcompactC).1
