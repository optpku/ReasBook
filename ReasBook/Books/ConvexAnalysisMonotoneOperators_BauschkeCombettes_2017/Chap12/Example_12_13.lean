/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

namespace ERealFunction

/-- Coercing the packaged reciprocal barrier back to `EReal` recovers the source-facing owner
`reciprocalBarrier`. -/
@[simp] theorem inversePowerIoiExtension_one_asEReal :
    (inversePowerIoiExtension 1).asEReal = reciprocalBarrier := by
  funext x
  by_cases hx : 0 < x
  · simp [reciprocalBarrier, hx, inversePowerIoiExtension_apply_of_pos]
  · have hxle : x ≤ 0 := le_of_not_gt hx
    rcases hxle.eq_or_lt with rfl | hxlt
    · simp [reciprocalBarrier, inversePowerIoiExtension_apply_zero, zero_lt_one]
    · simp [reciprocalBarrier, hx, inversePowerIoiExtension_apply_of_neg, hxlt]

/-- The canonical `Γ₀(ℝ)` Fenchel conjugate of the reciprocal barrier agrees with the explicit
Chapter 13 conjugate `reciprocalBarrier∗`. -/
@[simp] theorem gammaZeroConjugate_inversePowerIoiExtension_one_apply (u : ℝ) :
    (gammaZeroConjugate
      (inversePowerIoiExtension 1)
      (inversePowerIoiExtension_mem_gammaZero 1 le_rfl)
      u : EReal) =
      reciprocalBarrier∗ u := by
  rw [gammaZeroConjugate_apply, conjugate_apply_real]
  have hbarrier :
      (fun x : ℝ ↦ ((u * x : ℝ) : EReal) - ↑(inversePowerIoiExtension 1 x)) =
        fun x : ℝ ↦ ((u * x : ℝ) : EReal) - reciprocalBarrier x := by
    funext x
    rw [show (inversePowerIoiExtension 1 x : EReal) = reciprocalBarrier x by
      simpa using congrArg (fun f : ℝ → EReal ↦ f x) inversePowerIoiExtension_one_asEReal]
  rw [hbarrier]
  simpa using (conjugate_apply_real reciprocalBarrier u).symm

/-- Coercing the packaged Fenchel conjugate of the reciprocal barrier back to `EReal` recovers the
ordinary Fenchel conjugate `reciprocalBarrier∗`. -/
@[simp] theorem gammaZeroConjugate_inversePowerIoiExtension_one_asEReal :
    (gammaZeroConjugate
      (inversePowerIoiExtension 1)
      (inversePowerIoiExtension_mem_gammaZero 1 le_rfl)).asEReal =
      reciprocalBarrier∗ := by
  funext u
  exact gammaZeroConjugate_inversePowerIoiExtension_one_apply u

-- Proof sketch: show that the reciprocal barrier is lower semicontinuous and convex on its
-- effective domain `(0, ∞)`, and identify the explicit conjugate with its Fenchel conjugate,
-- which enjoys the same two properties.
/-- Example 12.13: the reciprocal barrier and its canonical Fenchel conjugate both belong to
`Γ₀(ℝ)`. -/
theorem positiveReciprocalBarrier_and_conjugate_mem_gammaZero :
    reciprocalBarrier = (inversePowerIoiExtension 1).asEReal ∧
      reciprocalBarrier∗ =
        (gammaZeroConjugate
          (inversePowerIoiExtension 1)
          (inversePowerIoiExtension_mem_gammaZero 1 le_rfl)).asEReal ∧
      inversePowerIoiExtension 1 ∈ Γ₀(ℝ) ∧
      gammaZeroConjugate
          (inversePowerIoiExtension 1)
          (inversePowerIoiExtension_mem_gammaZero 1 le_rfl) ∈
        Γ₀(ℝ) := by
  refine ⟨inversePowerIoiExtension_one_asEReal.symm, ?_, ?_, ?_⟩
  · exact gammaZeroConjugate_inversePowerIoiExtension_one_asEReal.symm
  · exact inversePowerIoiExtension_mem_gammaZero 1 le_rfl
  · exact gammaZeroConjugate_mem_gammaZero
      (inversePowerIoiExtension_mem_gammaZero 1 le_rfl)

-- Proof sketch: compute the defining infimum explicitly. For every `x`, the candidate
-- decomposition `x = y + (x - y)` yields the function
-- `y ↦ 1 / y - 2 * sqrt (-(x - y))` on the admissible region, whose infimum is `0`.
/-- The infimal convolution of the reciprocal barrier with its conjugate is the zero function. -/
theorem positiveReciprocalBarrier_infimalConvolution_eq_zero :
    infimalConvolution reciprocalBarrier reciprocalBarrier∗ = 0 := sorry

-- Proof sketch: if exactness held at some `x`, there would be a minimizing decomposition
-- achieving the infimum in the previous theorem. The explicit formula for the summands shows the
-- infimum `0` is only approached along a limiting family and is never attained.
/-- The infimal convolution of the reciprocal barrier with its conjugate is nowhere exact. -/
theorem positiveReciprocalBarrier_infimalConvolution_nowhere_exact (x : ℝ) :
    ¬ infimalConvolution.ExactAt
        (inversePowerIoiExtension 1)
        (gammaZeroConjugate
          (inversePowerIoiExtension 1)
          (inversePowerIoiExtension_mem_gammaZero 1 le_rfl))
        x := sorry

-- Proof sketch: clause (i) identifies both functions as members of `Γ₀(ℝ)`, so their epigraphs
-- are nonempty closed convex subsets of `ℝ²`. The indicator of a nonempty closed convex set then
-- lies in `Γ₀(ℝ²)`.
/-- The indicators of the two epigraphs belong to `Γ₀(ℝ²)`. -/
theorem positiveReciprocalEpigraphIndicators_mem_gammaZero :
    ι[epigraph reciprocalBarrier] ∈ Γ₀(ℝ × ℝ) ∧
      ι[epigraph reciprocalBarrier∗] ∈ Γ₀(ℝ × ℝ) := sorry

-- Proof sketch: describe the Minkowski sum of the two epigraphs by writing a generic point of the
-- sum as the sum of one point on each epigraph, then eliminate the auxiliary coordinates to show
-- that the second coordinate is positive, and conversely construct such a decomposition for any
-- point with positive second coordinate.
/-- The Minkowski sum of the two epigraphs is the open upper half-plane. -/
theorem positiveReciprocalEpigraph_sum_eq_openUpperHalfPlane :
    epigraph reciprocalBarrier + epigraph reciprocalBarrier∗ =
      univ ×ˢ Ioi (0 : ℝ) := sorry

-- Proof sketch: use the indicator-version of infimal convolution from Example 12.3 with
-- `C = epi f` and `D = epi g`, then rewrite the Minkowski sum by the previous theorem.
/-- The infimal convolution of the two epigraph indicators is the indicator of the open upper
half-plane. -/
theorem positiveReciprocalEpigraphIndicators_infimalConvolution_eq_openUpperHalfPlaneIndicator :
    infimalConvolution (ι[epigraph reciprocalBarrier]).asEReal
        (ι[epigraph reciprocalBarrier∗]).asEReal =
      (ι[univ ×ˢ Ioi (0 : ℝ)]).asEReal := sorry

-- Proof sketch: rewrite the infimal convolution as the indicator of the open upper half-plane. An
-- indicator of a set is lower semicontinuous exactly when the set is closed, and the open upper
-- half-plane is not closed in `ℝ²`.
/-- The infimal convolution of the two epigraph indicators is not lower semicontinuous. -/
theorem positiveReciprocalEpigraphIndicators_infimalConvolution_not_lowerSemicontinuous :
    ¬ LowerSemicontinuous
      (infimalConvolution (ι[epigraph reciprocalBarrier]).asEReal
        (ι[epigraph reciprocalBarrier∗]).asEReal) := sorry

end ERealFunction
