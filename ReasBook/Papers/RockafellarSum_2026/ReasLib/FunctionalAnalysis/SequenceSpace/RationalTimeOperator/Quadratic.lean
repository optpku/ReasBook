/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.InfiniteSum.NatTriangle
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Positive-operator quadratic series

This module develops the summability and triangular-series identities for the
rational-time positive operator.
-/

public section

namespace L1Seq

/-- The absolute values of the product-indexed rational-time kernel associated with an
`L1Seq` are summable. -/
theorem summable_abs_positiveOperator_kernel (a : L1Seq) :
    Summable (fun p : ℕ × ℕ ↦
      |min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2|) := by
  -- Recover the summable absolute-coordinate series from the exponent-one `lp` norm.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun n : ℕ ↦ |a n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hOne a).summable
  have hProduct : Summable (fun p : ℕ × ℕ ↦ |a p.1| * |a p.2|) :=
    hAbs.mul_of_nonneg hAbs (fun n ↦ abs_nonneg (a n)) (fun n ↦ abs_nonneg (a n))
  -- Every kernel coefficient lies in `[0, 1]`, giving the product majorant.
  refine Summable.of_nonneg_of_le (fun p ↦ abs_nonneg _) (fun p ↦ ?_) hProduct
  rw [abs_mul, abs_mul,
    abs_of_nonneg (le_min (rationalTime_mem_Ioo p.1).1.le
      (rationalTime_mem_Ioo p.2).1.le)]
  calc
    min (rationalTime p.1) (rationalTime p.2) * |a p.1| * |a p.2| =
        min (rationalTime p.1) (rationalTime p.2) * (|a p.1| * |a p.2|) := by
      rw [mul_assoc]
    _ ≤ 1 * (|a p.1| * |a p.2|) :=
      mul_le_mul_of_nonneg_right
        ((min_le_left _ _).trans (rationalTime_mem_Ioo p.1).2.le)
        (mul_nonneg (abs_nonneg (a p.1)) (abs_nonneg (a p.2)))
    _ = |a p.1| * |a p.2| := one_mul _

/-- The absolute values of the diagonal terms of the rational-time quadratic series
associated with an `L1Seq` are summable. -/
theorem summable_abs_positiveOperator_diagonal (a : L1Seq) :
    Summable (fun n : ℕ ↦ |rationalTime n * (a n) ^ 2|) := by
  -- Restrict the summable kernel family to the injectively embedded diagonal.
  have hDiagonalEmbedding : Function.Injective (fun n : ℕ ↦ (n, n)) := by
    intro m n hmn
    exact congrArg Prod.fst hmn
  simpa only [Function.comp_def, min_self, pow_two, mul_assoc] using
    (summable_abs_positiveOperator_kernel a).comp_injective hDiagonalEmbedding

/-- The absolute value of a weighted strict-upper tail is at most the `L1Seq` norm. -/
private theorem abs_tsum_positiveOperatorTail_le_norm (a : L1Seq) (n : ℕ) :
    |∑' m : ℕ,
      if n < m then min (rationalTime n) (rationalTime m) * a m else 0| ≤ ‖a‖ := by
  -- Use the exact absolute-coordinate sum as the majorizing series.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : HasSum (fun m : ℕ ↦ |a m|) ‖a‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      lp.hasSum_norm hOne a
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hAbs (fun m ↦ ?_)
  by_cases hnm : n < m
  · rw [if_pos hnm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (le_min (rationalTime_mem_Ioo n).1.le
        (rationalTime_mem_Ioo m).1.le)]
    exact mul_le_of_le_one_left (abs_nonneg (a m))
      ((min_le_left _ _).trans (rationalTime_mem_Ioo n).2.le)
  · simp only [if_neg hnm, norm_zero, abs_nonneg]

/-- The absolute values of the outer strict-upper terms of the rational-time quadratic
series associated with an `L1Seq` are summable. -/
theorem summable_abs_positiveOperator_offDiagonal (a : L1Seq) :
    Summable (fun n : ℕ ↦
      |(2 * ∑' m : ℕ,
        if n < m then min (rationalTime n) (rationalTime m) * a m else 0) * a n|) := by
  -- Scale the summable absolute-coordinate family to obtain an outer majorant.
  have hOne : 0 < (1 : ENNReal).toReal := by
    norm_num
  have hAbs : Summable (fun n : ℕ ↦ |a n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.hasSum_norm hOne a).summable
  have hMajorant : Summable (fun n : ℕ ↦ (2 * ‖a‖) * |a n|) :=
    hAbs.mul_left (2 * ‖a‖)
  -- The tail estimate bounds each outer term by the scaled absolute coordinate.
  refine Summable.of_nonneg_of_le (fun n ↦ abs_nonneg _) (fun n ↦ ?_) hMajorant
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_tsum_positiveOperatorTail_le_norm a n) (by norm_num))
    (abs_nonneg (a n))

/-- The diagonal plus twice the strict-upper-triangle sum of the rational-time kernel
associated with an `L1Seq` equals its full product-indexed sum. -/
theorem positiveOperator_diag_add_two_upper_eq_kernel (a : L1Seq) :
    (∑' n : ℕ, rationalTime n * (a n) ^ 2) +
        2 * (∑' n : ℕ, ∑' m : ℕ,
          if n < m then min (rationalTime n) (rationalTime m) * a n * a m else 0) =
      ∑' p : ℕ × ℕ,
        min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2 := by
  -- Convert the established absolute summability bound to norm summability.
  have hKernelNorm : Summable (fun p : ℕ × ℕ ↦
      ‖min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_positiveOperator_kernel a
  have hKernel : Summable (fun p : ℕ × ℕ ↦
      min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2) :=
    hKernelNorm.of_norm
  -- Symmetry identifies the lower triangular series with the upper one.
  have hKernelSymm : ∀ n m : ℕ,
      min (rationalTime n) (rationalTime m) * a n * a m =
        min (rationalTime m) (rationalTime n) * a m * a n := by
    intro n m
    rw [min_comm]
    ring
  have hTriangle := hKernel.tsum_prod_eq_diag_add_two_upper_of_symm hKernelSymm
  -- Reverse the decomposition and normalize its diagonal and doubling notation.
  simpa only [min_self, pow_two, mul_assoc, two_nsmul, two_mul] using hTriangle.symm

end L1Seq
