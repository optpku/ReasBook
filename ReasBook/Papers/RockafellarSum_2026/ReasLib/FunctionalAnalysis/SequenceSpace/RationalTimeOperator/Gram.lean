/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Quadratic
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

/-!
# Rational-time Gram identities

This module derives the Gram expansion for the interval-coordinate operator.
-/

namespace L1Seq

open scoped InnerProductSpace

/-- For `L1Seq.gramTsum_eq_norm_intervalCoordinateOperator_sq`, the inner product of
two interval-coordinate summands is their rational-time Gram coefficient. -/
private theorem intervalCoordinateSummand_inner (a : L1Seq) (n m : ℕ) :
    ⟪a n • UnitL2.rationalIntervalVec n, a m • UnitL2.rationalIntervalVec m⟫_ℝ =
      min (rationalTime n) (rationalTime m) * a n * a m := by
  -- Pull the two real scalars outside, then use the interval-indicator Gram formula.
  rw [real_inner_smul_left, real_inner_smul_right]
  unfold UnitL2.rationalIntervalVec
  rw [UnitL2.inner_intervalVec_of_mem_Ioo _ _
    (rationalTime_mem_Ioo n) (rationalTime_mem_Ioo m)]
  ring

/-- For `L1Seq.gramTsum_eq_norm_intervalCoordinateOperator_sq`, the self-inner-product
of the interval-coordinate synthesis is the iterated sum of pairwise inner products. -/
private theorem inner_intervalCoordinateSeries_eq_tsum (a : L1Seq) :
    ⟪∑' n : ℕ, a n • UnitL2.rationalIntervalVec n,
        ∑' n : ℕ, a n • UnitL2.rationalIntervalVec n⟫_ℝ =
      ∑' n : ℕ, ∑' m : ℕ,
        ⟪a n • UnitL2.rationalIntervalVec n,
          a m • UnitL2.rationalIntervalVec m⟫_ℝ := by
  -- Norm summability supplies the summability needed in both arguments.
  have hSummable : Summable (fun n : ℕ ↦ a n • UnitL2.rationalIntervalVec n) :=
    (summable_norm_smul_rationalIntervalVec a).of_norm
  -- Continuity of the inner product expands its first argument.
  calc
    ⟪∑' n : ℕ, a n • UnitL2.rationalIntervalVec n,
        ∑' n : ℕ, a n • UnitL2.rationalIntervalVec n⟫_ℝ =
        ∑' n : ℕ, ⟪a n • UnitL2.rationalIntervalVec n,
          ∑' m : ℕ, a m • UnitL2.rationalIntervalVec m⟫_ℝ := by
      simpa only [innerSLFlip_apply_apply] using
        (innerSLFlip ℝ (∑' m : ℕ, a m • UnitL2.rationalIntervalVec m)).map_tsum hSummable
    _ = ∑' n : ℕ, ∑' m : ℕ,
        ⟪a n • UnitL2.rationalIntervalVec n,
          a m • UnitL2.rationalIntervalVec m⟫_ℝ := by
      -- Expand the second argument separately for each outer summand.
      apply tsum_congr
      intro n
      simpa only [innerSL_apply_apply] using
        (innerSL ℝ (a n • UnitL2.rationalIntervalVec n)).map_tsum hSummable

/-- For `L1Seq.gramTsum_eq_norm_intervalCoordinateOperator_sq`, the rational-time Gram
series equals the self-inner-product of the interval-coordinate synthesis. -/
private theorem gramTsum_eq_inner_intervalCoordinateSeries (a : L1Seq) :
    (∑' p : ℕ × ℕ,
      min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2) =
      ⟪∑' n : ℕ, a n • UnitL2.rationalIntervalVec n,
        ∑' n : ℕ, a n • UnitL2.rationalIntervalVec n⟫_ℝ := by
  -- Absolute summability permits conversion from the product sum to an iterated sum.
  have hKernelNorm : Summable (fun p : ℕ × ℕ ↦
      ‖min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2‖) := by
    simpa only [Real.norm_eq_abs] using summable_abs_positiveOperator_kernel a
  have hKernel : Summable (fun p : ℕ × ℕ ↦
      min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2) :=
    hKernelNorm.of_norm
  rw [hKernel.tsum_prod]
  -- Replace every scalar kernel coefficient by its interval-vector inner product.
  simp_rw [← intervalCoordinateSummand_inner]
  exact (inner_intervalCoordinateSeries_eq_tsum a).symm

/-- The full rational-time Gram series of an `L1Seq` is the squared `UnitL2` norm of
its image under `intervalCoordinateOperator`. -/
public theorem gramTsum_eq_norm_intervalCoordinateOperator_sq (a : L1Seq) :
    (∑' p : ℕ × ℕ,
      min (rationalTime p.1) (rationalTime p.2) * a p.1 * a p.2) =
      ‖intervalCoordinateOperator a‖ ^ 2 := by
  -- Identify the Gram sum with the synthesis self-inner-product.
  rw [gramTsum_eq_inner_intervalCoordinateSeries]
  -- Fold the synthesis back into the operator and use the Hilbert-space norm identity.
  rw [← intervalCoordinateOperator_apply, real_inner_self_eq_norm_sq]

end L1Seq
