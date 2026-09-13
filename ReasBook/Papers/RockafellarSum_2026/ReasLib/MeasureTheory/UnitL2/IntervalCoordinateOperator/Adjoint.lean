/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.L1.Transpose
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator

/-!
# Interval-coordinate adjoint

This module defines the transpose of the interval-coordinate operator through
the real Riesz identification of `UnitL2`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace L1Seq

/-- The transpose of the interval-coordinate operator, reindexed through the real Riesz
identification of `UnitL2` with its strong dual. -/
noncomputable def intervalCoordinateAdjoint : UnitL2 →L[ℝ] StrongDual ℝ L1Seq :=
  intervalCoordinateOperator.paperTranspose.comp
    (InnerProductSpace.toDual ℝ UnitL2).toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluation of the interval-coordinate adjoint at an ℓ¹ vector is the inner product
with the corresponding synthesized interval vector. -/
theorem intervalCoordinateAdjoint_apply (y : UnitL2) (a : L1Seq) :
    intervalCoordinateAdjoint y a = ⟪y, intervalCoordinateOperator a⟫_ℝ := by
  -- Evaluate the transpose, then identify the resulting functional by the real Riesz map.
  simp [intervalCoordinateAdjoint, ContinuousLinearMap.paperTranspose_apply]

/-- Evaluating the interval-coordinate adjoint at the `n`th ℓ¹ unit vector gives the
inner product with the `n`th rational interval-indicator vector. -/
theorem intervalCoordinateAdjoint_apply_single (y : UnitL2) (n : ℕ) :
    intervalCoordinateAdjoint y (lp.single 1 n (1 : ℝ)) =
      ⟪y, UnitL2.rationalIntervalVec n⟫_ℝ := by
  -- Reduce to the general adjoint formula and compute the synthesized unit coordinate.
  rw [intervalCoordinateAdjoint_apply, intervalCoordinateOperator_apply_single]

end L1Seq
