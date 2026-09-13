/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.Sequence.L1Synthesis
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.RationalIntervalIndicator

/-!
# Interval-coordinate operator bounds

This module records norm bounds for the rational interval-coordinate vectors.
-/

public section

noncomputable section

namespace UnitL2

/-- The fixed rational interval-indicator vectors have norm at most one. -/
theorem norm_rationalIntervalVec_le_one (n : ℕ) :
    ‖rationalIntervalVec n‖ ≤ 1 := by
  -- Expose the rational endpoint and apply the general interval-vector estimate.
  unfold rationalIntervalVec
  exact norm_intervalVec_le_one_of_mem_Ioo _ (rationalTime_mem_Ioo n)

end UnitL2

namespace L1Seq

/-- The bounded real-linear synthesis map for the fixed rational interval-indicator family. -/
noncomputable def intervalCoordinateOperator : L1Seq →L[ℝ] UnitL2 :=
  synthesis UnitL2.rationalIntervalVec UnitL2.norm_rationalIntervalVec_le_one

/-- The interval-coordinate summands of an `L1Seq` element are norm-summable. -/
theorem summable_norm_smul_rationalIntervalVec (a : L1Seq) :
    Summable (fun n : ℕ ↦ ‖a n • UnitL2.rationalIntervalVec n‖) := by
  -- Specialize the generic synthesis summability theorem to the interval vectors.
  exact summable_norm_smul UnitL2.rationalIntervalVec
    UnitL2.norm_rationalIntervalVec_le_one a

/-- Applying `intervalCoordinateOperator` gives the sum of the interval coordinates. -/
theorem intervalCoordinateOperator_apply (a : L1Seq) :
    intervalCoordinateOperator a =
      ∑' n : ℕ, a n • UnitL2.rationalIntervalVec n := by
  -- Use the computation rule for synthesis after exposing the wrapper definition.
  unfold intervalCoordinateOperator
  exact synthesis_apply UnitL2.rationalIntervalVec
    UnitL2.norm_rationalIntervalVec_le_one a

/-- A unit `L1Seq` coordinate is sent to its corresponding rational interval vector. -/
theorem intervalCoordinateOperator_apply_single (n : ℕ) :
    intervalCoordinateOperator (lp.single 1 n (1 : ℝ)) = UnitL2.rationalIntervalVec n := by
  rw [intervalCoordinateOperator_apply]
  rw [tsum_eq_single n]
  · simp [lp.single_apply]
  · intro m hm
    simp [lp.single_apply, hm]

/-- The interval-coordinate operator does not increase the norm of an input. -/
theorem norm_intervalCoordinateOperator_apply_le (a : L1Seq) :
    ‖intervalCoordinateOperator a‖ ≤ ‖a‖ := by
  -- Turn the generic synthesis operator-norm bound into a pointwise estimate.
  unfold intervalCoordinateOperator
  simpa only [one_mul] using
    (synthesis UnitL2.rationalIntervalVec
      UnitL2.norm_rationalIntervalVec_le_one).le_of_opNorm_le
      (norm_synthesis_le UnitL2.rationalIntervalVec
        UnitL2.norm_rationalIntervalVec_le_one) a

/-- The operator norm of `intervalCoordinateOperator` is at most one. -/
theorem norm_intervalCoordinateOperator_le :
    ‖intervalCoordinateOperator‖ ≤ 1 := by
  -- The generic synthesis bound applies with uniform constant one.
  unfold intervalCoordinateOperator
  exact norm_synthesis_le UnitL2.rationalIntervalVec
    UnitL2.norm_rationalIntervalVec_le_one

end L1Seq
