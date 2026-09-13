/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedSchedule

/-!
# Cross comparisons for the S3 seed

The actual scheduled detector points are compatible with the source half-line
and the interior anchor whenever the two source vectors satisfy their stated
Lorentz bounds.
-/

public section

namespace Lorentz

/-- The half-line's negative coordinate lies in the backward cone from time one. -/
theorem seed_halfLine_cone_bound (z v : parametrizedSubspace axisDirection)
    (hz : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hv : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64)
    (p : ℝ) (hp : p ≤ 1 / 2) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v)‖ ≤ 1 - p := by
  rw [map_add, map_smul]
  exact affine_halfLine_mem_pastCone_of_small_base
    (z := (0, negativeCoordinate axisDirection seed_axis_ne_zero z))
    (v := (0, negativeCoordinate axisDirection seed_axis_ne_zero v)) hz hv hp

/-- Half-line points and actual detector points satisfy the required norm comparison. -/
theorem seed_halfLine_detector_bound (z v : parametrizedSubspace axisDirection)
    (hz : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hv : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64)
    (p : ℝ) (hp : p ≤ 1 / 2) (n : ℕ) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v) -
      negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n)‖ ≤ |p - seedTime n| := by
  have ha := seed_halfLine_cone_bound z v hz hv p hp
  have hb := norm_negativeCoordinate_seedPoint_lt n
  have hc := seedRadius_lt_time_sub_one n
  have ht := norm_sub_le
    (negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v))
    (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n))
  have hg : seedTime n - p ≤ |p - seedTime n| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

/-- The anchor has negative coordinate norm at most one thirty-second. -/
theorem seed_anchor_norm_le (v : parametrizedSubspace axisDirection)
    (hv : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero ((2 : ℝ) • v)‖ ≤ 1 / 32 := by
  rw [map_smul, norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

/-- The half-line and anchor satisfy the required norm comparison. -/
theorem seed_halfLine_anchor_bound (z v : parametrizedSubspace axisDirection)
    (hz : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hv : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64)
    (p : ℝ) (hp : p ≤ 1 / 2) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v) -
      negativeCoordinate axisDirection seed_axis_ne_zero ((2 : ℝ) • v)‖ ≤ |p - 2| := by
  have ha := seed_halfLine_cone_bound z v hz hv p hp
  have hb := seed_anchor_norm_le v hv
  have ht := norm_sub_le
    (negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v))
    (negativeCoordinate axisDirection seed_axis_ne_zero ((2 : ℝ) • v))
  rw [abs_of_nonpos (by linarith : p - 2 ≤ 0)]
  linarith

/-- Actual detector points and the anchor satisfy the required norm comparison. -/
theorem seed_detector_anchor_bound (v : parametrizedSubspace axisDirection)
    (hv : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64) (n : ℕ) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n) -
      negativeCoordinate axisDirection seed_axis_ne_zero ((2 : ℝ) • v)‖ ≤ |seedTime n - 2| := by
  have ha := norm_negativeCoordinate_seedPoint_lt n
  have hb := seedRadius_le_one_div_128 n
  have hc := seed_anchor_norm_le v hv
  have hd := (seedTime_bounds n).2
  have ht := norm_sub_le
    (negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n))
    (negativeCoordinate axisDirection seed_axis_ne_zero ((2 : ℝ) • v))
  rw [abs_of_nonpos (by linarith : seedTime n - 2 ≤ 0)]
  linarith

/-- Two points on the source half-line satisfy the required norm comparison. -/
theorem seed_halfLine_pair_bound (z v : parametrizedSubspace axisDirection)
    (hv : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64)
    (p q : ℝ) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v) -
      negativeCoordinate axisDirection seed_axis_ne_zero (z + q • v)‖ ≤ |p - q| := by
  simp only [map_add, map_smul]
  have hvone : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 := by linarith
  exact affine_halfLine_norm_sub_le_abs_sub
    (z := (0, negativeCoordinate axisDirection seed_axis_ne_zero z))
    (v := (0, negativeCoordinate axisDirection seed_axis_ne_zero v)) hvone

end Lorentz
