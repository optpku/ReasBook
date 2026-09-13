/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates

/-!
# Scaled detector combinations
-/

public section


namespace Lorentz

/-- The affine detector combination used by the seed construction. -/
noncomputable def scaledDetector {d : C0Seq} (ξ h : parametrizedSubspace d) (r : ℝ) :
    parametrizedSubspace d := ξ + r • h

/-- The ambient value of a scaled detector is its affine combination. -/
theorem coe_scaledDetector {d : C0Seq} (ξ h : parametrizedSubspace d) (r : ℝ) :
    (scaledDetector ξ h r : C0Seq × L1Seq) =
      (ξ : C0Seq × L1Seq) + r • (h : C0Seq × L1Seq) := by
  rfl

/-- Positive Lorentz coordinates of a scaled detector combination expand
linearly. -/
theorem positiveCoordinate_scaledDetector {d : C0Seq} (hd : d ≠ 0)
    (ξ h : parametrizedSubspace d) (r : ℝ) :
    positiveCoordinate d hd (scaledDetector ξ h r) =
      positiveCoordinate d hd ξ + r * positiveCoordinate d hd h := by
  unfold scaledDetector
  rw [map_add, map_smul]
  simp only [smul_eq_mul]

/-- Negative Lorentz coordinates of a scaled detector combination expand
linearly. -/
theorem negativeCoordinate_scaledDetector {d : C0Seq} (hd : d ≠ 0)
    (ξ h : parametrizedSubspace d) (r : ℝ) :
    negativeCoordinate d hd (scaledDetector ξ h r) =
      negativeCoordinate d hd ξ + r • negativeCoordinate d hd h := by
  unfold scaledDetector
  rw [map_add, map_smul]

end Lorentz
