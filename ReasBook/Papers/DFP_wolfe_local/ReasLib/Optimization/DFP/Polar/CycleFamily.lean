module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

noncomputable section

namespace DFP.Polar

/-- The limiting-cycle angle `a = 2 * π / 9`. -/
def baseAngle : ℝ :=
  2 * Real.pi / 9

/-- The limiting-cycle angle equals `2 * π / 9`. -/
theorem baseAngle_def :
    baseAngle = 2 * Real.pi / 9 := by
  -- Unfolding `baseAngle` exposes the prescribed angle directly.
  rfl

/-- The first rational coordinate `z(ν)` of the limiting two-cycle family. -/
def cycleZ (ν : ℝ) : ℝ :=
  ν * (2 * baseAngle - ν) / (2 * ν - baseAngle)

/-- The rational formula defining `cycleZ`. -/
theorem cycleZ_def (ν : ℝ) :
    cycleZ ν = ν * (2 * baseAngle - ν) / (2 * ν - baseAngle) := by
  -- Unfolding `cycleZ` exposes its defining rational expression.
  rfl

/-- The second rational coordinate `w(ν)` of the limiting two-cycle family. -/
def cycleW (ν : ℝ) : ℝ :=
  ν * (baseAngle + ν) / (2 * ν - baseAngle)

/-- The rational formula defining `cycleW`. -/
theorem cycleW_def (ν : ℝ) :
    cycleW ν = ν * (baseAngle + ν) / (2 * ν - baseAngle) := by
  -- Unfolding `cycleW` exposes its defining rational expression.
  rfl

/-- The rational normalization factor `K(ν)` of the limiting two-cycle family. -/
def cycleK (ν : ℝ) : ℝ :=
  (2 * ν - baseAngle) / (ν * (2 * baseAngle - ν) * (baseAngle + ν))

/-- The rational formula defining `cycleK`. -/
theorem cycleK_def (ν : ℝ) :
    cycleK ν =
      (2 * ν - baseAngle) / (ν * (2 * baseAngle - ν) * (baseAngle + ν)) := by
  -- Unfolding `cycleK` exposes its defining rational expression.
  rfl

end DFP.Polar
