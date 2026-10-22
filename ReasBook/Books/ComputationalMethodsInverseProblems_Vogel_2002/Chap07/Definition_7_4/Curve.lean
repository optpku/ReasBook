/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace LCurve

/-- The logarithmic residual-energy coordinate `α ↦ log (R α)` for an L-curve. -/
def logResidualSq (R : ℝ → ℝ) : ℝ → ℝ :=
  fun α ↦ Real.log (R α)

/-- The defining formula for `LCurve.logResidualSq`. -/
theorem logResidualSq_def (R : ℝ → ℝ) (α : ℝ) :
    logResidualSq R α = Real.log (R α) := by
  simp [logResidualSq]

/-- The logarithmic solution-energy coordinate `α ↦ log (S α)` for an L-curve. -/
def logSolutionSq (S : ℝ → ℝ) : ℝ → ℝ :=
  fun α ↦ Real.log (S α)

/-- The defining formula for `LCurve.logSolutionSq`. -/
theorem logSolutionSq_def (S : ℝ → ℝ) (α : ℝ) :
    logSolutionSq S α = Real.log (S α) := by
  simp [logSolutionSq]

/-- The curvature formula `(X'' Y' - X' Y'') / (X'^2 + Y'^2)^(3/2)` for a
smooth logarithmic L-curve parametrization `(X, Y)`. -/
def curvatureOfLogs (X Y : ℝ → ℝ) : ℝ → ℝ :=
  fun α ↦
    (iteratedDeriv 2 X α * deriv Y α - deriv X α * iteratedDeriv 2 Y α) /
      Real.rpow (deriv X α ^ 2 + deriv Y α ^ 2) (3 / 2 : ℝ)

/-- The defining formula for `LCurve.curvatureOfLogs`. -/
theorem curvatureOfLogs_def (X Y : ℝ → ℝ) (α : ℝ) :
    curvatureOfLogs X Y α =
      (iteratedDeriv 2 X α * deriv Y α - deriv X α * iteratedDeriv 2 Y α) /
        Real.rpow (deriv X α ^ 2 + deriv Y α ^ 2) (3 / 2 : ℝ) := by
  simp [curvatureOfLogs]

/-- The energy-only curvature formula `(7.32)` written directly in terms of the
residual and solution energies `R`, `S`, and `deriv S`. -/
def curvatureFromEnergies (R S : ℝ → ℝ) : ℝ → ℝ :=
  fun α ↦
    -(R α * S α * (α * R α + α ^ 2 * S α) + (R α * S α) ^ 2 / deriv S α) /
      Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ)

/-- The defining formula for `LCurve.curvatureFromEnergies`. -/
theorem curvatureFromEnergies_def (R S : ℝ → ℝ) (α : ℝ) :
    curvatureFromEnergies R S α =
      -(R α * S α * (α * R α + α ^ 2 * S α) + (R α * S α) ^ 2 / deriv S α) /
        Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) := by
  simp [curvatureFromEnergies]

/-- A corner parameter is a positive parameter where the curvature function
achieves a maximum. -/
def IsCornerParameter (κ : ℝ → ℝ) (α : ℝ) : Prop :=
  IsMaxOn κ (Set.Ioi (0 : ℝ)) α

/-- The defining characterization of `LCurve.IsCornerParameter`. -/
theorem IsCornerParameter_iff (κ : ℝ → ℝ) (α : ℝ) :
    IsCornerParameter κ α ↔ IsMaxOn κ (Set.Ioi (0 : ℝ)) α := Iff.rfl

end LCurve
