/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

noncomputable section

namespace VariationalRegularization

/-- The source-facing `L²` pairing on the unit square `[0,1] × [0,1]`,
expressed as an iterated integral on raw functions. -/
@[expose]
def unitSquareL2Pairing (u h : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, u (x, y) * h (x, y)

/-- The defining iterated-integral formula for `unitSquareL2Pairing`. -/
theorem unitSquareL2Pairing_def (u h : ℝ × ℝ → ℝ) :
    unitSquareL2Pairing u h =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, u (x, y) * h (x, y) := by
  -- This theorem just exposes the pairing definition.
  rfl

end VariationalRegularization
