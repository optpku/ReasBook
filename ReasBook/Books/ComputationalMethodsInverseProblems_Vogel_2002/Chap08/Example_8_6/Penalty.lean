/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- The Huber-type penalty `x ↦ ‖x‖ ^ 2 / (2 * ε)` for `‖x‖ ≤ ε` and
`x ↦ ‖x‖ - ε / 2` for `ε < ‖x‖` on `EuclideanSpace ℝ (Fin d)`. -/
def huberPenalty (ε : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x ↦ if ‖x‖ ≤ ε then ‖x‖ ^ 2 / (2 * ε) else ‖x‖ - ε / 2

/-- The defining piecewise formula for `huberPenalty`. -/
theorem huberPenalty_def (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    huberPenalty ε x =
      if ‖x‖ ≤ ε then ‖x‖ ^ 2 / (2 * ε) else ‖x‖ - ε / 2 := by
  rfl

/-- If `‖x‖ ≤ ε`, then `huberPenalty ε x` is given by the quadratic branch. -/
theorem huberPenalty_of_norm_le (ε : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (h : ‖x‖ ≤ ε) :
    huberPenalty ε x = ‖x‖ ^ 2 / (2 * ε) := by
  simp [huberPenalty_def, h]

/-- If `ε < ‖x‖`, then `huberPenalty ε x` is given by the affine branch. -/
theorem huberPenalty_of_lt_norm (ε : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (h : ε < ‖x‖) :
    huberPenalty ε x = ‖x‖ - ε / 2 := by
  simp [huberPenalty_def, not_le_of_gt h]

end VariationalRegularization
