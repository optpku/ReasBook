/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_44

public section

noncomputable section

universe u v

namespace GeneralizedTikhonov

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

/-- Under Assumption A2 and `α > 0`, the scaled canonical reconstruction operator
`reconstructionOperator K L (2 * α)` minimizes the Tikhonov functional pointwise. -/
theorem isReconstruction_reconstructionOperator
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) {α : ℝ} (hα : 0 < α) :
    IsReconstruction K L α (reconstructionOperator K L (2 * α)) := by
  rw [isReconstruction_iff]
  intro g
  exact scaledReconstruction_isMinOn K L hL hα g

end GeneralizedTikhonov
