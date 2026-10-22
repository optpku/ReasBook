/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.LinearMapFiniteDimensionalNorm

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The dual norm of a linear functional, realized as the operator norm of the associated
continuous linear functional. -/
def dualNorm (y : Module.Dual ℝ E) : ℝ :=
  ‖y‖

/-- The dual norm agrees with the operator norm of the associated continuous linear functional. -/
theorem dualNorm_eq_toContinuousLinearMap_norm (y : Module.Dual ℝ E) :
    dualNorm y = ‖y.toContinuousLinearMap‖ :=
  rfl

/-- Lemma 1.1 [generalized Cauchy--Schwarz inequality]: on a real normed space, the canonical
pairing between `y : E* = Module.Dual ℝ E` and `x : E` satisfies
`|y x| ≤ ‖y‖ * ‖x‖`. -/
theorem abs_apply_le_dual_norm_mul_norm (y : Module.Dual ℝ E) (x : E) :
    |y x| ≤ dualNorm y * ‖x‖ := by
  simpa [dualNorm, Real.norm_eq_abs] using y.toContinuousLinearMap.le_opNorm x

end
