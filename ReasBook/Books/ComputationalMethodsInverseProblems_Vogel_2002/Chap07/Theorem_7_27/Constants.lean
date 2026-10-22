/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19.KernelMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace TikhonovDiscrepancy

/-- The nonsaturated discrepancy-principle constant `C₁^discrep` from Theorem
7.27, written using the kernel moment `I_{p,2}^{p - q}`. -/
def parameterConstant1 (b c p q : ℝ) : ℝ :=
  (((2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) /
      KernelMoment.integral p 2 (p - q)) *
    (c ^ (q / p) / b)) ^ (p / (p + q))

/-- The defining formula for `parameterConstant1`. -/
theorem parameterConstant1_def (b c p q : ℝ) :
    parameterConstant1 b c p q =
      (((2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) /
          KernelMoment.integral p 2 (p - q)) *
        (c ^ (q / p) / b)) ^ (p / (p + q)) := by
  -- Unfold the benchmark constant once.
  rfl

/-- The saturated discrepancy-principle constant `C₂^discrep` from Theorem
7.27, parameterized by the source scalar `‖f_true‖_{K*}^2`. -/
def parameterConstant2 (c p normKStarSq : ℝ) : ℝ :=
  ((c ^ (1 / p) * (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)) /
    normKStarSq) ^ (p / (2 * p + 1))

/-- The defining formula for `parameterConstant2`. -/
theorem parameterConstant2_def (c p normKStarSq : ℝ) :
    parameterConstant2 c p normKStarSq =
      ((c ^ (1 / p) * (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)) /
        normKStarSq) ^ (p / (2 * p + 1)) := by
  -- Unfold the saturated benchmark constant once.
  rfl

end TikhonovDiscrepancy
