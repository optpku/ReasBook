/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic

public section

noncomputable section

namespace TsvdEstimation

/-- The explicit TSVD asymptotic constant `C₁^TSVD` from `(7.64)`. -/
def errorConstant (b c p q : ℝ) : ℝ :=
  ((p + q) / ((p + 1) * (q - 1))) * ((b ^ (p + 1) / c ^ (q - 1)) ^ (1 / (p + q)))

/-- The defining closed form for `errorConstant`. -/
theorem errorConstant_def (b c p q : ℝ) :
    errorConstant b c p q =
      ((p + q) / ((p + 1) * (q - 1))) *
        ((b ^ (p + 1) / c ^ (q - 1)) ^ (1 / (p + q))) := sorry

end TsvdEstimation
