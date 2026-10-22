/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic

public section

noncomputable section

namespace TsvdEstimation

/-- The explicit TSVD benchmark truncation-index sequence from `(7.63)`. -/
def optimalIndex (b c p q σ : ℝ) : ℕ → ℕ :=
  fun n ↦
    Nat.floor
      (((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))))

/-- The defining floor formula for `optimalIndex`. -/
theorem optimalIndex_def (b c p q σ : ℝ) (n : ℕ) :
    optimalIndex b c p q σ n =
      Nat.floor
        (((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))) := by
  rfl

end TsvdEstimation
