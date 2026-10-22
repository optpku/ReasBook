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

namespace TsvdDiscrepancy

/-- The explicit TSVD discrepancy-principle constant from `(7.89)`. -/
def indexConstant (b c p q : ℝ) : ℝ :=
  ((b * c) / (p + q - 1)) ^ (1 / (p + q))

/-- The defining closed form for `indexConstant`. -/
theorem indexConstant_def (b c p q : ℝ) :
    indexConstant b c p q =
      ((b * c) / (p + q - 1)) ^ (1 / (p + q)) := by
  rfl

/-- The explicit TSVD discrepancy-principle benchmark sequence from `(7.89)`. -/
def indexBenchmark (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ indexConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))

/-- The defining pointwise formula for `indexBenchmark`. -/
theorem indexBenchmark_def (b c p q σ : ℝ) (n : ℕ) :
    indexBenchmark b c p q σ n =
      indexConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
  rfl

end TsvdDiscrepancy
