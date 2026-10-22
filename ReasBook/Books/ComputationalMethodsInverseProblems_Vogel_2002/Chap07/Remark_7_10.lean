/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_10.Filters

public section

noncomputable section

namespace SpectralFilter

/-- Remark 7.10 (1). The discrete TSVD filter at `s ^ 2` is
`if ((n : ℝ) * α) ≤ s ^ 2 then 1 else 0`. -/
theorem discreteTsvd_sq_eq (n : ℕ) (α s : ℝ) :
    discreteTsvd n α (s ^ 2) = if ((n : ℝ) * α) ≤ s ^ 2 then 1 else 0 := by
  simpa using discreteTsvd_eq n α (s ^ 2)

/-- Remark 7.10 (2). The discrete Tikhonov filter at `s ^ 2` is
`s ^ 2 / (s ^ 2 + (n : ℝ) * α)`. -/
theorem discreteTikhonov_sq_eq (n : ℕ) (α s : ℝ) :
    discreteTikhonov n α (s ^ 2) = s ^ 2 / (s ^ 2 + (n : ℝ) * α) := by
  simpa using discreteTikhonov_eq n α (s ^ 2)

end SpectralFilter
