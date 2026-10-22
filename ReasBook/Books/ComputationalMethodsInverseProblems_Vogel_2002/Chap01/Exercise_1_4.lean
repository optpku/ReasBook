/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_4.ErrorTerms

public section

namespace FilterRegularization

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exercise 1.4. For noisy data written as `d = K fTrue + η`, the
reconstruction error decomposes as
`R d - fTrue = truncationError R K fTrue + noiseError R η`. -/
theorem error_eq_truncationError_add_noiseError
    {K : E →L[ℝ] F} {R : F →L[ℝ] E} {fTrue : E} {d η : F}
    (h_data : d = K fTrue + η) :
    R d - fTrue = truncationError R K fTrue + noiseError R η := by
  simp [h_data, truncationError, noiseError, sub_eq_add_neg, add_left_comm, add_comm]

end FilterRegularization
