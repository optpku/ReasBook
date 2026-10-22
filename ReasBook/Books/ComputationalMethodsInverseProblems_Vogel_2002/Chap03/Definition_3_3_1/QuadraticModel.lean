/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Newton quadratic model at the current iterate `f_v`, viewed as a function
`H → ℝ` in the step variable `s`. -/
def quadraticModel (J : H → ℝ) (f_v : H) : H → ℝ :=
  fun s ↦ J f_v + inner ℝ (gradient J f_v) s + (1 / 2 : ℝ) * inner ℝ (hessian J f_v s) s

/-- The defining formula for `Newton.quadraticModel`. -/
theorem quadraticModel_apply (J : H → ℝ) (f_v s : H) :
    quadraticModel J f_v s =
      J f_v + inner ℝ (gradient J f_v) s + (1 / 2 : ℝ) * inner ℝ (hessian J f_v s) s := by
  -- This is just the defining equation of `quadraticModel`.
  rfl

end Newton
