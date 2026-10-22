/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian

public section

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Definition 2.40. If `J` is Fréchet differentiable on a neighborhood of `f` with derivative
`fderiv ℝ J` and this derivative map has a Fréchet derivative at `f`, then the second Fréchet
derivative is represented by the bounded operator `hessian J f` through
`fderiv ℝ (fderiv ℝ J) f h k = inner ℝ (hessian J f h) k`. -/
theorem hessianRepresentation (J : H → ℝ) (f h k : H) :
    fderiv ℝ (fderiv ℝ J) f h k = inner ℝ (hessian J f h) k :=
  (hessian_inner J f h k).symm
