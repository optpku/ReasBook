/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40.Hessian

public section

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A `C²` functional with strongly positive Hessian at `f` has Hessian satisfying
Assumption A2 at `f`. This packages the self-adjointness furnished by
`hessian_isSelfAdjoint_of_contDiffAt` with the source lower-bound hypothesis
`(hessian J f).IsStronglyPositive`. -/
theorem hessian_selfAdjointStronglyPositive_of_contDiffAt
    (J : H → ℝ) (f : H) (hJ : ContDiffAt ℝ 2 J f)
    (hHess : (hessian J f).IsStronglyPositive) :
    ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J f) :=
  ContinuousLinearMap.SelfAdjointStronglyPositive.ofSelfAdjoint_isStronglyPositive
    (hessian_isSelfAdjoint_of_contDiffAt J f hJ) hHess
