/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1.Fredholm

public section

/- Remark 1.1-extra-1 (1). Equation (1.1) is already the canonical pointwise formula
for `Fredholm1D.operator`. The source-side restrictions `0 < x < 1` are standing context
for the model, not inputs needed by the identity itself. -/
#check Fredholm1D.operator_apply

/- Remark 1.1-extra-1 (2). Equation (1.2) is already the defining formula for
`Fredholm1D.gaussianKernel`. The positivity assumptions on `C` and `γ` do not change the
formula, so the canonical formula theorem is checked directly. -/
#check Fredholm1D.gaussianKernel_apply

/- Remark 1.1-extra-1 (3). Equation (1.3) is already the entrywise formula for
`Fredholm1D.midpointMatrix`. -/
#check Fredholm1D.midpointMatrix_apply
