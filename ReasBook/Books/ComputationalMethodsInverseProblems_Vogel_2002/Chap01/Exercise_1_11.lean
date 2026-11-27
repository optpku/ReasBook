/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.Operator
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.Regularity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.SourceCondition

public section

/-
Exercise 1.11 (source-faithful form).

Vogel, *Computational Methods for Inverse Problems*: for the continuous Gaussian Fredholm
operator `(1.1)`, the source condition `f_true = K^* z` with `z ∈ L²(0, 1)` implies that
`f_true` is smooth.

The item is organized as follows.

* `Operator.lean` bundles `(1.1)` with the Gaussian kernel as the continuous linear operator
  `Fredholm1D.gaussianBlurL2` on `L²(0, 1)`, shows it realizes the pointwise source operator
  `(1.1)` (`gaussianBlurL2_realizesOperator`) and that it is self-adjoint
  (`gaussianBlurL2_adjoint_eq`).
* `Regularity.lean` shows that the blur is infinitely differentiable, i.e. that the values of
  `K` are smooth (`gaussianBlurL2_hasSmoothRepresentative`).
* `SourceCondition.lean` derives the exercise's conclusion: the source condition forces the
  true solution to be smooth (`sourceCondition_hasSmoothRepresentative`).
-/

#check Fredholm1D.gaussianBlurL2_realizesOperator
#check Fredholm1D.gaussianBlurL2_adjoint_eq
#check Fredholm1D.gaussianBlurL2_hasSmoothRepresentative
#check Fredholm1D.sourceCondition_hasSmoothRepresentative
