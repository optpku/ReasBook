/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_12.Operator

public section

/- Exercise 1.3. The equality `(1.14)`-`(1.15)` obtained from the decomposition
`(1.6)`-`(1.8)` is formalized by the canonical Chapter 1 theorem
`Tikhonov.operator_apply_eq_svdFilter`. -/

#check Tikhonov.operator_apply_eq_svdFilter
