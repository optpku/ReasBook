/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_7.Factorization

public section

/- Exercise 4.7. Equation `(4.11)` is the pointwise factorization of the joint
probability mass function for independent, jointly distributed, discrete random
variables:
`joint (x, y) = fstMarginal joint x * sndMarginal joint y`.

In the current repo, that statement is formalized exactly by
`ProbabilityTheory.JointPmf.apply_eq_mul_marginals_of_indepFun`.
-/
#check ProbabilityTheory.JointPmf.apply_eq_mul_marginals_of_indepFun
